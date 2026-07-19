//! Boolean Constraint Propagation Engine

const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const List = std.ArrayList;
const Io = std.Io;

const Cnf = @import("Cnf.zig");

const Value = enum(u8) {
    /// variable is unassigned
    none,
    /// variable is FALSE
    neg,
    /// variable is TRUE
    pos,

    fn init(literal: u32) @This() {
        return switch (literal & 1) {
            0 => .pos,
            1 => .neg,
            else => unreachable,
        };
    }
};

const Reason = enum(u32) {
    /// literal assignment picked
    none = 0xFFFF_FFFF,
    /// assignment propagated
    _,

    fn init(clause: anytype) @This() {
        assert(clause != @intFromEnum(@This().none));
        return @enumFromInt(clause);
    }
};

/// The decision level, whether proven or propagated
const Level = enum(u32) {
    base = 0,
    _,

    fn init(level: u32) @This() {
        return @enumFromInt(level);
    }

    fn next(self: @This()) @This() {
        return .init(@intFromEnum(self) + 1);
    }
};

/// assigned values of each variable - indexed by variable
values: []Value,
/// reasons for literal assignment - indexed by variable
reasons: []Reason,
/// last explicitly assigned literal - indexed by variable
levels: []Level,
/// chronological history of literal assignments - stack
trail: List(u32),
/// conjunctive normal form clauses - owned by this CDCL
cnf: Cnf,

pub fn init(gpa: Allocator, reader: *Io.Reader) !@This() {
    var self: @This() = undefined;

    self.cnf = try .parse(gpa, reader);
    errdefer self.cnf.deinit(gpa);
    self.values = try gpa.alloc(Value, self.cnf.var_count);
    errdefer gpa.free(self.values);
    self.reasons = try gpa.alloc(Reason, self.cnf.var_count);
    errdefer gpa.free(self.reasons);
    self.levels = try gpa.alloc(Level, self.cnf.var_count);
    errdefer gpa.free(self.levels);
    self.trail = try .initCapacity(gpa, self.cnf.var_count);
    errdefer self.trail.deinit(gpa);

    @memset(self.values, .none);

    const clause_count = self.cnf.clauses.items.len;

    for (0..clause_count) |clause_index| {
        // incrementally add each clause into consideration
        self.cnf.clauses.items.len = clause_index + 1;
        // perform BCP and set up watch literals for clause
        const clause = self.cnf.clauses.items[clause_index];

        // TODO: collapse clauseUnsatisfied with unitClause
        if (clauseUnsatisfied(self.values, clause)) {
            return error.Unsatisfiable;
        } else if (unitClause(self.values, clause)) |literal| {
            if (try self.bcp(gpa, literal, .base)) |_| {
                return error.Unsatisfiable;
            }
        } else {
            // TODO: SET UP WATCHED LITERALS
        }
    }

    return self;
}

pub fn deinit(self: *@This(), gpa: Allocator) void {
    defer self.* = undefined;
    gpa.free(self.values);
    gpa.free(self.reasons);
    gpa.free(self.levels);
    self.trail.deinit(gpa);
    self.cnf.deinit(gpa);
}

/// check if a clause contains a variable - if so, return true
fn clauseContains(clause: []const u32, literal: u32) bool {
    for (clause) |check| {
        if (check / 2 == literal / 2) {
            return true;
        }
    }
    return false;
}

/// check if a clause is a unit clause - if so, return the literal
fn unitClause(values: []const Value, clause: []const u32) ?u32 {
    var unit: ?u32 = null;

    for (clause) |literal| {
        switch (values[literal / 2]) {
            .none => {
                // more than one unassigned variable
                if (unit != null) return null;
                // found one unassigned variable
                unit = literal;
            },
            // one literal has already been satisfied
            .neg => if (literal & 1 == 1) return null,
            // one literal has already been satisfied
            .pos => if (literal & 1 == 0) return null,
        }
    }

    return unit;
}

/// return true iff a clause is unsatisfied
fn clauseUnsatisfied(values: []const Value, clause: []const u32) bool {
    for (clause) |literal| {
        switch (values[literal / 2]) {
            // literal in clause is unassigned
            .none => return false,
            // literal in clause is already satisfied
            .neg => if (literal & 1 == 1) return false,
            // literal in clause is already satisfied
            .pos => if (literal & 1 == 0) return false,
        }
    }

    return true;
}

/// record a literal assignment with reason clause index and level
fn assign(self: *@This(), literal: u32, reason: Reason, level: Level) void {
    self.trail.appendAssumeCapacity(literal);
    self.values[literal / 2] = .init(literal);
    self.reasons[literal / 2] = reason;
    self.levels[literal / 2] = level;
}

/// Propagates changes for a literal - returns null if there
/// were no conflicts, else returns the conflict clause index.
fn bcp(self: *@This(), gpa: Allocator, literal: u32, level: Level) !?u32 {
    var literals: List(u32) = .empty;
    defer literals.deinit(gpa);

    self.assign(literal, .none, level);
    try literals.append(gpa, literal);

    std.debug.print("{s:-^40}\n", .{" STARTING BCP "});
    defer std.debug.print("{s:-^40}\n", .{" ENDING BCP "});

    std.debug.print("assigned literals: ", .{});
    for (self.values, 0..) |value, variable| {
        switch (value) {
            .neg => printLiteral(@intCast(variable * 2 + 1)),
            .pos => printLiteral(@intCast(variable * 2)),
            .none => continue,
        }

        if (variable + 1 < self.values.len) {
            std.debug.print(" ", .{});
        }
    }
    std.debug.print("\n", .{});

    while (literals.pop()) |check| {
        std.debug.print("Considering clauses containing literal ", .{});
        printLiteral(check);
        std.debug.print("\n", .{});

        for (0..self.cnf.clauses.items.len) |scan_index| {
            const scan_clause = self.cnf.clauses.items[scan_index];

            // clauses without the variable can be skipped
            if (!clauseContains(scan_clause, check)) continue;

            std.debug.print("considering clause:\n  ", .{});
            printClause(scan_clause);
            std.debug.print("\n", .{});

            // propagate a literal if it's clause is a unit
            if (unitClause(self.values, scan_clause)) |unit| {
                assert(self.values[unit / 2] == .none);

                std.debug.print("BCP - assigning literal: ", .{});
                printLiteral(unit);
                std.debug.print(" to level {}\n", .{level});

                self.assign(unit, .init(scan_index), level);
                try literals.append(gpa, unit);

                continue;
            } else {
                std.debug.print("clause not unit\n", .{});
            }

            if (clauseUnsatisfied(self.values, scan_clause)) {
                return @intCast(scan_index);
            }
        }
    }

    return null; // no conflict
}

/// pick a variable to branch on during CDCL
fn selectBranch(self: *const @This()) ?u32 {
    for (0..self.values.len) |root| {
        if (self.values[root] == .none) {
            return @intCast(root);
        }
    }

    return null;
}

/// combining two clauses together for deriving conflicting clauses
/// TODO make this so that one clause (a list) can absorb another (a slice)
fn combine(gpa: Allocator, a: []const u32, b: []const u32) ![]u32 {
    var result: List(u32) = try .initCapacity(gpa, a.len + b.len);
    defer result.deinit(gpa);

    if (std.debug.runtime_safety) {
        // assumption - neither a nor b contain duplicate variables
        for (a, 0..) |x, i| for (a[0..i]) |y| assert(x / 2 != y / 2);
        for (b, 0..) |x, i| for (b[0..i]) |y| assert(x / 2 != y / 2);
    }

    // When adding literals from clause a, check that the negative literal does
    // not exist within clause b. If the negative literal does exist in clause
    // b, then neither of the literals should be within the resulting clause.

    outer: for (a) |x| {
        for (b) |y| {
            if (x == y ^ 1) {
                continue :outer;
            }
        }
        result.appendAssumeCapacity(x);
    }

    // When adding literals from clause b, check that the same variable does
    // not exist within clause a. This is more strict than adding literals from
    // clause b to prevent duplicate literals being added to the result clause.

    outer: for (b) |x| {
        for (a) |y| {
            if (x / 2 == y / 2) {
                continue :outer;
            }
        }
        result.appendAssumeCapacity(x);
    }

    return try result.toOwnedSlice(gpa);
}

/// return true if there are at least two identical conflict levels
fn needResolve(self: *const @This(), conflict: []const u32, level: Level) bool {
    var found: bool = false;

    for (conflict) |literal| {
        if (self.levels[literal / 2] == level) {
            if (found) return true;
            found = true;
        }
    }

    return false;
}

/// return the most recent assigned literal from the list
fn mostRecent(self: *const @This(), literals: []const u32) ?u32 {
    for (0..self.trail.items.len) |index| {
        const reverse_index = self.trail.items.len - index - 1;
        const trail_literal = self.trail.items[reverse_index];
        for (literals) |check_literal| {
            if (trail_literal / 2 == check_literal / 2) {
                return trail_literal;
            }
        }
    }

    // no matching literals were found in the trail
    return null;
}

/// return the reason clause for a literal, or null if assigned
/// TODO: try simplifying so that I can remove the literal / 2 here
fn reasonClause(self: *const @This(), literal: u32) ?[]const u32 {
    const reason = self.reasons[literal / 2];
    if (reason == .none) return null;
    return self.cnf.clauses.items[@intFromEnum(reason)];
}

/// derive a conflicting clause from the last assignment
fn resolve(self: *const @This(), gpa: Allocator, clause: []const u32) ![]u32 {

    // 1. the last literal triggered the conflict because conflict_root was set
    const last_literal = self.trail.getLast() orelse unreachable;
    const conflict_level = self.levels[last_literal / 2];

    // 2. we are deriving another conflict clause, it is called "conflict"
    var conflict: List(u32) = .fromOwnedSlice(try gpa.dupe(u32, clause));
    defer conflict.deinit(gpa);

    var step: usize = 0;

    // 3. we continue factoring while more than one conflict root remains
    while (self.needResolve(conflict.items, conflict_level)) {
        step += 1;

        // a. select the most recently propagated literal
        const recent = self.mostRecent(conflict.items) orelse return &.{};

        // b. select the clause which forced that literal to be true
        const reason = self.reasonClause(recent) orelse unreachable;

        // c. merge the current conflict clause with the reason clause
        const merged = try combine(gpa, conflict.items, reason);

        // d. update the conflict clause to be the combined clauses
        conflict.clearAndFree(gpa);
        conflict = .fromOwnedSlice(merged);
    }

    return try conflict.toOwnedSlice(gpa);
}

// TODO: backtrack to the correct level or completely restart, because we are not
// currently backtracking far enough and it's screwing up the solver (infinite loops)

fn printLiteral(literal: u32) void {
    if (literal % 2 == 0) {
        std.debug.print("{}", .{(literal / 2) + 1});
    } else {
        std.debug.print("-{}", .{(literal / 2) + 1});
    }
}

fn printClause(clause: []const u32) void {
    for (clause) |literal| {
        printLiteral(literal);
        std.debug.print(" ", .{});
    }
    std.debug.print("0", .{});
}

/// return true iff satisfiable, return false iff unsatisfiable
pub fn cdcl(self: *@This(), gpa: Allocator) !bool {
    var conflict_count: u64 = 0;

    while (true) {
        std.debug.print("{s:-^80}\n", .{" CDCL INFORMATION "});

        std.debug.print("assigned literals: ", .{});
        for (self.values, 0..) |value, variable| {
            switch (value) {
                .neg => printLiteral(@intCast(variable * 2 + 1)),
                .pos => printLiteral(@intCast(variable * 2)),
                .none => continue,
            }

            if (variable + 1 < self.values.len) {
                std.debug.print(" ", .{});
            }
        }
        std.debug.print("\n", .{});

        std.debug.print("current clauses:\n", .{});
        for (self.cnf.clauses.items) |clause| {
            std.debug.print("  ", .{});
            printClause(clause);
            std.debug.print("\n", .{});
        }

        std.debug.print("{s:-^80}\n", .{" STARTING CDCL "});

        // pick the variable to branch on, otherwise satisfied
        const root = self.selectBranch() orelse return true;
        std.debug.print("variable to assign: {}\n", .{root + 1});

        const level: Level = blk: {
            if (self.trail.items.len == 0) break :blk .init(1);
            const literal = self.trail.getLast() orelse unreachable;
            break :blk self.levels[literal / 2].next();
        };

        std.debug.print("level of decision: {}\n", .{level});

        // attempt bcp with the negative literal
        if (try self.bcp(gpa, root * 2 + 1, level)) |conflict_index| {
            const conflict = self.cnf.clauses.items[conflict_index];
            std.debug.print("conflict found:\n  ", .{});
            printClause(conflict);
            std.debug.print("\n", .{});
            conflict_count += 1;

            // resolve the conflict clause and backtrack
            const resolved = try self.resolve(gpa, conflict);
            std.debug.print("resolved clause:\n  ", .{});
            printClause(resolved);
            std.debug.print("\n", .{});
            errdefer gpa.free(resolved);

            // add the derived clause to the CNF
            try self.cnf.clauses.append(gpa, resolved);

            // check if we have proven unsatisfiable
            if (resolved.len == 0) {
                std.debug.print("length = 0, so problem is UNSAT\n", .{});
                return false;
            }

            // ----------------------------------------------------------------
            // TODO: BACKTRACK TO WHERE THE DERIVED CLAUSE IS A UNIT. PROPAGATE
            // THAT UNIT CLAUSE VALUE. ALSO MAKE SURE TO PROPAGATE TO A BOUNDARY
            // OF WHERE WE HAVE JUST PROPAGATED A DECISION.

            while (clauseUnsatisfied(self.values, resolved)) {
                std.debug.print("resolved clause is still unsatisfied.\n", .{});
                if (self.trail.pop()) |literal| {
                    std.debug.print("unassigning literal ", .{});
                    printLiteral(literal);
                    std.debug.print("\n", .{});
                    self.values[literal / 2] = .none;
                } else return false;
            }

            // THIS CODE RESTARTS BECAUSE WE AREN'T BACKTRACKING CORRECTLY
            while (self.trail.getLast()) |literal| {
                if (self.levels[literal / 2] == .base) break;
                self.trail.items.len -= 1;
                std.debug.print("unassigning literal ", .{});
                printLiteral(literal);
                std.debug.print("\n", .{});
                self.values[literal / 2] = .none;
            }

            if (resolved.len == 1) {
                // go back to the base assignments
                while (self.trail.getLast()) |literal| {
                    if (self.levels[literal / 2] == .base) break;
                    self.values[literal / 2] = .none;
                    self.trail.items.len -= 1;
                }

                std.debug.print("resolved[0]: ", .{});
                printLiteral(resolved[0]);
                std.debug.print("\n", .{});

                if (try self.bcp(gpa, resolved[0], .base)) |_| {
                    return false; // unsatisfiable
                }
            }

            std.debug.print("number of clauses: {}\n", .{self.cnf.clauses.items.len});
        } else {
            std.debug.print("no conflict with decision.\n", .{});
        }

        std.debug.print("\n", .{});
    }
}

// ----------------------------------------------------------------------------

const expectEqualSlices = std.testing.expectEqualSlices;
const expectError = std.testing.expectError;
const expectEqual = std.testing.expectEqual;
const expect = std.testing.expect;

test "initialization works with empty CNF" {
    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed("p cnf 0 0");
    var self: @This() = try .init(gpa, &reader);
    defer self.deinit(gpa);

    try expectEqual(0, self.values.len);
    try expectEqual(0, self.reasons.len);
    try expectEqual(0, self.levels.len);
    try expectEqual(0, self.trail.items.len);
}

test "initialization returns error on empty clause" {
    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed("p cnf 0 1 0");
    const actual = @This().init(gpa, &reader);
    try expectError(error.Unsatisfiable, actual);
}

test "initialization returns error on propagated conflict" {
    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed(
        \\p cnf 1 2
        \\1 0
        \\-1 0
    );
    const actual = @This().init(gpa, &reader);
    try expectError(error.Unsatisfiable, actual);
}

test "initialization propagation works on complex CNF" {
    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed(
        \\p cnf 4 5
        \\1 0
        \\-1 2 0
        \\-1 -2 3 0
        \\-1 -2 -3 4 0
        \\-4 0
    );
    const actual = @This().init(gpa, &reader);
    try expectError(error.Unsatisfiable, actual);
}

test "initialization does not say UNSAT for trivial SAT" {
    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed("p cnf 1 1 1 0");
    var self: @This() = try .init(gpa, &reader);
    defer self.deinit(gpa);
}

test "clause is not a unit clause, no terms" {
    try expectEqual(null, unitClause(&.{}, &.{}));
}

test "clause is a unit clause, one term" {
    try expectEqual(0, unitClause(&.{.none}, &.{0}));
}

test "clause is a unit clause, two terms" {
    // lit 1 [negative var 0] is unsatisfied, lit 2 is unit
    try expectEqual(2, unitClause(&.{ .pos, .none }, &.{ 1, 2 }));
}

test "clause is not a unit clause, two terms" {
    // lit 0 [positive var 0] is already satisfied, lit 2 is unassigned
    try expectEqual(null, unitClause(&.{ .pos, .none }, &.{ 0, 2 }));
}

test "clause is not unit clause, unsatisfied two terms" {
    // both literals are unsatisfied, no unit possible
    try expectEqual(null, unitClause(&.{ .neg, .pos }, &.{ 1, 2 }));
}

test "clause is a unit clause, one literal forced" {
    try expectEqual(2, unitClause(&.{ .neg, .none }, &.{ 0, 2 }));
}

test "clause contains a variable - single term" {
    try expect(clauseContains(&.{0}, 0));
}

test "clause does not contain a variable - single term" {
    try expect(!clauseContains(&.{2}, 0));
}

test "clause contains variable at end of clause" {
    try expect(clauseContains(&.{ 0, 2, 4, 9 }, 9));
}

test "multi-literal clause does not contain variable" {
    try expect(!clauseContains(&.{ 0, 2, 4, 7 }, 8));
}

test "zero literal clause is unsatisfied" {
    try expect(clauseUnsatisfied(&.{}, &.{}));
}

test "one literal clause is not unsatisfied - unassigned" {
    try expect(!clauseUnsatisfied(&.{.none}, &.{0}));
}

test "one literal clause is not unsatisfied - satisfied" {
    try expect(!clauseUnsatisfied(&.{.neg}, &.{1}));
}

test "empty clauses combined result in empty result" {
    const gpa = std.testing.allocator;
    const actual = try combine(gpa, &.{}, &.{});
    defer gpa.free(actual);
    try expectEqualSlices(u32, &.{}, actual);
}

test "combined clause deduplicates literals" {
    const gpa = std.testing.allocator;
    const actual = try combine(gpa, &.{ 0, 2, 4 }, &.{ 0, 2, 4 });
    defer gpa.free(actual);
    try expectEqualSlices(u32, &.{ 0, 2, 4 }, actual);
}

test "combined clause eliminates negated literals" {
    const gpa = std.testing.allocator;
    const actual = try combine(gpa, &.{ 0, 2, 4 }, &.{ 1, 3, 5 });
    defer gpa.free(actual);
    try expectEqualSlices(u32, &.{}, actual);
}

test "clauses are combined correctly" {
    const gpa = std.testing.allocator;

    const a = &.{ 3, 10, 5, 13, 17, 1, 7 };
    const b = &.{ 13, 17, 9, 2, 11, 15 };
    const c = &.{ 5, 13, 17, 1, 7, 9, 15 };

    const actual = try combine(gpa, a, b);
    defer gpa.free(actual);
    try expectEqualSlices(u32, c, actual);
}

test "cdcl solves empty CNF" {
    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed("p cnf 0 0");
    var self: @This() = try .init(gpa, &reader);
    defer self.deinit(gpa);

    try expect(try self.cdcl(gpa));
}

test "cdcl solves one clause CNF" {
    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed("p cnf 1 1 1 0");
    var self: @This() = try .init(gpa, &reader);
    defer self.deinit(gpa);

    try expect(try self.cdcl(gpa));
}

test "cdcl solves two clause CNF" {
    const cnf_text =
        \\p cnf 2 2
        \\1 2 0
        \\-1 -2 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed(cnf_text);
    var self: @This() = try .init(gpa, &reader);
    defer self.deinit(gpa);

    try expect(try self.cdcl(gpa));
}

test "cdcl resolves correct clause" {
    const cnf_text =
        \\ p cnf 2 2
        \\ 1 2 0
        \\ 1 -2 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed(cnf_text);
    var self: @This() = try .init(gpa, &reader);
    defer self.deinit(gpa);

    if (try self.bcp(gpa, 1, .base)) |conflict| {
        try expectEqual(1, conflict);
    } else {
        return error.ExpectedConflictFromBcp;
    }
}

test "cdcl solves complex if-then-else" {
    const cnf_text =
        \\p cnf 4 6
        \\1 2 3 4 0
        \\-1 -2 -3 -4 0
        \\3 -1 2 0
        \\-3 -1 -2 0
        \\3 1 -4 0
        \\-3 1 4 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed(cnf_text);
    var self: @This() = try .init(gpa, &reader);
    defer self.deinit(gpa);

    try expect(try self.cdcl(gpa));
}

test "cdcl solves all disallowed combo of 3 variables" {
    const cnf_text =
        \\p cnf 3 8
        \\1 2 3 0
        \\1 2 -3 0
        \\1 -2 3 0
        \\1 -2 -3 0
        \\-1 2 3 0
        \\-1 2 -3 0
        \\-1 -2 3 0
        \\-1 -2 -3 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed(cnf_text);
    var self: @This() = try .init(gpa, &reader);
    defer self.deinit(gpa);

    try expect(try self.cdcl(gpa));
}
