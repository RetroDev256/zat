//! Boolean Constraint Propagation Engine

const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const List = std.ArrayList;
const Io = std.Io;

const Cnf = @import("Cnf.zig");

const Value = enum(u8) {
    none,
    neg,
    pos,

    fn fromLiteral(lit: u32) @This() {
        return switch (lit & 1) {
            0 => .pos,
            1 => .neg,
            else => unreachable,
        };
    }
};

/// assigned values of each variable - indexed by variable
values: []Value,
/// reasons for literal assignment - indexed by variable
reasons: []u32,
/// last explicitly assigned literal - indexed by variable
roots: []u32,
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
    self.reasons = try gpa.alloc(u32, self.cnf.var_count);
    errdefer gpa.free(self.reasons);
    self.roots = try gpa.alloc(u32, self.cnf.var_count);
    errdefer gpa.free(self.roots);
    self.trail = try .initCapacity(gpa, self.cnf.var_count);
    errdefer self.trail.deinit(gpa);

    @memset(self.values, .none);
    try self.initialBcp(gpa);

    return self;
}

pub fn deinit(self: *@This(), gpa: Allocator) void {
    defer self.* = undefined;
    gpa.free(self.values);
    gpa.free(self.reasons);
    gpa.free(self.roots);
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

/// Initial boolean propagation algorithm - simplified as we
/// do not need to trace changes or reasons for asssignments.
fn initialBcp(self: *@This(), gpa: Allocator) !void {
    var literals: List(u32) = .empty;
    defer literals.deinit(gpa);

    for (self.cnf.clauses.items) |clause| {
        // clauses with no literals are unsatisfiable
        if (clause.len == 0) return error.Unsatisfiable;

        // clauses are units if length 1 and variable unassigned
        if (clause.len != 1) continue; // not a unit clause
        self.values[clause[0] / 2] = .fromLiteral(clause[0]);
        try literals.append(gpa, clause[0]);

        while (literals.pop()) |check| {
            for (self.cnf.clauses.items) |scan_clause| {
                // clauses without the variable can be skipped
                if (!clauseContains(scan_clause, check)) continue;

                // propagate a literal if it's clause is a unit
                if (unitClause(self.values, scan_clause)) |unit| {
                    self.values[unit / 2] = .fromLiteral(unit);
                    try literals.append(gpa, unit);
                    continue;
                }

                // return an error if the clause is unsatisfied
                if (clauseUnsatisfied(self.values, scan_clause)) {
                    return error.Unsatisfiable;
                }
            }
        }
    }
}

/// Propagates changes for a literal - returns true if there is a conflict. If
/// there is a conflict, the last literal in trail is the conflicting literal.
fn bcp(self: *@This(), gpa: Allocator, assignment: u32) !bool {

    // assign the literal value, root, trail, and prepare for BCP
    self.values[assignment / 2] = .fromLiteral(assignment);
    self.reasons[assignment / 2] = undefined; // no reason for choice
    self.roots[assignment / 2] = assignment / 2; // explicitly assigned
    self.trail.appendAssumeCapacity(assignment);

    var literals: List(u32) = .empty;
    defer literals.deinit(gpa);
    try literals.append(gpa, assignment);

    while (literals.pop()) |check| {
        for (0..self.cnf.clauses.items.len) |scan_index| {
            const scan_clause = self.cnf.clauses.items[scan_index];

            // clauses without the literal can be skipped
            if (!clauseContains(scan_clause, check)) continue;

            // propagate a literal if it's clause is a unit
            if (unitClause(self.values, scan_clause)) |unit| {
                self.values[unit / 2] = .fromLiteral(unit);
                self.reasons[unit / 2] = @intCast(scan_index);
                self.roots[unit / 2] = assignment / 2;
                self.trail.appendAssumeCapacity(unit);
                try literals.append(gpa, unit);
                continue;
            }

            if (clauseUnsatisfied(self.values, scan_clause)) {
                return true; // clause was unsatisfied in BCP
            }
        }
    }

    return false; // no conflict
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

/// return true if there are at least two identical conflict roots
fn needResolve(self: *const @This(), conflict: []const u32, root: u32) bool {
    var found: bool = false;

    for (conflict) |literal| {
        if (self.roots[literal / 2] == root / 2) {
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
            if (trail_literal == check_literal) {
                return trail_literal;
            }
        }
    }

    // no matching literals were found in the trail
    return null;
}

/// return the reason clause for a literal, or null if assigned
fn reasonClause(self: *const @This(), literal: u32) ?[]const u32 {
    if (self.roots[literal / 2] == literal) return null;
    return self.cnf.clauses.items[self.reasons[literal / 2]];
}

/// derive a conflicting clause from the last assignment
fn resolve(self: *const @This(), gpa: Allocator) ![]u32 {
    // 1. the last literal triggered the conflict because conflict_root was set
    const last_literal = self.trail.getLast() orelse unreachable;
    const conflict_root = self.roots[last_literal / 2];

    // 2. we are deriving another conflict clause, it is called "conflict"
    const last_reason = self.cnf.clauses.items[self.reasons[last_literal / 2]];
    var conflict: List(u32) = .fromOwnedSlice(try gpa.dupe(u32, last_reason));
    defer conflict.deinit(gpa);

    // 3. we continue factoring while more than one conflict root remains
    while (self.needResolve(conflict.items, conflict_root)) {

        // a. select the most recently propagated literal
        const recent = self.mostRecent(conflict.items) orelse return &.{};

        // b. select the clause which forced that literal to be true
        const reason = self.reasonClause(recent) orelse &.{recent};

        // c. merge the current conflict clause with the reason clause
        const merged = try combine(gpa, conflict.items, reason);

        // d. update the conflict clause to be the combined clauses
        conflict.clearAndFree(gpa);
        conflict = .fromOwnedSlice(merged);
    }

    return try conflict.toOwnedSlice(gpa);
}

/// return true iff satisfiable, return false iff unsatisfiable
pub fn cdcl(self: *@This(), gpa: Allocator) !bool {
    while (true) {
        // pick the variable to branch on, otherwise satisfied
        const root = self.selectBranch() orelse return true;

        // attempt bcp with the negative literal
        if (!try self.bcp(gpa, root * 2)) continue;

        // resolve a conflict clause and backtrack
        const resolved = try self.resolve(gpa);
        errdefer gpa.free(resolved);

        // check if we have proven unsatisfiable
        if (resolved.len == 0) return false;

        // undo the changes made for this root
        while (self.trail.getLast()) |literal| {
            if (self.roots[literal / 2] == root) {
                self.values[literal / 2] = .none;
                self.trail.items.len -= 1;
            } else break;
        }

        // add the derived clause to the CNF
        try self.cnf.clauses.append(gpa, resolved);
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
    try expectEqual(0, self.roots.len);
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
