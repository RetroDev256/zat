const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const Cnf = @import("Cnf.zig");

/// Original CNF
cnf: *const Cnf,
/// Values: +1 / 0 / -1
values: []i8,
/// Boolean assignments history
undo_trail: std.ArrayList(u32),
/// Number of conflicts during solve
conflicts: u64,

pub fn init(gpa: Allocator, cnf: *const Cnf) !@This() {
    const values = try gpa.alloc(i8, cnf.variableCount() + 1);
    errdefer gpa.free(values);
    @memset(values, 0);

    return .{
        .cnf = cnf,
        .values = values,
        .undo_trail = .empty,
        .conflicts = 0,
    };
}

pub fn deinit(self: *@This(), gpa: Allocator) void {
    defer self.* = undefined;
    self.undo_trail.deinit(gpa);
    gpa.free(self.values);
}

// TODO: this might benefit from removing short-circuiting
// returns true IFF each clause is assigned and not satisfiable
fn clauseConflict(self: *const @This(), clause: u32) bool {
    for (self.cnf.clauseLiterals(clause)) |literal| {
        const value = self.values[@abs(literal)];
        if (value == 0) return false; // unassigned
        if (literal < 0 and value == -1) return false;
        if (literal > 0 and value == 1) return false;
    }

    return true;
}

// TODO: this might benefit from removing short-circuiting
// returns true IFF at least one clause is assigned and satisfiable
fn clauseSatisfied(self: *const @This(), clause: u32) bool {
    for (self.cnf.clauseLiterals(clause)) |literal| {
        const value = self.values[@abs(literal)];
        if (literal < 0 and value == -1) return true;
        if (literal > 0 and value == 1) return true;
    }

    return false;
}

/// Returns the variable index (and sign value) that would be REQUIRED to
/// validate the clause. If the clause is not a unit clause, 0 is returned.
fn findUnit(self: *const @This(), clause: u32) i32 {
    var term: i32 = 0;

    for (self.cnf.clauseLiterals(clause)) |literal| {
        const value = self.values[@abs(literal)];

        if (value == 0) {
            // more than one term is unspecified
            if (term != 0) return 0;
            term = literal; // term equals literal
        } else if (value == -1) {
            // one term is already satisfied
            if (literal < 0) return 0;
        } else { // value == 1
            // one term is already satisfied
            if (literal > 0) return 0;
        }
    }

    return term;
}

// Assign a value to a variable - asserts that the variable is not yet
// assigned, asserts that the value is either false (-1) or true (1).
fn assignVariable(
    self: *@This(),
    gpa: Allocator,
    variable: usize,
    value: i8,
) !void {
    assert(self.values[variable] == 0);
    assert(value == -1 or value == 1);
    try self.undo_trail.append(gpa, @intCast(variable));
    self.values[variable] = value;
}

// Finds unit clauses and propagates their values across clauses.
// Returns false if there is a conflict, true if there is not.
fn propagateUnits(self: *@This(), gpa: Allocator) !bool {
    while (true) {
        var changed: bool = false;
        for (0..self.cnf.clauseCount()) |clause| {
            if (self.clauseConflict(@intCast(clause))) return false;
            if (!self.clauseSatisfied(@intCast(clause))) {
                const unit = self.findUnit(@intCast(clause));
                if (unit != 0) {
                    const sign: i8 = if (unit > 0) 1 else -1;
                    try self.assignVariable(gpa, @abs(unit), sign);
                    changed = true;
                }
            }
        }
        if (!changed) return true;
    }
}

// Finds literals in unsatisfied clauses. If the literals only appear as
// true or false, they are assigned respectively. A sound reduction.
fn applyPureLiterals(self: *@This(), gpa: Allocator) !void {
    // for each unsatisfied clause where the variable appears: false?
    const appears_false = try gpa.alloc(bool, self.cnf.variableCount() + 1);
    defer gpa.free(appears_false);
    @memset(appears_false, false);

    // for each unsatisfied clause where the variable appears: true?
    const appears_true = try gpa.alloc(bool, self.cnf.variableCount() + 1);
    defer gpa.free(appears_true);
    @memset(appears_true, false);

    // determine the appearances of each variable
    for (0..self.cnf.clauseCount()) |clause| {
        if (self.clauseSatisfied(@intCast(clause))) continue;
        for (self.cnf.clauseLiterals(@intCast(clause))) |literal| {
            const variable: u32 = @abs(literal);
            if (literal > 0) appears_true[variable] = true;
            if (literal < 0) appears_false[variable] = true;
        }
    }

    // assign the values respective of appearances
    for (1..self.cnf.variableCount() + 1) |variable| {
        // we can only consider unassigned variables
        if (self.values[variable] != 0) continue;

        if (appears_false[variable]) {
            if (appears_true[variable]) {
                // appears in unsatisfied clauses as "false" AND "true"
                // there is nothing that we can do here
            } else {
                // appears in unsatisfied clauses as "false" BUT NOT "true"
                try self.assignVariable(gpa, variable, -1);
            }
        } else {
            if (appears_true[variable]) {
                // appears in unsatisfied clauses as "true" BUT NOT "false"
                try self.assignVariable(gpa, variable, 1);
            } else {
                // does not appear in unsatisfied clauses - default "false"
                try self.assignVariable(gpa, variable, -1);
            }
        }
    }
}

// returns true if SATISFIABLE, false if UNSATISFIABLE
pub fn dpll(self: *@This(), gpa: Allocator) !bool {
    // restore point at the beginning of the function
    const trail_a = self.undo_trail.items.len;

    // attempt some basic simplification
    try self.applyPureLiterals(gpa);
    if (!try self.propagateUnits(gpa)) {
        // there is a conflict with applied literals and propagated units
        // undo changes and return false to signify a conflict occurred
        for (self.undo_trail.items[trail_a..]) |val| self.values[val] = 0;
        self.undo_trail.items.len = trail_a;
        self.conflicts += 1;
        return false;
    }

    // check if all the clauses have been satisfied
    var satisfied: bool = true;
    for (0..self.cnf.clauseCount()) |clause| {
        if (!self.clauseSatisfied(@intCast(clause))) {
            satisfied = false;
            break;
        }
    }

    // the problem is SATISFIABLE
    if (satisfied) return true;

    // find a variable we can attempt to assign
    var unassigned_idx: usize = 0;
    for (1..self.cnf.variableCount()) |var_idx| {
        if (self.values[var_idx] == 0) {
            unassigned_idx = var_idx;
            break;
        }
    }

    if (unassigned_idx == 0) {
        // there are no more unassigned variables, and some unsatisfied clauses
        // undo changes and return false to signify that we ran into a conflict
        for (self.undo_trail.items[trail_a..]) |val| self.values[val] = 0;
        self.undo_trail.items.len = trail_a;
        self.conflicts += 1;
        return false;
    }

    // restore point at time of decision
    const trail_b = self.undo_trail.items.len;

    // try to assign this variable to true - recurse
    try self.assignVariable(gpa, unassigned_idx, 1);
    if (try self.dpll(gpa)) return true; // SATISFIABLE

    // that change is not satisfiable - backtrack to point of assignment
    for (self.undo_trail.items[trail_b..]) |val| self.values[val] = 0;
    self.undo_trail.items.len = trail_b;

    // try to assign this variable to false - recurse
    try self.assignVariable(gpa, unassigned_idx, -1);
    if (try self.dpll(gpa)) return true; // SATISFIABLE

    // that change is not satisfiable - backtrack all changes, conflict
    for (self.undo_trail.items[trail_a..]) |val| self.values[val] = 0;
    self.undo_trail.items.len = trail_a;
    self.conflicts += 1;
    return false;
}

fn testDpll(cnf_text: []const u8, sat: bool) !void {
    const gpa = std.testing.allocator;
    var reader: std.Io.Reader = .fixed(cnf_text);
    var cnf = try Cnf.parse(gpa, &reader);
    defer cnf.deinit(gpa);

    var solver: @This() = try .init(gpa, &cnf);
    defer solver.deinit(gpa);

    const sat_actual = try solver.dpll(gpa);
    try std.testing.expectEqual(sat, sat_actual);
}

test "single variable must be true" {
    try testDpll(
        \\p cnf 1 1
        \\1 0
        \\
    , true);
}

test "single variable must be false" {
    try testDpll(
        \\p cnf 1 1
        \\-1 0
        \\
    , true);
}

test "variables must be equal" {
    try testDpll(
        \\p cnf 2 2
        \\-1 2 0
        \\1 -2 0
        \\
    , true);
}

test "variables must be not equal" {
    try testDpll(
        \\p cnf 2 2
        \\-1 -2 0
        \\1 2 0
        \\
    , true);
}

test "variable cannot be both equal and unequal" {
    try testDpll(
        \\p cnf 1 2
        \\-1 0
        \\1 0
        \\
    , false);
}

test "some more complicated cnf works as expected" {
    try testDpll(
        \\p cnf 5 3
        \\-2 5 -3 0
        \\1 4 0
        \\-4 1 2 5 0
        \\
    , true);
}
