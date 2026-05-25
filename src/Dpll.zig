const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const Cnf = @import("Cnf.zig");

/// original problem CNF
cnf: *const Cnf,
/// number of conflicts
conflicts: u64,

pub fn init(cnf: *const Cnf) @This() {
    return .{ .cnf = cnf, .conflicts = 0 };
}

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
    const appears_false = try gpa.alloc(bool, self.cnf.variable_count + 1);
    defer gpa.free(appears_false);
    @memset(appears_false, false);

    // for each unsatisfied clause where the variable appears: true?
    const appears_true = try gpa.alloc(bool, self.cnf.variable_count + 1);
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
    for (1..self.cnf.variable_count + 1) |variable| {
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
    // ------------------------------------------------------------------------
    // create the data structures we will use during the actual dpll algorithm

    // a stack: stores the *number* of assignments made during undo points
    var undo_stack: std.ArrayList(u32) = .empty;
    defer undo_stack.deinit(gpa);

    // a stack: stores the last assignments made during the dpll algorithm
    var assign_stack: std.ArrayList(u32) = .empty;
    const variable_count: u32 = self.cnf.variable_count;
    try assign_stack.ensureTotalCapacityPrecise(gpa, variable_count);
    defer assign_stack.deinit(gpa);

    // assignments for each variable: 1 if true, -1 if false, 0 if unassigned
    const assignments = try gpa.alloc(i8, variable_count + 1);
    defer gpa.free(assignments);
    @memset(assignments, 0);

    // ------------------------------------------------------------------------
    // do pre-processing on the entire CNF input for speed and simplification

    // TODO: apply ALL pure literals
    // TODO: propagate ALL units

    // ------------------------------------------------------------------------
    // dpll algorithm - the problem is satisfiable when assign_stack is full

    outer: while (assign_stack.items.len != variable_count) {

        // push a restore point onto the undo stack
        try undo_stack.append(gpa, @intCast(assign_stack.items.len));

        // find a variable to assign
        var set_variable: u32 = 1;
        while (assignments[set_variable] != 0) {
            set_variable += 1;
        }

        inline for (&.{ -1, 1 }) |value| {
            // assign `value` to `set_variable`
            assignments[set_variable] = value;
            assign_stack.appendAssumeCapacity(set_variable);

            // TODO: I might not need to check for conflicts if I do these
            // *** apply pure literals
            // *** propagate units

            const conflict: bool = blk: {
                next_clause: for (0..self.cnf.clauseCount()) |clause| {
                    for (self.cnf.clauseLiterals(@intCast(clause))) |literal| {
                        const variable = @abs(literal);

                        if (assignments[variable] == 0) // unassigned
                            continue :next_clause;
                        if (literal > 0 and assignments[variable] == 1)
                            continue :next_clause;
                        if (literal < 0 and assignments[variable] == -1)
                            continue :next_clause;
                    }

                    break :blk true;
                }

                break :blk false;
            };

            if (conflict) {
                // undo the current assignments
                const last_undo = undo_stack.items.len - 1;
                const start = undo_stack.items[last_undo];
                const end = assign_stack.items.len;
                for (assign_stack.items[start..end]) |undo| {
                    assignments[undo] = 0;
                }

                // rewind the assignment stack
                assign_stack.items.len = start;
            } else {
                continue :outer;
            }
        }

        // encountered a conflict
        undo_stack.items.len -= 1;

        // we cannot backtrack further - UNSATISFIABLE
        if (assign_stack.items.len == 0) return false;
    }

    // If we have reached this point, it means that all of the variables have
    // been assigned and there are no conflicts - in other words, satisfiable.
    return true;
}

fn testDpll(cnf_text: []const u8, sat: bool) !void {
    const gpa = std.testing.allocator;
    var reader: std.Io.Reader = .fixed(cnf_text);
    var cnf = try Cnf.parse(gpa, &reader);
    defer cnf.deinit(gpa);

    var solver: @This() = .init(&cnf);
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
