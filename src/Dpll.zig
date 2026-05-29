const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const Cnf = @import("Cnf.zig");

const Preprocess = @import("Preprocess.zig");
const VCMapping = Preprocess.VCMapping;
const Value = enum { positive, negative, unassigned };

/// original problem CNF
cnf: *const Cnf,
/// number of conflicts
conflicts: u64,

pub fn init(cnf: *const Cnf) @This() {
    return .{ .cnf = cnf, .conflicts = 0 };
}

// returns true if SATISFIABLE, false if UNSATISFIABLE
pub fn dpll(self: *@This(), gpa: Allocator) !bool {
    // ------------------------------------------------------------------------
    // zero clauses is trivially satisfiable, empty clauses are unsatisfiable

    if (self.cnf.clauses.items.len == 0) {
        return true; // no clauses, SAT
    }

    for (self.cnf.clauses.items) |clause| {
        if (clause.len == 0) return false; // empty clause, UNSAT
    }

    // ------------------------------------------------------------------------
    // create the data structures we will use during the actual dpll algorithm

    // a stack: the current variable we are modifying
    var current: std.ArrayList(u32) = .empty;
    defer current.deinit(gpa);

    // stack: the number of assigned variables per loop
    var reduce_counts: std.ArrayList(u32) = .empty;
    defer reduce_counts.deinit(gpa);

    // stack: every variable which was assigned
    var assignments: std.ArrayList(u32) = .empty;
    defer assignments.deinit(gpa);

    // values for each variable: 1 if true, -1 if false, 0 if unassigned
    const value_count: u32 = self.cnf.variable_count + 1;
    const value_map = try gpa.alloc(Value, value_count);
    defer gpa.free(value_map);
    @memset(value_map, .unassigned);

    // ------------------------------------------------------------------------
    // do pre-processing on the entire CNF input for speed and simplification

    // TODO: basic clause redundancy - set the clause to be in-conflict and
    // check if propagation causes conflict elsewhere. if it does, the clause
    // is trivially redundant and can be removed. this doesn't mean the clause
    // is only redundant if trying this results in a conflict though - it could
    // be that we only prove it's redundant after evaluating more deeply.

    // TODO: failed literal elimination (lookahead)
    // TODO: equivalent literal substitution
    // TODO: self-subsuming resolution
    // TODO: duplicate literal removal
    // TODO: apply ALL pure literals
    // TODO: resolution elimination
    // TODO: tautology elimination
    // TODO: propagate ALL units
    // TODO: vivification
    // TODO: subsumption

    const priority = try Preprocess.variablePriority(gpa, self.cnf);
    defer gpa.free(priority);

    var vc_map = try Preprocess.mapVariablesToClauses(gpa, self.cnf);
    defer vc_map.deinit(gpa);

    // ------------------------------------------------------------------------
    // dpll algorithm - the problem is satisfiable when assign_stack is full

    if (next(priority, value_map)) |next_variable| {
        try current.append(gpa, next_variable);
    } else return false; // SATISFIABLE

    loop: while (current.getLast()) |variable| {
        switch (value_map[variable]) {
            .unassigned => {
                // unassigned, so try negative
                value_map[variable] = .negative;
            },
            .negative => {
                // negative failed, revert and try positive
                undo(&reduce_counts, &assignments, value_map);
                value_map[variable] = .positive;
            },
            .positive => {
                // both failed, revert and pop and backtrack
                undo(&reduce_counts, &assignments, value_map);
                value_map[variable] = .unassigned;
                current.items.len -= 1;
                continue :loop;
            },
        }

        // prepare a restore point before we attempt simplification
        const reset: u32 = @intCast(assignments.items.len);
        try reduce_counts.append(gpa, reset);

        // unit propagation, pure literal elimination,
        const conflict = try self.simplify(
            gpa,
            &assignments,
            &vc_map,
            value_map,
            variable,
        );

        if (!conflict) { // if there is no conflict, continue
            if (next(priority, value_map)) |next_variable| {
                try current.append(gpa, next_variable);
            } else return true; // SATISFIABLE
            continue :loop;
        }

        self.conflicts += 1;
    }

    // no solution could be found
    return false; // UNSATISFIABLE
}

fn simplify(
    self: *@This(),
    gpa: Allocator,
    assignments: *std.ArrayList(u32),
    vc_map: *const VCMapping,
    value_map: []Value,
    first_variable: u32,
) !bool {
    // the variables we need to consider for propagation
    var process: std.ArrayList(u32) = .empty;
    try process.append(gpa, first_variable);
    defer process.deinit(gpa);

    while (process.pop()) |variable| {
        clauses: for (vc_map.variableClauses(variable)) |clause| {

            // literal for unit clause
            var target: ?i32 = null;
            var conflict: bool = true;

            for (self.cnf.clauses.items[clause]) |literal| {
                switch (value_map[@abs(literal)]) {
                    .unassigned => {
                        conflict = false; // unassigned literal
                        // at least two unassigned literals here
                        if (target != null) continue :clauses;
                        // track the single unassigned literal
                        target = literal;
                    },
                    // the clause has a satisfied literal
                    .negative => if (literal < 0) continue :clauses,
                    // the clause has a satisfied literal
                    .positive => if (literal > 0) continue :clauses,
                }
            }

            // not satisfied and no unassigned
            if (conflict) return true;

            if (target) |literal| {
                // assign the value to satisfy the clause;
                // consider the affected clauses for units

                if (literal < 0) {
                    // the literal must be negative to satisfy
                    value_map[@abs(literal)] = .negative;
                } else if (literal > 0) {
                    // the literal must be positive to satisfy
                    value_map[@abs(literal)] = .positive;
                } else unreachable; // literals must not be 0

                const new_variable = @abs(literal);
                try assignments.append(gpa, new_variable);
                try process.append(gpa, new_variable);
            }
        }
    }

    // no conflicts found
    return false;
}

fn next(
    priority: []const u32,
    value_map: []const Value,
) ?u32 {
    for (priority) |index|
        if (value_map[index] == .unassigned)
            return @intCast(index);

    // there are no unassigned variables
    return null; // SATISFIABLE
}

fn undo(
    reduce_counts: *std.ArrayList(u32),
    assignments: *std.ArrayList(u32),
    value_map: []Value,
) void {
    const reset = reduce_counts.pop() orelse unreachable;
    for (assignments.items[reset..]) |x| value_map[x] = .unassigned;
    assignments.items.len = reset;
}

// fn conflict(
//     self: *const @This(),
//     vc_map: *const VCMapping,
//     value_map: []const Value,
//     variable: u32,
// ) bool {
//     // variable 0 can be used as an edge case - and since it
//     // does not affect anything, we will never conflict.
//     if (variable == 0) return false;

//     outer: for (vc_map.variableClauses(variable)) |clause| {
//         for (self.cnf.clauseLiterals(clause)) |literal| {
//             const value = value_map[@abs(literal)];

//             if (value == .unassigned)
//                 continue :outer; // unassigned
//             if (literal < 0 and value == .negative)
//                 continue :outer; // satisfied
//             if (literal > 0 and value == .positive)
//                 continue :outer; // satisfied
//         }

//         // all of the variables within the clause were assigned - and
//         // none of the variables within the clause were satisfied -
//         // meaning that the clause was unsatisfied, and in conflict.
//         return true;
//     }

//     // none of the affected clauses were in conflict - because
//     // they had at least one clause satisfied or unassigned.
//     return false;
// }

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

test "empty clause is unsatisfiable" {
    try testDpll(
        \\p cnf 0 1
        \\0
        \\
    , false);
}

test "unit propagation works, unsat" {
    try testDpll(
        \\p cnf 2 3
        \\-1 2 0
        \\1 2 0
        \\-2 0
        \\
    , false);
}

test "single variable must be false" {
    try testDpll(
        \\p cnf 1 1
        \\-1 0
        \\
    , true);
}

test "kinda complicated if-then-else sat" {
    try testDpll(
        \\p cnf 4 6
        \\4 -2 0
        \\-4 2 0
        \\2 -3 -4 0
        \\2 3 4 0
        \\-2 -3 -1 0
        \\-2 3 1 0
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

test "unspecified first variable, unsatisfiable" {
    try testDpll(
        \\p cnf 2 2
        \\2 0
        \\-2 0
        \\
    , false);
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
