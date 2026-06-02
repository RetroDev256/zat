const std = @import("std");
const Cnf = @import("Cnf.zig");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const List = std.ArrayList;

cnf: *Cnf,

pub fn init(cnf: *Cnf) @This() {
    return .{ .cnf = cnf };
}

/// remove clauses that are always true
fn pruneTautologies(gpa: Allocator, clauses: *List([]u32)) !void {
    var write_index: u32 = 0;
    outer: for (clauses.items) |clause| {
        for (clause, 0..) |a, idx_a| {
            for (clause[0..idx_a]) |b| {
                // Both X and NOT X are in the clause
                if (a == b ^ 1) {
                    gpa.free(clause);
                    continue :outer;
                }
            }
        }

        // write the clause into the next free spot
        clauses.items[write_index] = clause;
        write_index += 1;
    }

    // set the new number of clauses
    clauses.items.len = write_index;
}

/// remove duplicate literals from clauses
fn dedupeLiterals(gpa: Allocator, clauses: *const List([]u32)) !void {
    for (clauses.items, 0..) |*clause, clause_idx| {
        var write_index: u32 = 0;
        write: for (clause.*, 0..) |a, read_index| {
            for (clause.*[0..read_index]) |b| {
                if (a == b) continue :write;
            }

            clause.*[write_index] = a;
            write_index += 1;
        }

        var clause_list: List(u32) = .fromOwnedSlice(clause.*);
        clause_list.items.len = write_index;
        const owned = try clause_list.toOwnedSlice(gpa);
        clauses.items[clause_idx] = owned;
    }
}

// the reason this is so bad is because I'm not doing any
// unit propagation or pure literal elimination, I think

/// returns "true" on SAT, "false" on UNSAT
pub fn solve(self: *@This(), gpa: Allocator) !bool {

    // ------------------------------------------------------------------------
    // optimize and reduce spanning of tree

    // clauses with 0 terms are unsatisfiable
    for (self.cnf.clauses.items) |clause| {
        if (clause.len == 0) return false;
    }

    try pruneTautologies(gpa, &self.cnf.clauses);
    try dedupeLiterals(gpa, &self.cnf.clauses);

    // ------------------------------------------------------------------------
    // construct a mapping from literals back to clause

    var lit_map: List(List(u32)) = .empty;
    defer lit_map.deinit(gpa);

    try lit_map.appendNTimes(gpa, .empty, self.cnf.var_count * 2);
    defer for (lit_map.items) |*list| list.deinit(gpa);

    for (0..self.cnf.clauses.items.len) |clause_index| {
        for (self.cnf.clauses.items[clause_index]) |literal| {
            // clauses must not contain duplicated literals
            const index: u32 = @intCast(clause_index);
            try lit_map.items[literal].append(gpa, index);
        }
    }

    // ------------------------------------------------------------------------
    // davis-putnam algorithm

    for (0..self.cnf.var_count) |variable| {
        std.debug.print(
            "Eliminating {}/{}...\n",
            .{ variable, self.cnf.var_count },
        );

        // gather a list of true and false referenced clauses
        const lit_list_t = lit_map.items[variable * 2].items;
        defer lit_map.items[variable * 2].clearAndFree(gpa);
        const lit_list_f = lit_map.items[variable * 2 + 1].items;
        defer lit_map.items[variable * 2 + 1].clearAndFree(gpa);

        defer {
            // remove true clauses that have been consumed
            for (lit_list_t) |t_index| {
                gpa.free(self.cnf.clauses.items[t_index]);
                self.cnf.clauses.items[t_index] = &.{};
            }

            // remove false clauses that have been consumed
            for (lit_list_f) |f_index| {
                gpa.free(self.cnf.clauses.items[f_index]);
                self.cnf.clauses.items[f_index] = &.{};
            }
        }

        // compute pairwise combinations of true/false clauses

        var pairwise: List([]u32) = .empty;
        defer pairwise.deinit(gpa);
        defer for (pairwise.items) |c| gpa.free(c);

        for (lit_list_t) |t_index| {
            for (lit_list_f) |f_index| {
                const t_clause = self.cnf.clauses.items[t_index];
                const f_clause = self.cnf.clauses.items[f_index];
                if (t_clause.len == 0 or f_clause.len == 0)
                    continue; // clause no longer in formula

                const new_pair = try pairwise.addOne(gpa);
                errdefer pairwise.items.len -= 1;

                var clause: List(u32) = .empty;
                errdefer clause.deinit(gpa);

                for (t_clause) |literal|
                    if (literal / 2 != variable)
                        try clause.append(gpa, literal);

                for (f_clause) |literal|
                    if (literal / 2 != variable)
                        try clause.append(gpa, literal);

                try clause.shrinkToLen(gpa);
                new_pair.* = clause.toOwnedSliceAssert();
            }
        }

        try pruneTautologies(gpa, &pairwise);
        try dedupeLiterals(gpa, &pairwise);

        for (pairwise.items) |clause| {
            if (clause.len == 0) {
                return false;
            }
        }

        // add pairwise back into the main clause list

        const start_new = self.cnf.clauses.items.len;

        try pairwise.shrinkToLen(gpa);
        const clause_pairs = pairwise.toOwnedSliceAssert();
        defer gpa.free(clause_pairs);
        errdefer for (clause_pairs) |c| gpa.free(c);
        try self.cnf.clauses.appendSlice(gpa, clause_pairs);

        for (start_new..self.cnf.clauses.items.len) |clause_index| {
            for (self.cnf.clauses.items[clause_index]) |literal| {
                // clauses must not contain duplicated literals
                const index: u32 = @intCast(clause_index);
                try lit_map.items[literal].append(gpa, index);
            }
        }
    }

    return true;
}

fn testDp(cnf_text: []const u8, sat: bool) !void {
    const gpa = std.testing.allocator;
    var reader: std.Io.Reader = .fixed(cnf_text);
    var cnf = try Cnf.parse(gpa, &reader);
    defer cnf.deinit(gpa);

    var solver: @This() = .init(&cnf);
    const sat_actual = try solver.solve(gpa);
    try std.testing.expectEqual(sat, sat_actual);
}

test "single variable must be true" {
    try testDp(
        \\p cnf 1 1
        \\1 0
        \\
    , true);
}

test "empty clause is unsatisfiable" {
    try testDp(
        \\p cnf 0 1
        \\0
        \\
    , false);
}

test "unit propagation works, unsat" {
    try testDp(
        \\p cnf 2 3
        \\-1 2 0
        \\1 2 0
        \\-2 0
        \\
    , false);
}

test "single variable must be false" {
    try testDp(
        \\p cnf 1 1
        \\-1 0
        \\
    , true);
}

test "kinda complicated if-then-else sat" {
    try testDp(
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
    try testDp(
        \\p cnf 2 2
        \\-1 2 0
        \\1 -2 0
        \\
    , true);
}

test "variables must be not equal" {
    try testDp(
        \\p cnf 2 2
        \\-1 -2 0
        \\1 2 0
        \\
    , true);
}

test "unspecified first variable, unsatisfiable" {
    try testDp(
        \\p cnf 2 2
        \\2 0
        \\-2 0
        \\
    , false);
}

test "variable cannot be both equal and unequal" {
    try testDp(
        \\p cnf 1 2
        \\-1 0
        \\1 0
        \\
    , false);
}

test "some more complicated cnf works as expected" {
    try testDp(
        \\p cnf 5 3
        \\-2 5 -3 0
        \\1 4 0
        \\-4 1 2 5 0
        \\
    , true);
}
