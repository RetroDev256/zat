//! Boolean Constraint Propagation Engine

const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const List = std.ArrayList;

const Cnf = @import("Cnf.zig");

const Value = enum(u8) { none, neg, pos };

const Reason = enum(u32) {
    none = 0xFFFF_FFFF,
    _,

    fn init(clause: u32) @This() {
        assert(clause != 0xFFFF_FFFF);
        return @enumFromInt(clause);
    }
};

/// indexed by variable, assigned or propagated value
values: List(Value),
/// indexed by literal, two-watching clauses
watches: List(List(u32)),

/// ordered by assignment, literal value
t_literal: List(u32),
/// ordered by assignment, depth of decision
t_level: List(u32),
/// ordered by assignment, index of causal clause
t_reason: List(Reason),
/// the number of trail elements already propagated
propagated: u32,

pub fn init(gpa: Allocator, cnf: *Cnf) !@This() {
    var values: List(Value) = try .initCapacity(gpa, cnf.var_count);
    errdefer values.deinit(gpa);
    var watches: List(List(u32)) = try .initCapacity(gpa, cnf.var_count * 2);
    errdefer watches.deinit(gpa);
    var t_literal: List(u32) = try .initCapacity(gpa, cnf.var_count);
    errdefer t_literal.deinit(gpa);
    var t_level: List(u32) = try .initCapacity(gpa, cnf.var_count);
    errdefer t_level.deinit(gpa);
    var t_reason: List(Reason) = try .initCapacity(gpa, cnf.var_count);
    errdefer t_reason.deinit(gpa);

    values.expandToCapacity();
    @memset(values.items, .none);
    watches.expandToCapacity();
    @memset(watches.items, .empty);

    for (cnf.clauses.items, 0..) |clause, index| {
        switch (clause.len) {
            // a clause of length 0 is never satisfiable
            0 => return error.Unsatisfiable,
            1 => { // clauses of length 1 are unit by default
                try t_literal.append(gpa, clause[0]);
                try t_level.append(gpa, 0);
                try t_reason.append(gpa, .init(@intCast(index)));
            },
            else => { // other clauses have watches installed
                try watches.items[clause[0] ^ 1].append(gpa, @intCast(index));
                try watches.items[clause[1] ^ 1].append(gpa, @intCast(index));
            },
        }
    }

    var self: @This() = .{
        .values = values,
        .watches = watches,
        .t_literal = t_literal,
        .t_level = t_level,
        .t_reason = t_reason,
        .propagated = 0,
    };

    if (try self.propagate(gpa, cnf)) {
        return error.Unsatisfiable;
    } else {
        return self;
    }
}

pub fn deinit(self: *@This(), gpa: Allocator) void {
    defer self.* = undefined;

    for (self.watches.items) |*watch| {
        watch.deinit(gpa);
    }

    self.values.deinit(gpa);
    self.watches.deinit(gpa);
    self.t_literal.deinit(gpa);
    self.t_level.deinit(gpa);
    self.t_reason.deinit(gpa);
}

/// propagate unpropagated implications in the trail, return true on conflict
pub fn propagate(self: *@This(), gpa: Allocator, cnf: *Cnf) !bool {
    while (self.propagated < self.t_literal.items.len) {
        const literal = self.t_literal.items[self.propagated];
        const level = self.t_level.items[self.propagated];
        _ = self.t_reason.items[self.propagated];

        // the invalidated clauses are a subset of this list
        var clause_index: u32 = 0;
        const clauses = self.watches.items[literal].items;
        repair: while (clause_index < clauses.len) {
            const clause = clauses[clause_index];

            // try to find a replacement for the watched literal

            const literal_0 = cnf.clauses.items[clause][0];
            // the index of the current watch in the clause
            const a_index = @intFromBool(literal_0 ^ 1 != literal);
            // pointer to the old watched literal in the clause
            const watch_a = &cnf.clauses.items[clause][a_index];

            const clause_literals = cnf.clauses.items[clause];
            for (clause_literals[2..], 2..) |r_literal, r_index| {
                if (self.evalLiteral(r_literal) != false) {
                    // pointer to the replacement literal in the clause
                    const watch_r = &cnf.clauses.items[clause][r_index];
                    std.mem.swap(u32, watch_a, watch_r); // swap in new
                    _ = self.watches.items[literal].swapRemove(clause_index);
                    try self.watches.items[r_literal ^ 1].append(gpa, clause);
                    continue :repair; // do not increment, we removed with swap
                }
            }

            // detect that the clause is a unit clause and enqueue implication

            const b_index = 1 - a_index;
            const watch_b = cnf.clauses.items[clause][b_index];
            const literal_value = self.evalLiteral(watch_b);

            if (literal_value == null) { // unit clause
                try self.t_literal.append(gpa, watch_b);
                try self.t_level.append(gpa, level);
                try self.t_reason.append(gpa, .init(clause));
            } else if (literal_value == false) {
                return true; // conflict
            }

            clause_index += 1;
        }

        self.propagated += 1;
    }

    return false; // no conflict
}

/// check if a literal is currently unassigned or satisfied
fn evalLiteral(self: *const @This(), literal: u32) ?bool {
    switch (self.values.items[literal / 2]) {
        .neg => return literal & 1 == 1,
        .pos => return literal & 1 == 0,
        .none => return null,
    }
}
