//! Boolean Constraint Propagation - initialized with CNF. Clause count may
//! change, but this structure has no facility to change the variable count.
//! This structure manages variable values (unassigned, positive, negative).

const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;

const Cnf = @import("Cnf.zig");

const Val = enum {
    /// the variable is not assigned
    none,
    /// the variable is assigned as "true"
    pos,
    /// the variable is assigned as "false"
    neg,
};

// /// TODO: multiArrayList this?
// const Assignment = struct {
//     /// index of the variable
//     variable: u32,
//     /// level of the assignment
//     level: u32,
//     /// index of unit clause
//     reason: ?u32,
// };

cnf: *const Cnf,
/// assigned/propagated values of variables
values: std.ArrayList(Val),
/// two-watched clause literals - first two
watches: std.ArrayList(std.ArrayList(u32)),
// /// trail of variables, levels, and reasons
// trail: std.ArrayList(Assignment),

/// Create a structure for BCP - inc. variable watches
pub fn init(gpa: Allocator, cnf: *const Cnf) !@This() {
    var self: @This() = .{
        .cnf = cnf,
        .values = .empty,
        .watches = .empty,
        // .trail = .empty,
    };

    errdefer self.deinit(gpa);

    // create a value mapping for each variable
    try self.values.appendNTimes(gpa, .none, self.cnf.variable_count + 1);
    // create a watched clause list for each variable
    try self.watches.appendNTimes(gpa, .empty, self.cnf.variable_count + 1);
    // add all clauses into consideration for literal watching
    for (0..self.cnf.clauses.items.len) |index| try self.addClause(gpa, index);

    return self;
}

pub fn deinit(self: *@This(), gpa: Allocator) void {
    defer self.* = undefined;
    for (self.watches.items) |watch| watch.deinit(gpa);
    self.watches.deinit(gpa);
}

/// Associate a new clause into the watch literals
pub fn addClause(self: *@This(), gpa: Allocator, index: u32) !void {
    const clause = self.cnf.clauses.items[index];

    switch (clause.len) {
        // 0 values is impossible to satisfy
        0 => return error.Conflict,
        // 1 value means the variable is set
        1 => try self.propagate(clause[0], gpa, 0),
        // 2 or more values involve watches
        else => inline for (0..2) |offset| {
            if (self.findOpen(clause[offset + 1 ..])) |open| {
                const dest = &clause[offset + 1 + open];
                std.mem.swap(i32, &clause[offset], dest);
            } else {
                try self.propagate(clause[offset], gpa, 0);
            }

            const variable = @abs(clause[offset]);
            assert(variable < self.cnf.variable_count + 1);
            const watch = &self.watches.items[variable];

            // clauses should not have duplicates
            if (std.debug.runtime_safety)
                for (watch.items) |watch_clause|
                    assert(watch_clause != index);

            try watch.append(gpa, index);
        },
    }
}

fn findOpen(self: *@This(), clause: []i32) ?usize {
    for (clause, 0..) |literal, index| {
        switch (self.values.items[@abs(literal)]) {
            .none => return index, // unassigned
            .neg => if (literal < 0) return index,
            .pos => if (literal > 0) return index,
        }
    }

    return null;
}

/// just assign, don't check or propagate
fn assign(
    self: *@This(),
    gpa: Allocator,
    literal: i32,
    level: u32,
) !void {
    if (literal < 0) {
        self.values.items[@abs(literal)] = .neg;
    } else if (literal > 0) {
        self.values.items[@abs(literal)] = .pos;
    } else unreachable;

    _ = gpa;
    _ = level;
}

/// do assignments and recursive propagation
fn propagate(
    self: *@This(),
    gpa: Allocator,
    start_literal: i32,
    level: u32,
) !void {
    var lit_list: std.ArrayList(i32) = .empty;
    defer lit_list.deinit(gpa);
    try lit_list.append(gpa, start_literal);

    while (lit_list.pop()) |literal| {
        for (self.watches.items[@abs(literal)]) |clause| {
            inline for (0..2) |offset| {
                if (self.findOpen(clause[offset + 1 ..])) |open| {
                    const dest = &clause[offset + 1 + open];
                    std.mem.swap(i32, &clause[offset], dest);
                } else {
                    try self.assign(gpa, clause[offset], level);
                    lit_list.append(gpa, clause[offset]);
                }
            }
        }
    }
}

/// Remove all references to a clause, by index
pub fn delClause(self: *@This(), index: u32) void {
    const clause = self.cnf.clauses.items[index];
    outer: for (clause[0..@max(2, clause.len)]) |literal| {
        assert(@abs(literal) < self.cnf.variable_count + 1);
        const watch = &self.watches.items[@abs(literal)];

        // remove clause references from associated watch lists
        for (watch.items, 0..) |watch_clause, watch_index| {
            if (watch_clause != index) continue;
            watch.swapRemove(watch_index);
            continue :outer;
        }

        unreachable; // the clause must be watched
    }
}
