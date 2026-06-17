//! Boolean Constraint Propagation Engine

const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const List = std.ArrayList;

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

// TODO: this cdcl function requires that unit propagation takes place before
// the algorithm - it must operate on clauses which none are units, all have
// at least two elements at all times (except for intermediate propagation,
// but that is assumed).

pub fn cdcl(gpa: Allocator, cnf: *Cnf) !bool {
    // ------------------------------------------------------------------------
    // initialize variables that will be used to store information for CDCL

    // the assigned value of each variable
    const values = try gpa.alloc(Value, cnf.var_count);
    defer gpa.free(values);

    // reasons for assignment per variable - this is the index of clause in CNF
    // which caused the literal to be assigned - the index at reasons[literal]
    // is undefined if the literal was explicitly assigned
    const reasons = try gpa.alloc(u32, cnf.var_count);
    defer gpa.free(reasons);

    // last explicitly assigned (via selection instead of BCP) literal -
    // indexed by variable
    const roots = try gpa.alloc(u32, cnf.var_count);
    defer gpa.free(roots);

    // chronological history of literal assignments
    var trail: List(u32) = try .initCapacity(gpa, cnf.var_count);
    defer trail.deinit(gpa);

    cdcl: while (true) {
        // --------------------------------------------------------------------
        // pick a variable to branch on

        var root = 0;
        while (values[root] != .none) {
            if (root >= cnf.var_count)
                return true; // SAT
            root += 1;
        }

        // --------------------------------------------------------------------
        // assign the false literal

        values[root] = .neg;
        reasons[root] = undefined;
        roots[root] = root;
        trail.appendAssumeCapacity(root);

        // --------------------------------------------------------------------
        // boolean constraint propagation

        var bcp_stack: List(u32) = .empty;
        defer bcp_stack.deinit(gpa);
        try bcp_stack.append(root);

        var bcp_conflict: bool = false;

        bcp: while (bcp_stack.pop()) |check| {

            // get the list of affected clauses
            var affected: List(u32) = .empty;
            defer affected.deinit(gpa);
            for (cnf.clauses, 0..) |literal, clause| {
                if (literal == check) {
                    try affected.append(gpa, clause);
                }
            }

            // check if any of them are conflicted
            for (affected.items) |clause_idx| {
                var conflict: bool = true;
                search: for (cnf.clauses[clause_idx]) |lit| {
                    if (values[lit / 2] != .neg) {
                        conflict = false;
                        break :search;
                    }
                }

                if (conflict) {
                    bcp_conflict = true;
                    break :bcp;
                }
            }

            // check if any of them can propagate
            for (affected.items) |clause_idx| {
                var unit_lit: ?u32 = null;
                search: for (cnf.clauses[clause_idx]) |lit| {
                    if (values[lit / 2] == .none) {
                        if (unit_lit != null) {
                            unit_lit = null;
                            break :search;
                        }
                        unit_lit = lit;
                    }
                }

                if (unit_lit) |lit| {
                    try bcp_stack.append(gpa, lit);
                    const variable = lit / 2;
                    values[variable] = .fromLiteral(lit);
                    reasons[variable] = clause_idx;
                    roots[variable] = root;
                    trail.appendAssumeCapacity(lit);
                }
            }
        }

        // --------------------------------------------------------------------
        // clause resolution

        if (!bcp_conflict) continue :cdcl;

        // TODO: single BCP before cdcl so this works 100%

        const reason_index = (trail.getLast() orelse unreachable).reason;
        const conflicting_clause = cnf.clauses.items[reason_index];
        const owned_conflicting = try gpa.dupe(gpa, conflicting_clause);
        var conflicting: List(u32) = .fromOwnedSlice(owned_conflicting);
        defer conflicting.deinit(gpa);

        resolve: while (true) {
            // resolution exits when at most one literal from the conflicting
            // clause has been propagated from the current root.

            var root_count: u32 = 0;
            for (conflicting.items) |lit| {
                if (roots[lit / 2] == root) {
                    root_count += 1;
                }
            }

            // if this does happen, it means that the conflicting clause had no
            // terms to begin with - which should be impossible as the literal
            // that triggered conflict analysis should have been part of this
            // clause, or it could be the case that all of the literals which
            // were propagated from the root decision have been replaced - ...
            // actually, that might be possible... so yeah if this gets hit,
            // just change the second condition to <= 1 instead of == 1 and
            // remove the first condition
            if (root_count == 0) unreachable;
            if (root_count == 1) break :resolve;

            // select the most recently assigned literal to resolve
            const elim_literal: u32 = blk: {
                const len = trail.items.len;
                for (0..len) |rev_index| {
                    const index = len - 1 - rev_index;
                    const item = trail.items[index];
                    for (conflicting.items) |lit| {
                        if (lit == item) {
                            break :blk lit;
                        }
                    }
                }

                // surely it is the case that we 1) have items within the list
                // for conflict literals, and that they exist within the trail
                unreachable;
            };

            // remove the eliminated variable from the conflicting clause
            var write_idx: usize = 0;
            for (0..conflicting.items) |lit| {
                // skip literals that should be eliminated
                if (lit / 2 != elim_literal / 2) {
                    conflicting.items[write_idx] = lit;
                    write_idx += 1;
                }
            }
            conflicting.items.len = write_idx;

            // fetch the elimination literal clause and add to conflict clause
            const reason = reasons[elim_literal]; // ASSUMPTION NOT UNDEFINED
            for (cnf.clauses.items[reason]) |lit| {
                // skip literals that should be eliminated
                if (lit / 2 != elim_literal / 2) {
                    try conflicting.append(gpa, lit);
                }
            }
        }

        // simplify the conflicting clause - handle the case where it has 0 and 1 elements
        // for 0 elements, return false as the entire thing is proven unsat
        // for 1 elements, immediately propagate and resume cdcl
        // for more elements, add to list of clauses and stuff
    }
}

// const Reason = enum(u32) {
//     none = 0xFFFF_FFFF,
//     _,

//     fn init(clause: u32) @This() {
//         assert(clause != 0xFFFF_FFFF);
//         return @enumFromInt(clause);
//     }
// };

// /// indexed by variable, assigned or propagated value
// values: List(Value),
// /// indexed by literal, two-watching clauses
// watches: List(List(u32)),

// /// ordered by assignment, literal value
// t_literal: List(u32),
// /// ordered by assignment, depth of decision
// t_level: List(u32),
// /// ordered by assignment, index of causal clause
// t_reason: List(Reason),

// pub fn init(gpa: Allocator, cnf: *Cnf) !@This() {
//     var values: List(Value) = try .initCapacity(gpa, cnf.var_count);
//     errdefer values.deinit(gpa);
//     var watches: List(List(u32)) = try .initCapacity(gpa, cnf.var_count * 2);
//     errdefer watches.deinit(gpa);
//     var t_literal: List(u32) = try .initCapacity(gpa, cnf.var_count);
//     errdefer t_literal.deinit(gpa);
//     var t_level: List(u32) = try .initCapacity(gpa, cnf.var_count);
//     errdefer t_level.deinit(gpa);
//     var t_reason: List(Reason) = try .initCapacity(gpa, cnf.var_count);
//     errdefer t_reason.deinit(gpa);

//     values.expandToCapacity();
//     @memset(values.items, .none);
//     watches.expandToCapacity();
//     @memset(watches.items, .empty);

//     for (cnf.clauses.items, 0..) |clause, index| {
//         switch (clause.len) {
//             // a clause of length 0 is never satisfiable
//             0 => return error.Unsatisfiable,
//             1 => { // clauses of length 1 are unit by default
//                 try t_literal.append(gpa, clause[0]);
//                 try t_level.append(gpa, 0);
//                 try t_reason.append(gpa, .init(@intCast(index)));
//             },
//             else => { // other clauses have watches installed
//                 try watches.items[clause[0] ^ 1].append(gpa, @intCast(index));
//                 try watches.items[clause[1] ^ 1].append(gpa, @intCast(index));
//             },
//         }
//     }

//     var self: @This() = .{
//         .values = values,
//         .watches = watches,
//         .t_literal = t_literal,
//         .t_level = t_level,
//         .t_reason = t_reason,
//         .propagated = 0,
//     };

//     if (try self.propagate(gpa, cnf)) {
//         return error.Unsatisfiable;
//     } else {
//         return self;
//     }
// }

// pub fn deinit(self: *@This(), gpa: Allocator) void {
//     defer self.* = undefined;

//     for (self.watches.items) |*watch| {
//         watch.deinit(gpa);
//     }

//     self.values.deinit(gpa);
//     self.watches.deinit(gpa);
//     self.t_literal.deinit(gpa);
//     self.t_level.deinit(gpa);
//     self.t_reason.deinit(gpa);
// }

// /// propagate unpropagated implications in the trail, return true on conflict
// pub fn propagate(self: *@This(), gpa: Allocator, cnf: *Cnf) !bool {
//     while (self.propagated < self.t_literal.items.len) {
//         const literal = self.t_literal.items[self.propagated];
//         const level = self.t_level.items[self.propagated];
//         _ = self.t_reason.items[self.propagated];

//         // the invalidated clauses are a subset of this list
//         var clause_index: u32 = 0;
//         const clauses = self.watches.items[literal].items;
//         repair: while (clause_index < clauses.len) {
//             const clause = clauses[clause_index];

//             // try to find a replacement for the watched literal

//             const literal_0 = cnf.clauses.items[clause][0];
//             // the index of the current watch in the clause
//             const a_index = @intFromBool(literal_0 ^ 1 != literal);
//             // pointer to the old watched literal in the clause
//             const watch_a = &cnf.clauses.items[clause][a_index];

//             const clause_literals = cnf.clauses.items[clause];
//             for (clause_literals[2..], 2..) |r_literal, r_index| {
//                 if (self.evalLiteral(r_literal) != false) {
//                     // pointer to the replacement literal in the clause
//                     const watch_r = &cnf.clauses.items[clause][r_index];
//                     std.mem.swap(u32, watch_a, watch_r); // swap in new
//                     _ = self.watches.items[literal].swapRemove(clause_index);
//                     try self.watches.items[r_literal ^ 1].append(gpa, clause);
//                     continue :repair; // do not increment, we removed with swap
//                 }
//             }

//             // detect that the clause is a unit clause and enqueue implication

//             const b_index = 1 - a_index;
//             const watch_b = cnf.clauses.items[clause][b_index];
//             const literal_value = self.evalLiteral(watch_b);

//             if (literal_value == null) { // unit clause
//                 try self.t_literal.append(gpa, watch_b);
//                 try self.t_level.append(gpa, level);
//                 try self.t_reason.append(gpa, .init(clause));
//             } else if (literal_value == false) {
//                 return true; // conflict
//             }

//             clause_index += 1;
//         }

//         self.propagated += 1;
//     }

//     return false; // no conflict
// }

// /// check if a literal is currently unassigned or satisfied
// fn evalLiteral(self: *const @This(), literal: u32) ?bool {
//     switch (self.values.items[literal / 2]) {
//         .neg => return literal & 1 == 1,
//         .pos => return literal & 1 == 0,
//         .none => return null,
//     }
// }
