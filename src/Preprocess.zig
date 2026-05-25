//! Splits CNF with N-literal clauses into 2/3-literal clauses
//! Creates an adjacency list to do so (using linked lists)

const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const Cnf = @import("Cnf.zig");

/// Finds good pairs of variables to factor out of CNF; the pairs of variables
/// are the most common pairs across clauses. Constructs a partial adjacency
/// list to do so, this is a fairly expensive function.
///
/// NOTE: this won't work correctly if you have duplicate variables in clauses -
/// it will double-count and not accurately pick variable pairs that occur the
/// most within clauses. This step should come AFTER that naive simplification.
pub const Pair = struct { lhs: u32, rhs: u32, count: u32 };
pub fn factorPairs(gpa: Allocator, cnf: *const Cnf) ![]const Pair {
    // ------------------------------------------------------------------------
    // create an adjacency list of variables in considered clauses

    const Index = enum(u32) { none = 0, _ };
    const Node = struct { variable: u32, next: Index, count: u32 };

    var linked_list: std.MultiArrayList(Node) = .empty;
    defer linked_list.deinit(gpa);
    try linked_list.append(gpa, undefined);

    // Each variable element here is the root of a linked list, whose nodes
    // live within linked_list. This way we have random insertion without a
    // time or space tradeoff, unless we are counting random fetch / store.
    const variables = try gpa.alloc(Index, cnf.variable_count + 1);
    defer gpa.free(variables);
    @memset(variables, .none);

    for (0..cnf.clauseCount()) |clause| {
        const clause_u32: u32 = @intCast(clause);
        const literals = cnf.clauseLiterals(clause_u32);

        for (literals) |lhs| {
            pairwise: for (literals) |rhs| {
                const lhs_variable: u32 = @abs(lhs);
                const rhs_variable: u32 = @abs(rhs);

                // do not consider the opposite edges
                if (lhs_variable >= rhs_variable) continue;

                // locate and increment an existing count
                var index: *Index = &variables[lhs_variable];
                while (index.* != .none) {
                    // get the node at the current position
                    const int_index = @intFromEnum(index.*);
                    const node = linked_list.get(int_index);

                    if (node.variable == rhs_variable) {
                        // we found an existing link, increment it
                        linked_list.items(.count)[int_index] += 1;
                        // skip to considering the next pair
                        continue :pairwise;
                    }

                    // advance to the next node
                    index = &linked_list.items(.next)[int_index];
                }

                // create a new count for a new found pair
                index.* = @enumFromInt(linked_list.len);
                try linked_list.append(gpa, .{
                    .variable = rhs_variable,
                    .next = .none,
                    .count = 1,
                });
            }
        }
    }

    // ------------------------------------------------------------------------
    // determine the pair that occurs the most, based off of this list

    var pairs: std.ArrayList(Pair) = .empty;
    errdefer pairs.deinit(gpa);

    // index 0 does not map to any variable - they start from one
    for (variables[1..], 1..) |start_index, lhs| {
        var index: Index = start_index;
        while (index != .none) {
            // get the node at the current position
            const int_index = @intFromEnum(index);
            const node = linked_list.get(int_index);

            // there are no nodes with count = 0
            assert(node.count != 0);

            // skip pairs that only occur once
            if (node.count > 1) {
                // append the pair to the list
                assert(lhs < node.variable);
                try pairs.append(gpa, .{
                    .lhs = @intCast(lhs),
                    .rhs = node.variable,
                    .count = node.count,
                });
            }

            // Advance to the next pair
            index = node.next;
        }
    }

    return try pairs.toOwnedSlice(gpa);
}

/// Finds the number of distinct variables that are in an equation with each
/// variable. This can be used to decide which variables to assign first.
pub fn variablePopularity(gpa: Allocator, cnf: *const Cnf) ![]const u32 {
    // ------------------------------------------------------------------------
    // create an adjacency list of variables, and count the length of the list

    const Node = struct { variable: u32, next: u32 };
    var linked_list: std.ArrayList(Node) = .empty;
    defer linked_list.deinit(gpa);

    // Each variable element here is the root of a linked list, whose nodes
    // live within linked_list. This way we have random insertion without a
    // time or space tradeoff, unless we are counting random fetch / store.
    const variables = try gpa.alloc(u32, cnf.variable_count + 1);
    defer gpa.free(variables);
    @memset(variables, 0);

    // The length of the linked list for each variable - our output
    const lengths = try gpa.alloc(u32, cnf.variable_count + 1);
    errdefer gpa.free(lengths);
    @memset(lengths, 0);

    for (0..cnf.clauseCount()) |clause| {
        const clause_u32: u32 = @intCast(clause);
        const literals = cnf.clauseLiterals(clause_u32);

        for (literals) |lhs| {
            pairwise: for (literals) |rhs| {
                const lhs_variable: u32 = @abs(lhs);
                const rhs_variable: u32 = @abs(rhs);

                // do not consider the same variable
                if (lhs_variable == rhs_variable) continue;

                var index: *u32 = &variables[lhs_variable];
                for (0..lengths[lhs_variable]) |_| {
                    // skip this pair if it is already in the linked list
                    const variable = linked_list.items[index.*].variable;
                    if (variable == rhs_variable) continue :pairwise;
                    // advance to the next node in the chain
                    index = &linked_list.items[index.*].next;
                }

                // update the index and create a new entry
                index.* = @intCast(linked_list.items.len);
                lengths[lhs_variable] += 1;
                try linked_list.append(gpa, .{
                    .variable = rhs_variable,
                    .next = undefined,
                });
            }
        }
    }

    return lengths;
}

// A simple sugar to cut down on text bytes in each test
const expectEqualSlices = std.testing.expectEqualSlices;

fn testFactorPairs(cnf_text: []const u8, expected: []const Pair) !void {
    const gpa = std.testing.allocator;
    var reader: std.Io.Reader = .fixed(cnf_text);
    var cnf: Cnf = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    const actual = try factorPairs(gpa, &cnf);
    defer gpa.free(actual);

    try expectEqualSlices(Pair, expected, actual);
}

test "factorPairs does not crash on empty CNF" {
    try testFactorPairs(
        \\p cnf 0 0
        \\
    , &.{});
}

test "factorPairs works with signed variables" {
    try testFactorPairs(
        \\p cnf 2 5
        \\1 2 0
        \\1 2 0
        \\1 -2 0
        \\-1 2 0
        \\-1 -2 0
        \\
    , &.{
        .{ .lhs = 1, .rhs = 2, .count = 5 },
    });
}

test "factorPairs with two pairs and simple CNF" {
    try testFactorPairs(
        \\p cnf 5 3
        \\-2 5 -3 0
        \\1 4 0
        \\-4 1 2 5 0
        \\
    , &.{
        .{ .lhs = 1, .rhs = 4, .count = 2 },
        .{ .lhs = 2, .rhs = 5, .count = 2 },
    });
}

fn testVariablePopularity(cnf_text: []const u8, expected: []const u32) !void {
    const gpa = std.testing.allocator;
    var reader: std.Io.Reader = .fixed(cnf_text);
    var cnf: Cnf = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    const actual = try variablePopularity(gpa, &cnf);
    defer gpa.free(actual);

    try expectEqualSlices(u32, expected, actual);
}

test "variablePopularity does not crash on empty CNF" {
    try testVariablePopularity(
        \\p cnf 0 0
        \\
    , &.{0});
}

test "variablePopularity works with signed variables" {
    try testVariablePopularity(
        \\p cnf 2 5
        \\1 2 0
        \\1 2 0
        \\1 -2 0
        \\-1 2 0
        \\-1 -2 0
        \\
    , &.{ 0, 1, 1 });
}

test "variablePopularity with two pairs and simple CNF" {
    try testVariablePopularity(
        \\p cnf 5 3
        \\-2 5 -3 0
        \\1 4 0
        \\-4 1 2 5 0
        \\
    , &.{ 0, 3, 4, 2, 3, 4 });
}
