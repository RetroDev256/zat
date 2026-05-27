//! Splits CNF with N-literal clauses into 2/3-literal clauses
//! Creates an adjacency list to do so (using linked lists)

const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const Cnf = @import("Cnf.zig");

const Pair = struct {
    lhs: u32,
    rhs: u32,
    count: u32,
};

/// Finds good pairs of variables to factor out of CNF; the pairs of variables
/// are the most common pairs across clauses. This is an expensive function.
/// Asserts that you do not have duplicate variables within your clauses.
pub fn factorPairs(gpa: Allocator, cnf: *const Cnf) ![]const Pair {
    // ------------------------------------------------------------------------
    // verify that clauses do not contain duplicate variables

    if (std.debug.runtime_safety) {
        for (0..cnf.clauseCount()) |clause| {
            for (cnf.clauseLiterals(@intCast(clause)), 0..) |lhs, lhs_idx| {
                for (cnf.clauseLiterals(@intCast(clause))[0..lhs_idx]) |rhs| {
                    assert(@abs(lhs) != @abs(rhs));
                }
            }
        }
    }

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

// TODO: SIMPLIFY

/// Based on variablePopularity - returns a list of variables in decreasing
/// order of how many distinct variables are on related equations - can be
/// used as a heuristic ordering for which variables to set next.
pub fn variablePriority(gpa: Allocator, cnf: *const Cnf) ![]const u32 {
    const popularities = try variablePopularity(gpa, cnf);
    defer gpa.free(popularities);

    // ------------------------------------------------------------------------
    // construct a map of the number of popularities per popularity
    // count the number of distinct popularities

    const pop_count = try gpa.alloc(u32, cnf.variable_count);
    defer gpa.free(pop_count);

    var bucket_count: u32 = 0;
    @memset(pop_count, 0);

    for (popularities[1..]) |pop| {
        if (pop_count[pop] == 0) {
            bucket_count += 1;
        }
        pop_count[pop] += 1;
    }

    // ------------------------------------------------------------------------
    // construct a reverse mapping from popularities to offset bucket index
    // construct a map of offsets into the destination list to place things

    const pop_to_bucket = try gpa.alloc(u32, cnf.variable_count);
    defer gpa.free(pop_to_bucket);

    const pop_offsets = try gpa.alloc(u32, bucket_count + 1);
    defer gpa.free(pop_offsets);

    @memset(pop_to_bucket, undefined);
    var total_offset: u32 = 0;
    var bucket_index: u32 = 0;
    pop_offsets[0] = 0;

    for (0..cnf.variable_count) |reverse| {
        // skip popularities which do not exist
        const index = cnf.variable_count - reverse - 1;
        const popularity = pop_count[index];
        if (popularity == 0) continue;

        // set the mapping for population to bucket
        pop_to_bucket[index] = bucket_index;
        bucket_index += 1;

        // set the mapping from population to offset
        total_offset += popularity;
        pop_offsets[bucket_index] = total_offset;
    }

    // ------------------------------------------------------------------------
    // copy all of the most popular variable indexes into the list

    const most_popular = try gpa.alloc(u32, cnf.variable_count);
    errdefer gpa.free(most_popular);

    // skip variable
    for (popularities[1..], 1..) |popularity, variable| {
        const bucket = pop_to_bucket[popularity];
        const remaining = pop_count[popularity];
        const end = pop_offsets[bucket + 1];
        most_popular[end - remaining] = @intCast(variable);
        pop_count[popularity] -= 1;
    }

    if (std.debug.runtime_safety) {
        for (pop_count) |remaining| {
            assert(remaining == 0);
        }
    }

    return most_popular;
}

pub const VCMapping = struct {
    offsets: []const u32,
    clauses: []const u32,

    pub fn deinit(self: *@This(), gpa: Allocator) void {
        defer self.* = undefined;
        gpa.free(self.offsets);
        gpa.free(self.clauses);
    }

    // returns the clauses containing a literal of the variable
    pub fn variableClauses(self: *const @This(), variable: u32) []const u32 {
        assert(variable != 0); // index 0 is invalid, there is no 0 variable
        const start = self.offsets[variable];
        const end = self.offsets[variable + 1];
        return self.clauses[start..end];
    }
};

/// Construct an inverse mapping from variables to clauses in linear time.
/// Asserts that you do not have duplicate variables within your clauses.
pub fn mapVariablesToClauses(gpa: Allocator, cnf: *const Cnf) !VCMapping {
    // ------------------------------------------------------------------------
    // count the number of clauses each variable is in, in linear time

    const histogram = try gpa.alloc(u32, cnf.variable_count + 1);
    defer gpa.free(histogram);
    @memset(histogram, 0);

    for (0..cnf.clauseCount()) |clause| {
        for (cnf.clauseLiterals(@intCast(clause)), 0..) |lhs, lhs_idx| {
            histogram[@abs(lhs)] += 1;

            if (std.debug.runtime_safety) {
                // do not have duplicate variables in clauses
                for (cnf.clauseLiterals(@intCast(clause))[0..lhs_idx]) |rhs| {
                    assert(@abs(lhs) != @abs(rhs));
                }
            }
        }
    }

    // -------------------------------------------------- 1, 2 ----------------------
    // create a list of offsets into the clause list for each variable

    const offsets = try gpa.alloc(u32, cnf.variable_count + 2);
    errdefer gpa.free(offsets);
    offsets[0] = undefined;
    offsets[1] = 0;

    var literal_offset: u32 = 0;
    for (histogram[1..], 1..) |count, variable| {
        literal_offset += count;
        offsets[variable + 1] = literal_offset;
    }

    // ------------------------------------------------------------------------
    // place each clause into the respective variable clause sub-list

    const clauses = try gpa.alloc(u32, literal_offset);
    errdefer gpa.free(clauses);

    for (0..cnf.clauseCount()) |clause| {
        for (cnf.clauseLiterals(@intCast(clause))) |literal| {
            const variable: u32 = @abs(literal);
            const upper = offsets[variable + 1];
            const remaining = histogram[variable];
            const index = upper - remaining;
            clauses[index] = @intCast(clause);
            histogram[variable] -= 1;
        }
    }

    return .{ .offsets = offsets, .clauses = clauses };
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

fn testMapVariablesToClauses(cnf_text: []const u8, expected: VCMapping) !void {
    const gpa = std.testing.allocator;
    var reader: std.Io.Reader = .fixed(cnf_text);
    var cnf: Cnf = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    var actual = try mapVariablesToClauses(gpa, &cnf);
    defer actual.deinit(gpa);

    // The first element of the offsets is undefined, as there is no 0 variable
    try expectEqualSlices(u32, expected.offsets[1..], actual.offsets[1..]);
    try expectEqualSlices(u32, expected.clauses, actual.clauses);
}

test "mapVariablesToClauses does not crash on empty CNF" {
    try testMapVariablesToClauses(
        \\p cnf 0 0
        \\
    , .{
        .offsets = &.{ undefined, 0 },
        .clauses = &.{},
    });
}

test "mapVariablesToClauses works with signed variables" {
    try testMapVariablesToClauses(
        \\p cnf 2 5
        \\1 2 0
        \\1 2 0
        \\1 -2 0
        \\-1 2 0
        \\-1 -2 0
        \\
    , .{
        .offsets = &.{ undefined, 0, 5, 10 },
        .clauses = &.{ 0, 1, 2, 3, 4, 0, 1, 2, 3, 4 },
    });
}

test "mapVariablesToClauses with two pairs and simple CNF" {
    try testMapVariablesToClauses(
        \\p cnf 5 3
        \\-2 5 -3 0
        \\1 4 0
        \\-4 1 2 5 0
        \\
    , .{
        .offsets = &.{ undefined, 0, 2, 4, 5, 7, 9 },
        .clauses = &.{ 1, 2, 0, 2, 0, 1, 2, 0, 2 },
    });
}

fn testMostPopularVariables(cnf_text: []const u8, expected: []const u32) !void {
    const gpa = std.testing.allocator;
    var reader: std.Io.Reader = .fixed(cnf_text);
    var cnf: Cnf = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    const actual = try variablePriority(gpa, &cnf);
    defer gpa.free(actual);

    try expectEqualSlices(u32, expected, actual);
}

test "variablePriority does not crash on empty CNF" {
    try testMostPopularVariables(
        \\p cnf 0 0
        \\
    , &.{});
}

test "variablePriority works with signed variables" {
    try testMostPopularVariables(
        \\p cnf 2 5
        \\1 2 0
        \\1 2 0
        \\1 -2 0
        \\-1 2 0
        \\-1 -2 0
        \\
    , &.{ 1, 2 });
}

test "variablePriority with two pairs and simple CNF" {
    try testMostPopularVariables(
        \\p cnf 5 3
        \\-2 5 -3 0
        \\1 4 0
        \\-4 1 2 5 0
        \\
    , &.{ 2, 5, 1, 4, 3 });
}
