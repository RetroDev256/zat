const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const Io = std.Io;

clauses: std.ArrayList([]i32),
variable_count: u32,

/// Parser for a strict superset of DIMACS CNF:
/// - comments may occur before and after the DIMACS header
/// - comments may occur before, after, and between clauses
/// - comments start with 'c' and terminate with a newline
/// - the header starts with 'p' and terminate with a newline
/// - the header line is of format "p cnf VARIABLES CLAUSES"
/// - "VARIABLES" is the maximum variable index that may occur
/// - "CLAUSES" is the exact number of clauses in the CNF
/// - clauses are lists of literals separated by whitespace
/// - literals are base-10 signed integers, sign denoting negation
/// - literals whose absolute value exceeds VARS return an error
/// - all clauses must end in '0', including the last clause
/// - empty clauses (eg. "0") *are* allowed within the CNF
/// - empty lines *are* tolerated within this CNF parser
/// - carriage returns *are* tolerated within this parser
/// - end-of-clauses can be marked with a % if desired
/// - end-of-file can be marked with a 0 if desired
/// - ending non-comment tokens return an error
pub fn parse(gpa: Allocator, reader: *Io.Reader) !@This() {
    var clauses: std.ArrayList([]i32) = .empty;
    errdefer clauses.deinit(gpa);

    // header: "p cnf h_variables h_clauses"
    var h_variables: u32 = undefined;
    var h_clauses: u32 = undefined;

    top_level: switch (enum { start, header, clauses }.start) {
        .start => {
            // skip whitespace, comments, branch on 'p'
            while (true) switch (try reader.peekByte()) {
                ' ', '\t', '\n', '\r' => reader.toss(1),
                'p' => continue :top_level .header,
                'c' => try tossComment(reader),
                else => return error.UnexpectedByte,
            };
        },
        .header => {
            // skip the "p cnf " string
            assert(try reader.takeByte() == 'p');
            try tossWhitespace(reader);
            const cnf = try reader.take(3);
            if (cnf[0] != 'c') return error.InvalidHeader;
            if (cnf[1] != 'n') return error.InvalidHeader;
            if (cnf[2] != 'f') return error.InvalidHeader;
            try tossWhitespace(reader);

            // parse the "VARIABLES CLAUSES" bit
            h_variables = try takeInteger(u32, reader);
            try tossWhitespace(reader);
            h_clauses = try takeInteger(u32, reader);
            try tossWhitespace(reader);

            // continue on to clause parsing
            continue :top_level .clauses;
        },
        .clauses => {
            var literals: std.ArrayList(i32) = .empty;
            defer literals.deinit(gpa);

            mid_level: switch (enum { start, clause }.start) {
                .start => {
                    // skip whitespace, branch on other bytes
                    while (reader.peekByte()) |byte| switch (byte) {
                        ' ', '\t', '\n', '\r' => reader.toss(1),
                        'c' => try tossComment(reader),
                        else => continue :mid_level .clause,
                    } else |err| switch (err) {
                        error.EndOfStream => {},
                        else => return err,
                    }
                },
                .clause => {
                    if (clauses.items.len >= h_clauses) {
                        break :mid_level; // no more
                    }

                    while (true) {
                        try tossWhitespace(reader);
                        const term = try takeInteger(i32, reader);
                        if (term == 0) break; // end of clause
                        if (@abs(term) > h_variables)
                            return error.InvalidTerm;
                        try literals.append(gpa, term);
                    }

                    const lit_slice = try literals.toOwnedSlice(gpa);
                    errdefer gpa.free(lit_slice);
                    try clauses.append(gpa, lit_slice);
                    continue :mid_level .start; // resume parsing clauses
                },
            }

            if (clauses.items.len != h_clauses) {
                return error.MissingClauses;
            }

            optional_percent: {
                // end of clauses sometimes marked by %
                try tossWhitespace(reader);
                const percent = reader.peekByte() catch |err| {
                    if (err == error.EndOfStream)
                        break :optional_percent;
                    return err; // we don't handle read failures
                };

                if (percent == '%') reader.toss(1); // skip the %
            }

            optional_zero: {
                // end of file sometimes marked by 0
                try tossWhitespace(reader);
                const percent = reader.peekByte() catch |err| {
                    if (err == error.EndOfStream)
                        break :optional_zero;
                    return err; // we don't handle read failures
                };

                if (percent == '0') reader.toss(1); // skip the 0
            }

            // skip trailing whitespace and comments
            while (reader.peekByte()) |byte| switch (byte) {
                ' ', '\t', '\n', '\r' => reader.toss(1),
                'c' => try tossComment(reader),
                else => return error.UnexpectedByte,
            } else |err| switch (err) {
                error.EndOfStream => {},
                else => return err,
            }

            return .{
                .clauses = clauses,
                .variable_count = h_variables,
            };
        },
    }
}

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

/// assert that clauses and literals are in ascending order
fn assertClauseOrder(self: *const @This()) !void {
    if (!std.debug.runtime_safety) return;
    if (self.clauses.items.len == 0) return;
    const clauses = self.clauses.items;

    if (clauses.len > 0) for (1..clauses) |i| {
        assert(clauses[i - 1] < clauses[i]);
        if (clauses[i].len > 0) for (1..clauses[i].len) |x| {
            assert(clauses[i][x - 1] < clauses[i][x + 1]);
        };
    };
}

/// sort clauses and literals into ascending order
pub fn orderCnf(self: *@This()) void {
    const clauses = self.clauses.items;

    // Order the clauses from smallest to largest, subsume right
    std.mem.sortUnstable([]i32, clauses, {}, lessThanClause);

    for (clauses) |clause| {
        // Order the terms in each clause from least to greatest
        std.mem.sortUnstable(i32, clause, {}, std.sort.asc(i32));
    }
}

/// comparison function for sorting clauses by arity
fn lessThanClause(_: void, lhs: []i32, rhs: []i32) bool {
    return lhs.len < rhs.len;
}

/// remove clauses that are deemed trivially redundant
/// - eg. they are a subset of another clause
pub fn subsume(self: *@This(), gpa: Allocator) !void {
    if (self.clauses.items.len == 0) return;
    const clauses = self.clauses.items;

    // Clauses and literals must be ordered
    try self.assertClauseOrder();

    // Create a map of the redundant clauses
    const redundant = try gpa.alloc(bool, clauses.len);
    defer gpa.free(redundant);
    @memset(redundant, false);

    var a: usize = 0;
    while (a < clauses.len) : (a += 1) {
        if (redundant[a]) continue;

        var b: usize = a + 1;
        while (b < clauses.len) : (b += 1) {
            if (redundant[b]) continue;

            const c_a = clauses[a];
            const c_b = clauses[b];
            redundant[b] = subsetOf(c_a, c_b);
        }
    }

    // Remove all the redundant clauses
    var write: usize = 0;
    for (clauses, 0..) |clause, index| {
        if (redundant[index]) {
            gpa.free(clause);
        } else {
            clauses[write] = clause;
            write += 1;
        }
    }

    // Update the number of clauses
    clauses.len = write;
}

/// check if one clause is a subset of another - both clauses must be sorted in
/// ascending order of terms - lhs must contain less or equal elements than rhs
fn subsetOf(noalias lhs: []const i32, noalias rhs: []const i32) bool {
    assert(lhs.len <= rhs.len);
    if (std.debug.runtime_safety) {
        if (lhs.len > 0) for (0..lhs.len - 1) |i|
            assert(lhs[i] < lhs[i + 1]);
        if (rhs.len > 0) for (0..rhs.len - 1) |i|
            assert(rhs[i] < rhs[i + 1]);
    }

    var a: usize = 0;
    var b: usize = 0;

    while (a < lhs.len and b < rhs.len) {
        if (lhs[a] == rhs[b]) {
            // match found, advance pointers
            a += 1;
            b += 1;
        } else if (lhs[a] > rhs[b]) {
            // rhs is too small, advance rhs
            b += 1;
        } else {
            // rhs can never contain lhs[a]
            return false;
        }
    }

    return a == lhs.len;
}

pub fn serialize(self: *const @This(), writer: *Io.Writer) !void {
    try writer.print("p cnf {} {}\n", .{
        self.variable_count,
        self.clauses.items.len,
    });

    for (self.clauses.items) |clause| {
        for (clause.literals) |literal| {
            try writer.print("{} ", .{literal});
        }
        try writer.writeAll("0\n");
    }
}

pub fn deinit(self: *@This(), gpa: Allocator) void {
    defer self.* = undefined;

    for (self.clauses.items) |clause| {
        gpa.free(clause);
    }

    self.clauses.deinit(gpa);
}

fn takeInteger(comptime T: type, reader: *Io.Reader) !T {
    const info: std.builtin.Type.Int = @typeInfo(T).int;
    const digits = comptime try std.math.divCeil(u16, info.bits, 3);
    // space for a possible negative sign and digits to hold type T
    const max_len = @intFromBool(info.signedness == .signed) + digits;

    var buf: [max_len]u8 = undefined;
    buf[0] = try reader.takeByte();
    var len: usize = 1;

    while (true) {
        const byte = reader.peekByte() catch |err| {
            if (err == error.EndOfStream) break;
            return err;
        };

        if (byte < '0' or byte > '9') break;
        if (len >= max_len) return error.IntegerTooLong;

        buf[len] = byte;
        reader.toss(1);
        len += 1;
    }

    return try std.fmt.parseInt(T, buf[0..len], 10);
}

fn tossComment(reader: *Io.Reader) !void {
    // all comments terminate with a newline
    if (std.debug.runtime_safety)
        assert(try reader.takeByte() == 'c');
    _ = try reader.discardDelimiterInclusive('\n');
}

fn tossWhitespace(reader: *Io.Reader) !void {
    while (reader.peekByte()) |byte| switch (byte) {
        ' ', '\t', '\n', '\r' => reader.toss(1),
        else => break,
    } else |err| switch (err) {
        error.EndOfStream => {},
        else => return err,
    }
}

// A simple sugar to cut down on text bytes in each test
const expectEqualSlices = std.testing.expectEqualSlices;
const expectEqual = std.testing.expectEqual;
const expect = std.testing.expect;

test "subsetOf works with empty list" {
    try expect(subsetOf(&.{}, &.{}));
}

test "subsetOf works with offset elements" {
    try expect(subsetOf(&.{3}, &.{ -2, -1, 3, 4 }));
}

test "subsetOf works with two elements" {
    try expect(subsetOf(&.{ -1, 4 }, &.{ -2, -1, 3, 4 }));
}

test "subsetOf works with equal elements" {
    try expect(subsetOf(&.{ -2, -1, 3, 4 }, &.{ -2, -1, 3, 4 }));
}

test "subsetOf returns false for missing element" {
    try expect(!subsetOf(&.{7}, &.{ -2, -1, 3 }));
}

test "subsetOf returns true for empty set subset" {
    try expect(subsetOf(&.{}, &.{ -2, -1, 3 }));
}

test "takeInteger takes one and only one integer" {
    const int_str = "-123 4 -5 -5 5 0 -7";
    var reader: Io.Reader = .fixed(int_str);

    inline for (&.{ -123, 4, -5, -5, 5, 0, -7 }) |expected| {
        const actual = try takeInteger(i32, &reader);
        try expectEqual(expected, actual);
        try tossWhitespace(&reader);
    }
}

test "cnf can parse input lacking cnf clauses" {
    const cnf_text = "p cnf 0 0\n";

    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed(cnf_text);
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    try expectEqual(cnf.variable_count, 0);
    try expectEqual(cnf.clauses.items.len, 0);
}

test "cnf can parse dimacs cnf file with comments" {
    const cnf_text =
        \\c this is one comment
        \\c
        \\c so was that previous line
        \\c and that one as well!
        \\p cnf 0 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed(cnf_text);
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    try expectEqual(cnf.variable_count, 0);
    try expectEqual(cnf.clauses.items.len, 0);
}

test "cnf can parse one valid clause" {
    const cnf_text =
        \\p cnf 1 1
        \\1 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed(cnf_text);
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    try expectEqual(cnf.variable_count, 1);
    try expectEqual(cnf.clauses.items.len, 1);
    try expectEqualSlices(i32, &.{1}, cnf.clauses.items[0]);
}

test "cnf can parse complicated clause" {
    const cnf_text =
        \\c this is one comment
        \\c this is another
        \\p cnf 5 3
        \\-2 5 -3 0
        \\1 4 0
        \\c how complex!
        \\-4 1 2 5 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed(cnf_text);
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    try expectEqual(cnf.variable_count, 5);
    try expectEqual(cnf.clauses.items.len, 3);
    try expectEqualSlices(i32, &.{ -2, 5, -3 }, cnf.clauses.items[0]);
    try expectEqualSlices(i32, &.{ 1, 4 }, cnf.clauses.items[1]);
    try expectEqualSlices(i32, &.{ -4, 1, 2, 5 }, cnf.clauses.items[2]);
}

test "cnf rejects literals that exceed the variable count" {
    const cnf_text =
        \\c if there are at most 3 variables, 4 cannot exist
        \\p cnf 3 1
        \\-2 4 3 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed(cnf_text);
    const cnf_error = @This().parse(gpa, &reader);
    try std.testing.expectError(error.InvalidTerm, cnf_error);
}
