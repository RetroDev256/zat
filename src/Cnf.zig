const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const Reader = std.Io.Reader;

/// a per-clause offset into the list of concatenated literals it resides
/// the length of offsets is one more than the number of clauses
offsets: []const u32,
/// a per-clause concatenated list of literals that belong to that clause
/// the length of literals is equal to the last element of offsets
literals: []const i32,
/// the number of variables within the CNF clauses
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
/// - non-comment tokens after all clauses return an error
pub fn parse(gpa: Allocator, reader: *Reader) !@This() {
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
            const offsets = try gpa.alloc(u32, h_clauses + 1);
            errdefer gpa.free(offsets);
            var literals: std.ArrayList(i32) = .empty;
            errdefer literals.deinit(gpa);

            var clause_count: u32 = 0;
            offsets[0] = 0;

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
                    if (clause_count >= h_clauses) {
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

                    clause_count += 1; // record existence of each clause
                    offsets[clause_count] = @intCast(literals.items.len);
                    continue :mid_level .start; // resume parsing clauses
                },
            }

            if (clause_count != h_clauses) {
                return error.MissingClauses;
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
                .offsets = offsets,
                .literals = try literals.toOwnedSlice(gpa),
                .variable_count = h_variables,
            };
        },
    }
}

pub fn deinit(self: *@This(), gpa: Allocator) void {
    defer self.* = undefined;
    gpa.free(self.offsets);
    gpa.free(self.literals);
}

fn takeInteger(comptime T: type, reader: *Reader) !T {
    const info: std.builtin.Type.Int = @typeInfo(T).int;
    const digits = comptime std.math.log2_int_ceil(u16, info.bits);
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

fn tossComment(reader: *Reader) !void {
    // all comments terminate with a newline
    if (std.debug.runtime_safety)
        assert(try reader.takeByte() == 'c');
    _ = try reader.discardDelimiterInclusive('\n');
}

fn tossWhitespace(reader: *Reader) !void {
    while (reader.peekByte()) |byte| switch (byte) {
        ' ', '\t', '\n', '\r' => reader.toss(1),
        else => break,
    } else |err| switch (err) {
        error.EndOfStream => {},
        else => return err,
    }
}

/// returns the literals in a clause
pub fn clauseLiterals(self: *const @This(), clause: u32) []const i32 {
    assert(clause < self.clauseCount()); // must be a valid clause
    const start = self.offsets[clause];
    const end = self.offsets[clause + 1];
    return self.literals[start..end];
}

/// number of clauses within the CNF
pub fn clauseCount(self: *const @This()) u32 {
    return @intCast(self.offsets.len - 1);
}

// A simple sugar to cut down on text bytes in each test
const expectEqualSlices = std.testing.expectEqualSlices;

test "takeInteger takes one and only one integer" {
    const int_str = "-123 4 -5 -5 5 0 -7";
    var reader: Reader = .fixed(int_str);

    inline for (&.{ -123, 4, -5, -5, 5, 0, -7 }) |expected| {
        const actual = try takeInteger(i32, &reader);
        try std.testing.expectEqual(expected, actual);
        try tossWhitespace(&reader);
    }
}

test "cnf can parse input lacking cnf clauses" {
    const cnf_text = "p cnf 0 0\n";

    const gpa = std.testing.allocator;
    var reader: Reader = .fixed(cnf_text);
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    try expectEqualSlices(u32, &.{0}, cnf.offsets);
    try expectEqualSlices(i32, &.{}, cnf.literals);
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
    var reader: Reader = .fixed(cnf_text);
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    try expectEqualSlices(u32, &.{0}, cnf.offsets);
    try expectEqualSlices(i32, &.{}, cnf.literals);
}

test "cnf can parse one valid clause" {
    const cnf_text =
        \\p cnf 1 1
        \\1 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader: Reader = .fixed(cnf_text);
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    try expectEqualSlices(u32, &.{ 0, 1 }, cnf.offsets);
    try expectEqualSlices(i32, &.{1}, cnf.literals);
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
    var reader: Reader = .fixed(cnf_text);
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    try expectEqualSlices(u32, &.{ 0, 3, 5, 9 }, cnf.offsets);
    try expectEqualSlices(i32, &.{ -2, 5, -3, 1, 4, -4, 1, 2, 5 }, cnf.literals);
}

test "clauseLiterals works as expected" {
    const cnf_text =
        \\c this is one comment
        \\c this is another
        \\p cnf 5 3
        \\-2 5 -3 0
        \\1 4 0
        \\-4 1 2 5 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader: Reader = .fixed(cnf_text);
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    try expectEqualSlices(i32, &.{ -2, 5, -3 }, cnf.clauseLiterals(0));
    try expectEqualSlices(i32, &.{ 1, 4 }, cnf.clauseLiterals(1));
    try expectEqualSlices(i32, &.{ -4, 1, 2, 5 }, cnf.clauseLiterals(2));
}

test "cnf rejects literals that exceed the variable count" {
    const cnf_text =
        \\c if there are at most 3 variables, 4 cannot exist
        \\p cnf 3 1
        \\-2 4 3 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader: Reader = .fixed(cnf_text);
    const cnf_error = @This().parse(gpa, &reader);
    try std.testing.expectError(error.InvalidTerm, cnf_error);
}
