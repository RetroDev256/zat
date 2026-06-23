const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const Io = std.Io;

/// each clause within the CNF, where each literal is EVEN if it is within the
/// clause, and ODD if it is within the clause, but also inverted - to convert
/// from literal to variable, divide by 2 - to see if it is inverted, AND by 1
clauses: std.ArrayList([]u32),
/// the number of variables (at maximum) within the clauses - this does not
/// necessarily mean that there are var_count variables, but that the largest
/// literal within any clause must not exceed 2 * var_count - due to inversion
var_count: u32,

/// Parser for a superset of DIMACS CNF - supports comments, clauses (they must
/// all end with a 0), whitespace (spaces, tabs, newlines, carriage returns),
/// and a trailing % (to denote end of clauses). This should parse most DIMACS
/// CNF files. NOTE: the variable count in the header is the maximum literal
/// absolute value that may occur, and the number of clauses in the header must
/// match the number of clauses within the file exactly.
pub fn parse(gpa: Allocator, reader: *Io.Reader) !@This() {
    var clauses: std.ArrayList([]u32) = .empty;
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
            var literals: std.ArrayList(u32) = .empty;
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
                        const raw_term = try takeInteger(i32, reader);
                        if (raw_term == 0) break; // end of clause
                        if (@abs(raw_term) > h_variables)
                            return error.InvalidTerm;

                        const variable = @abs(raw_term) - 1;
                        const sign = @intFromBool(raw_term < 0);
                        try literals.append(gpa, variable * 2 + sign);
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
                // end of file sometimes marked by 0 after a %
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
                .var_count = h_variables,
            };
        },
    }
}

pub fn deinit(self: *@This(), gpa: Allocator) void {
    defer self.* = undefined;

    for (self.clauses.items) |clause| {
        gpa.free(clause);
    }

    self.clauses.deinit(gpa);
}

pub fn serialize(self: *const @This(), writer: *Io.Writer) !void {
    try writer.print("p cnf {} {}\n", .{
        self.var_count,
        self.clauses.items.len,
    });

    for (self.clauses.items) |clause| {
        for (clause) |literal| {
            if (literal & 1 == 1) {
                try writer.print("-{} ", .{literal / 2});
            } else {
                try writer.print("{} ", .{literal / 2});
            }
        }
        try writer.writeAll("0\n");
    }
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

test "takeInteger takes one and only one integer" {
    var reader: Io.Reader = .fixed("123 4 5 5 9 0 7");
    inline for (&.{ 123, 4, 5, 5, 9, 0, 7 }) |expected| {
        const actual = try takeInteger(u32, &reader);
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

    try expectEqual(cnf.var_count, 0);
    try expectEqual(cnf.clauses.items.len, 0);
}

test "cnf parses single 1 as a positive literal" {
    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed("p cnf 1 1 1 0");
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    try expectEqual(1, cnf.var_count);
    try expectEqual(1, cnf.clauses.items.len);
    try expectEqualSlices(u32, &.{0}, cnf.clauses.items[0]);
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

    try expectEqual(cnf.var_count, 0);
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

    try expectEqual(cnf.var_count, 1);
    try expectEqual(cnf.clauses.items.len, 1);
    try expectEqualSlices(u32, &.{0}, cnf.clauses.items[0]);
}

test "cnf does not crash with simple cnf" {
    const cnf_text =
        \\p cnf 2 2
        \\1 2 0
        \\1 -2 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed(cnf_text);
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    try expectEqual(cnf.var_count, 2);
    try expectEqual(cnf.clauses.items.len, 2);
    try expectEqualSlices(u32, &.{ 0, 2 }, cnf.clauses.items[0]);
    try expectEqualSlices(u32, &.{ 0, 3 }, cnf.clauses.items[1]);
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

    try expectEqual(cnf.var_count, 5);
    try expectEqual(cnf.clauses.items.len, 3);
    try expectEqualSlices(u32, &.{ 3, 8, 5 }, cnf.clauses.items[0]);
    try expectEqualSlices(u32, &.{ 0, 6 }, cnf.clauses.items[1]);
    try expectEqualSlices(u32, &.{ 7, 0, 2, 8 }, cnf.clauses.items[2]);
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

test "cnf parses a really weird file" {
    const cnf_text =
        \\c this is a comment
        \\p cnf 5 3 -2
        \\          5 -3 0 c this is a comment
        \\1
        \\4 0   -4 1 2      5 0 % 0
    ;

    const gpa = std.testing.allocator;
    var reader: Io.Reader = .fixed(cnf_text);
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    try expectEqual(cnf.var_count, 5);
    try expectEqual(cnf.clauses.items.len, 3);
    try expectEqualSlices(u32, &.{ 3, 8, 5 }, cnf.clauses.items[0]);
    try expectEqualSlices(u32, &.{ 0, 6 }, cnf.clauses.items[1]);
    try expectEqualSlices(u32, &.{ 7, 0, 2, 8 }, cnf.clauses.items[2]);
}
