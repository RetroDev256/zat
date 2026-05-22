const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const Reader = std.Io.Reader;

/// Number of variables
v_count: u32,
/// Offsets into literal for clauses
offsets: std.ArrayList(u32),
/// Concatenated iterals for clauses
literal: std.ArrayList(i32),

fn parse(gpa: Allocator, reader: *Reader) !@This() {

    // skip all of the comment lines

    while (true) {
        const byte = try reader.peekByte();
        if (byte == '\n') return error.EmptyLines;
        if (byte != 'c') break; // no comment
        _ = try reader.discardDelimiterInclusive('\n');
    }

    // parse the DIMACS CNF header

    const expected_header: []const u8 = "p cnf ";
    const header = try reader.take(expected_header.len);
    if (!std.mem.eql(u8, header, expected_header)) {
        return error.InvalidDimacsCnfHeader;
    }

    var v_count_int = try reader.takeDelimiterInclusive(' ');
    v_count_int.len -= 1; // remove the space from attention
    const v_count = try std.fmt.parseInt(u32, v_count_int, 10);

    var c_count_int = try reader.takeDelimiterInclusive('\n');
    c_count_int.len -= 1; // remove the newline from attention
    const c_count = try std.fmt.parseInt(u32, c_count_int, 10);

    var offsets: std.ArrayList(u32) = try .initCapacity(gpa, c_count + 1);
    errdefer offsets.deinit(gpa);

    var literal: std.ArrayList(i32) = .empty;
    errdefer literal.deinit(gpa);

    // parse the CNF clauses

    var offset: u32 = 0;
    try offsets.append(gpa, 0);

    for (0..c_count) |_| {
        var terms: u32 = 0;

        while (true) {

            // determine the nature of the next term
            const byte = try reader.peekByte();
            if (byte == 'c') return error.UnexpectedComment;
            if (byte == '\n') return error.EmptyLines;
            if (byte == '0') break; // end of clause

            // read the term - it is delimited by space
            var int_str = try reader.takeDelimiterInclusive(' ');
            int_str.len -= 1; // remove the space from attention
            const int = try std.fmt.parseInt(i32, int_str, 10);

            // verify that the term is valid for the cnf header
            if (@abs(int) > v_count) return error.InvalidTerm;

            // add the term to the list of literals
            try literal.append(gpa, int);
            terms += 1;
        }

        // verify end of the clause
        const discard = try reader.discardShort(2); // "0\n"
        if (discard != 2) return error.DimacsCnfTruncated;
        if (terms == 0) return error.ExpectedClauseTerm;

        // add clause offset to the list - preallocated
        offset += terms; // `terms` terms in the clause
        try offsets.append(Allocator.failing, offset);
    }

    // verify end of the stream

    if (reader.peekByte()) |_| {
        return error.CnfTooLong;
    } else |err| switch (err) {
        error.EndOfStream => {},
        else => return err,
    }

    return .{
        .v_count = v_count,
        .offsets = offsets,
        .literal = literal,
    };
}

fn clauseCount(self: *const @This()) usize {
    return self.offsets.items.len - 1;
}

fn deinit(self: *@This(), gpa: Allocator) void {
    defer self.* = undefined;
    self.offsets.deinit(gpa);
    self.literal.deinit(gpa);
}

test "cnf can parse input lacking cnf clauses" {
    const cnf_text = "p cnf 0 0\n";

    const gpa = std.testing.allocator;
    var reader = Reader.fixed(cnf_text);
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    assert(cnf.v_count == 0);
    assert(cnf.offsets.items.len == 1);
    assert(cnf.offsets.items[0] == 0);
    assert(cnf.literal.items.len == 0);
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
    var reader = Reader.fixed(cnf_text);
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    assert(cnf.v_count == 0);
    assert(cnf.offsets.items.len == 1);
    assert(cnf.offsets.items[0] == 0);
    assert(cnf.literal.items.len == 0);
}

test "cnf can parse one valid clause" {
    const cnf_text =
        \\p cnf 1 1
        \\1 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader = Reader.fixed(cnf_text);
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    assert(cnf.v_count == 1);
    assert(cnf.offsets.items.len == 2);
    assert(cnf.offsets.items[0] == 0);
    assert(cnf.literal.items.len == 1);
    assert(cnf.literal.items[0] == 1);
}

test "cnf can parse complicated clause" {
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
    var reader = Reader.fixed(cnf_text);
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    assert(cnf.v_count == 5);
    assert(cnf.offsets.items.len == 4);
    assert(cnf.literal.items.len == 9);
    try std.testing.expectEqualSlices(u32, &.{
        0, 3, 5, 9,
    }, cnf.offsets.items);
    try std.testing.expectEqualSlices(i32, &.{
        -2, 5, -3, 1, 4, -4, 1, 2, 5,
    }, cnf.literal.items);
}

test "cnf rejects inputs with space lines" {
    const cnf_text =
        \\
        \\c above and below should not be empty
        \\
        \\p cnf 0 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader = Reader.fixed(cnf_text);
    const cnf_error = @This().parse(gpa, &reader);
    try std.testing.expectError(error.EmptyLines, cnf_error);
}

test "cnf rejects empty lines between inputs" {
    const cnf_text =
        \\c the clause must be on the same line, ending in a "0\n"
        \\p cnf 2 1
        \\
        \\1 2 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader = Reader.fixed(cnf_text);
    const cnf_error = @This().parse(gpa, &reader);
    try std.testing.expectError(error.EmptyLines, cnf_error);
}

test "cnf rejects comments after dimacs cnf header" {
    const cnf_text =
        \\p cnf 2 1
        \\c this comment should not be here
        \\1 2 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader = Reader.fixed(cnf_text);
    const cnf_error = @This().parse(gpa, &reader);
    try std.testing.expectError(error.UnexpectedComment, cnf_error);
}

test "cnf rejects clauses that have zero terms" {
    const cnf_text =
        \\c must have at least one term
        \\p cnf 0 1
        \\0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader = Reader.fixed(cnf_text);
    const cnf_error = @This().parse(gpa, &reader);
    try std.testing.expectError(error.ExpectedClauseTerm, cnf_error);
}

test "cnf rejects files which have more lines than expected" {
    const cnf_text =
        \\c there should only be one clause here, not two
        \\p cnf 2 1
        \\1 -2 0
        \\-1 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader = Reader.fixed(cnf_text);
    const cnf_error = @This().parse(gpa, &reader);
    try std.testing.expectError(error.CnfTooLong, cnf_error);
}

test "cnf rejects terms that exceed the variable count" {
    const cnf_text =
        \\c if there are at most 3 variables, 4 cannot exist
        \\p cnf 3 1
        \\-2 4 3 0
        \\
    ;

    const gpa = std.testing.allocator;
    var reader = Reader.fixed(cnf_text);
    const cnf_error = @This().parse(gpa, &reader);
    try std.testing.expectError(error.InvalidTerm, cnf_error);
}
