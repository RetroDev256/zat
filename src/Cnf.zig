const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const Reader = std.Io.Reader;

/// a per-clause offset into the list of concatenated literals it resides
l_offsets: []const u32,
/// a per-clause concatenated list of literals that belong to that clause
l_list: []const i32,
/// a per-variable offset into the list of concatenated clauses it resides
c_offsets: []const u32,
/// a per-variable concatenated list of clauses that reference the variable
c_list: []const u32,

/// Parse CNF from a strict subset of DIMACS CNF
pub fn parse(gpa: Allocator, reader: *Reader) !@This() {

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

    // a per-clause offset into the list of concatenated literals it resides
    const l_offsets = try gpa.alloc(u32, c_count + 1);
    errdefer gpa.free(l_offsets);

    // a per-clause concatenated list of literals that belong to that clause
    var l_list: std.ArrayList(i32) = .empty;
    defer l_list.deinit(gpa);

    // a per variable count of distinct clauses it is a literal within
    const v_c_counts = try gpa.alloc(u32, v_count + 1);
    defer gpa.free(v_c_counts);
    @memset(v_c_counts, 0);

    // parse the CNF clauses

    var l_off: u32 = 0;
    l_offsets[0] = 0;

    for (0..c_count) |clause| {
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
            const literal = try std.fmt.parseInt(i32, int_str, 10);
            const variable = @abs(literal);

            // verify that the term is valid for the cnf header
            if (variable > v_count) return error.InvalidTerm;

            // mark this literal as being used in a clause
            v_c_counts[variable] += 1;
            for (0..terms) |past| {
                const idx = l_list.items.len - terms + past;
                if (@abs(l_list.items[idx]) == variable) {
                    // literal appears earlier in clause
                    v_c_counts[variable] -= 1;
                    break;
                }
            }

            // add the term to the list of literals
            try l_list.append(gpa, literal);
            terms += 1;
        }

        // verify end of the clause
        const discard = try reader.discardShort(2); // "0\n"
        if (discard != 2) return error.DimacsCnfTruncated;
        if (terms == 0) return error.ExpectedClauseTerm;

        // add clause offset to the list - preallocated
        l_off += terms; // `terms` terms in the clause
        l_offsets[clause + 1] = l_off;
    }

    // verify end of the stream

    if (reader.peekByte()) |_| {
        return error.CnfTooLong;
    } else |err| switch (err) {
        error.EndOfStream => {},
        else => return err,
    }

    // construct the reverse mappings

    // a per-variable offset into the list of concatenated clauses it resides
    const c_offsets = try gpa.alloc(u32, v_count + 2);
    errdefer gpa.free(c_offsets);

    var c_off: u32 = 0;
    c_offsets[0] = 0;
    c_offsets[1] = 0;

    for (1..v_count + 1) |variable| {
        c_off += v_c_counts[variable];
        c_offsets[variable + 1] = c_off;
    }

    // a per-variable concatenated list of clauses that reference the variable
    const c_list = try gpa.alloc(u32, c_off);
    errdefer gpa.free(c_list);

    for (0..c_count) |clause| {
        const start = l_offsets[clause];
        const end = l_offsets[clause + 1];
        per_clause: for (l_list.items[start..end]) |literal| {
            const variable = @abs(literal);
            const base_off = c_offsets[variable];
            const limit_off = c_offsets[variable + 1];
            const target_off = limit_off - v_c_counts[variable];

            // check if the clause already references the variable
            for (base_off..target_off) |off| {
                if (c_list[off] == clause) {
                    continue :per_clause;
                }
            }

            // record the clause as referencing the variable
            c_list[target_off] = @intCast(clause);
            v_c_counts[variable] -= 1;
        }
    }

    for (v_c_counts) |x| {
        assert(x == 0);
    }

    return .{
        .l_offsets = l_offsets,
        .l_list = try l_list.toOwnedSlice(gpa),
        .c_offsets = c_offsets,
        .c_list = c_list,
    };
}

pub fn deinit(self: *@This(), gpa: Allocator) void {
    defer self.* = undefined;
    gpa.free(self.l_offsets);
    gpa.free(self.l_list);
    gpa.free(self.c_offsets);
    gpa.free(self.c_list);
}

/// returns the literals in a clause
pub fn clauseLiterals(self: *const @This(), clause: u32) []const i32 {
    assert(clause < self.clauseCount()); // must be a valid clause
    const start = self.l_offsets[clause];
    const end = self.l_offsets[clause + 1];
    return self.l_list[start..end];
}

/// returns the clauses referencing a variable
pub fn variableClauses(self: *const @This(), variable: u32) []const u32 {
    assert(variable != 0 and variable <= self.variableCount()); // valid
    const start = self.c_offsets[variable];
    const end = self.c_offsets[variable + 1];
    return self.c_list[start..end];
}

/// number of clauses within the CNF
pub fn clauseCount(self: *const @This()) u32 {
    return @intCast(self.l_offsets.len - 1);
}

/// number of variables within the CNF
pub fn variableCount(self: *const @This()) u32 {
    return @intCast(self.c_offsets.len - 1);
}

// A simple sugar to cut down on text bytes in each test
const expectEqualSlices = std.testing.expectEqualSlices;

test "cnf can parse input lacking cnf clauses" {
    const cnf_text = "p cnf 0 0\n";

    const gpa = std.testing.allocator;
    var reader = Reader.fixed(cnf_text);
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    try expectEqualSlices(u32, &.{0}, cnf.l_offsets);
    try expectEqualSlices(i32, &.{}, cnf.l_list);
    try expectEqualSlices(u32, &.{ 0, 0 }, cnf.c_offsets);
    try expectEqualSlices(u32, &.{}, cnf.c_list);
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

    try expectEqualSlices(u32, &.{0}, cnf.l_offsets);
    try expectEqualSlices(i32, &.{}, cnf.l_list);
    try expectEqualSlices(u32, &.{ 0, 0 }, cnf.c_offsets);
    try expectEqualSlices(u32, &.{}, cnf.c_list);
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

    try expectEqualSlices(u32, &.{ 0, 1 }, cnf.l_offsets);
    try expectEqualSlices(i32, &.{1}, cnf.l_list);
    try expectEqualSlices(u32, &.{ 0, 0, 1 }, cnf.c_offsets);
    try expectEqualSlices(u32, &.{0}, cnf.c_list);
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

    try expectEqualSlices(u32, &.{ 0, 3, 5, 9 }, cnf.l_offsets);
    try expectEqualSlices(i32, &.{ -2, 5, -3, 1, 4, -4, 1, 2, 5 }, cnf.l_list);
    try expectEqualSlices(u32, &.{ 0, 0, 2, 4, 5, 7, 9 }, cnf.c_offsets);
    try expectEqualSlices(u32, &.{ 1, 2, 0, 2, 0, 1, 2, 0, 2 }, cnf.c_list);
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
    var reader = Reader.fixed(cnf_text);
    var cnf: @This() = try .parse(gpa, &reader);
    defer cnf.deinit(gpa);

    try expectEqualSlices(i32, &.{ -2, 5, -3 }, cnf.clauseLiterals(0));
    try expectEqualSlices(i32, &.{ 1, 4 }, cnf.clauseLiterals(1));
    try expectEqualSlices(i32, &.{ -4, 1, 2, 5 }, cnf.clauseLiterals(2));
}

test "variableClauses works as expected" {
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

    try expectEqualSlices(u32, &.{ 1, 2 }, cnf.variableClauses(1));
    try expectEqualSlices(u32, &.{ 0, 2 }, cnf.variableClauses(2));
    try expectEqualSlices(u32, &.{0}, cnf.variableClauses(3));
    try expectEqualSlices(u32, &.{ 1, 2 }, cnf.variableClauses(4));
    try expectEqualSlices(u32, &.{ 0, 2 }, cnf.variableClauses(5));
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
