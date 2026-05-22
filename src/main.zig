const std = @import("std");
const Cnf = @import("Cnf.zig");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const Io = std.Io;

const Solver = struct {
    /// Original CNF
    cnf: *Cnf,
    /// Values: +1 / 0 / -1
    values: std.ArrayList(i8),
    /// Boolean assignments history
    undo_trail: std.ArrayList(u32),

    fn init(gpa: Allocator, cnf: *Cnf) @This() {
        const values: std.ArrayList(i8) = .empty;
        errdefer values.deinit(gpa);

        try values.ensureTotalCapacity(cnf.v_count + 1);
        values.items.len = cnf.v_count + 1;
        @memset(values.items, 0);

        return .{
            .cnf = cnf,
            .values = values,
            .undo_trail = .empty,
        };
    }

    fn deinit(self: *@This(), gpa: Allocator) void {
        defer self.* = undefined;
        self.values.deinit(gpa);
        self.undo_trail.deinit(gpa);
    }

    // TODO: this might benefit from removing short-circuiting
    // returns true IFF each clause is assigned and not satisfiable
    fn clauseConflict(self: *const @This(), clause: u32) bool {
        const start = self.cnf.offsets.items[clause];
        const end = self.cnf.offsets.items[clause + 1];

        for (start..end) |lit_idx| {
            const lit = self.cnf.literal.items[lit_idx];
            const val = self.values.items[@abs(lit)];
            if (val == 0) return false; // unassigned

            if (lit < 0 and val == -1) return false;
            if (lit > 0 and val == 1) return false;
        }

        return true;
    }

    // TODO: this might benefit from removing short-circuiting
    // returns true IFF at least one clause is assigned and satisfiable
    fn clauseSatisfied(self: *const @This(), clause: u32) bool {
        const start = self.cnf.offsets.items[clause];
        const end = self.cnf.offsets.items[clause + 1];

        for (start..end) |lit_idx| {
            const lit = self.cnf.literal.items[lit_idx];
            const val = self.values.items[@abs(lit)];
            if (val == 0) return true; // unassigned

            if (lit < 0 and val == -1) return true;
            if (lit > 0 and val == 1) return true;
        }

        return false;
    }

    /// Returns the variable index (and sign value) that would be REQUIRED to
    /// validate the clause. If the clause is not a unit clause, 0 is returned.
    fn unitClause(self: *const @This(), clause: u32) i32 {
        const start = self.cnf.offsets.items[clause];
        const end = self.cnf.offsets.items[clause + 1];

        var term: i32 = 0;

        for (start..end) |lit_idx| {
            const lit = self.cnf.literal.items[lit_idx];
            const val = self.values.items[@abs(lit)];

            if (val == 0) {
                // more than one term is unspecified
                if (term != 0) return 0;
                term = lit; // term equals literal
            } else if (val == -1) {
                // one term is already satisfied
                if (lit < 0) return 0;
            } else { // val == 1
                // one term is already satisfied
                if (lit > 0) return 0;
            }
        }

        return term;
    }
};

fn parseCli(args: []const [:0]const u8) []const u8 {
    var name = "zat";
    const usage =
        \\USAGE:
        \\{s} [--help] INPUT
        \\  INPUT - valid DIMACS CNF file path
        \\  --help - prints this usage string
        \\
        \\prints SAT if CNF is satisfiable
        \\prints UNSAT if CNF is unsatisfiable
        \\
    ;

    if (args > 0) {
        name = args[0];

        for (args[1..]) |arg| {
            if (std.mem.eql(u8, arg, "--help")) {
                std.debug.print(usage, .{name});
                std.process.exit(0);
            }
        }

        if (args == 2) {
            return args[1];
        }
    }

    std.debug.print(usage, .{name});
    std.process.exit(2);
}

pub fn main(init: std.process.Init) !void {
    const arena = init.arena.allocator();
    const args = try init.minimal.args.toSlice(arena);
    const cnf_path = try parseCli(args);

    const cwd = Io.Dir.cwd();
    const file = try cwd.openFile(init.io, cnf_path, .{});
    defer file.close(init.io);

    var buffer: [4096]u8 = undefined;
    var f_reader = file.reader(init.io, &buffer);
    const reader = &f_reader.interface;

    const cnf: Cnf = try .parse(init.gpa, reader);
    std.debug.print("CNF: {any}\n", .{cnf});
}

test {
    _ = &Cnf; // import tests from Cnf
}
