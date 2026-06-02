const std = @import("std");
// const Bcp = @import("Bcp.zig");
const Cnf = @import("Cnf.zig");
const Dp = @import("Dp.zig");
// const Dpll = @import("Dpll.zig");
// const Preprocess = @import("Preprocess.zig");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const Io = std.Io;

// Things to consider - variable assignment priority
// - variables that occur most often first?
// - variables in smaller clauses come first?
// - common variables in small clauses come first?
// - variables that occur least often first?

fn parseCli(args: []const [:0]const u8) ![]const u8 {
    var name: []const u8 = "zat";
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

    if (args.len > 0) {
        name = args[0];

        for (args[1..]) |arg| {
            if (std.mem.eql(u8, arg, "--help")) {
                std.debug.print(usage, .{name});
                std.process.exit(0);
            }
        }

        if (args.len == 2) {
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

    std.debug.print("c Parsing contents of {s}...\n", .{cnf_path});
    var cnf: Cnf = try .parse(init.gpa, reader);
    defer cnf.deinit(init.gpa);

    std.debug.print("c {} clauses loaded...\n", .{cnf.clauses.items.len});
    std.debug.print("c {} variables loaded...\n", .{cnf.var_count});

    // const before = cnf.clauses.items.len;
    // try cnf.subsume(init.gpa);
    // const removed = before - cnf.clauses.items.len;
    // std.debug.print("c {} clauses subsumed...\n", .{removed});

    std.debug.print("c Initializing solver...\n", .{});
    var solver: Dp = .init(&cnf);
    std.debug.print("c Running DP algorithm...\n", .{});
    const sat = try solver.solve(init.gpa);

    std.debug.print(
        "s {s}SATISFIABLE\n\n",
        .{if (sat) "" else "UN"},
    );
}

test {
    // _ = &Bcp; // import tests from Bcp
    _ = &Cnf; // import tests from Cnf
    // _ = &Dpll; // import tests from Dpll
    // _ = &Preprocess; // import tests from Preprocess
}
