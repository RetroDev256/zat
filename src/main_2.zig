const std = @import("std");

const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const END = -9;
const UNSAT = 0;
const SAT = 1;
const MARK = 2;
const IMPLIED = 6;

const Solver = struct {
    /// number of variables in the problem
    num_vars: i32,
    /// number of clauses in the problem
    num_clauses: i32,

    /// (initial?) maximum memory usage for solver
    mem_max: i32,
    /// number of integers allocated in the DB
    mem_used: i32,

    // (initial?) maximum learned clause count
    max_lemmas: i32,
    /// number of learned/redundant clauses
    num_lemmas: i32,

    /// number of conflicts used to update scores
    num_conflicts: i32,
    /// fast moving average (???)
    fast: i32,
    /// slow moving average (???)
    slow: i32,
    /// database of variables
    db: []i32,

    /// full assignment of the boolean variables (initially false)
    model: []i32,
    /// next variable in the heuristic order
    next: []i32,
    /// previous variable in the heuristic order
    prev: []i32,
    /// buffer to store a temporary clause
    buffer: []i32,
    /// array of clauses
    reason: []i32,
    /// stack of falsified literals
    false_stack: []i32,
    /// points inside false_stack at first decision (unforced literal)
    forced: [*]i32,
    /// points inside false_stack at first unprocessed literal
    processed: [*]i32,
    /// points inside false_stack at last unprocessed literal
    assigned: [*]i32,
    /// labels for variables, non-zero means false
    falsey: []i32,
    /// offset of the first watched clause
    first: []i32,
    /// head of the double-linked list
    head: i32,

    mem_fixed: i32,
    res: i32,

    pub fn init(self: *@This(), gpa: Allocator, num_vars: i32, num_clauses: i32) !void {
        // There must be at least one variable
        if (num_vars == 0) return error.ZeroVariables;

        self.num_vars = num_vars;
        self.num_clauses = num_clauses;
        self.mem_max = 1 << 30;
        self.mem_used = 0;
        self.num_lemmas = 0;
        self.num_conflicts = 0;
        self.max_lemmas = 2000;
        self.fast = 1 << 24;
        self.slow = 1 << 24;

        self.db = try gpa.alloc(i32, @as(usize, @intCast(self.mem_max)));
        errdefer gpa.free(self.db);

        self.model = try self.getMemory(num_vars + 1);
        self.next = try self.getMemory(num_vars + 1);
        self.prev = try self.getMemory(num_vars + 1);
        self.buffer = try self.getMemory(num_vars);
        self.reason = try self.getMemory(num_vars + 1);

        self.false_stack = try self.getMemory(num_vars + 1);
        self.forced = self.false_stack.ptr;
        self.processed = self.false_stack.ptr;
        self.assigned = self.false_stack.ptr;

        self.falsey = try self.getMemory(2 * num_vars + 1);
        self.falsey = self.falsey[@as(usize, @intCast(num_vars))..];

        self.first = try self.getMemory(2 * num_vars + 1);
        self.first = self.first[@as(usize, @intCast(num_vars))..];

        // Make sure there is a 0 before the clauses are loaded (???)
        self.db[@as(usize, @intCast(self.mem_used))] = 0;
        self.mem_used += 1;

        // Initialize the main data structures:
        for (1..@as(usize, @intCast(num_clauses)) + 1) |i_usize| {
            const i = @as(i32, @intCast(i_usize));
            self.prev[@as(usize, @intCast(i))] = i - 1;
            self.next[@as(usize, @intCast(i - 1))] = i; // the double-linked list for variable-move-to-front,

            self.model[@as(usize, @intCast(i))] = 0;
            if (i >= 0) {
                self.falsey[@intCast(i)] = 0;
            } else {
                (self.falsey.ptr - @as(usize, @intCast(-i)))[0] = 0;
            }
            self.falsey[@as(usize, @intCast(i))] = 0; // the model (phase-saving), the false array,

            self.first[@as(usize, @intCast(i))] = END;
            if (i >= 0) { // and first (watch pointers).
                self.first[@intCast(i)] = END;
            } else {
                (self.first.ptr - @as(usize, @intCast(-i)))[0] = END;
            }
        }

        // Initialize the head of the double-linked list
        self.head = num_vars;
    }

    // Allocate memory of size mem_size
    fn getMemory(self: *@This(), mem_size: i32) ![]i32 {
        if (self.mem_used + mem_size > self.mem_max) {
            return error.OutOfMemory;
        }

        // Compute a pointer to the new memory location
        const store: []i32 = self.db[@as(usize, @intCast(self.mem_used))..];
        // Update the size of the used memory
        self.mem_used += mem_size;
        // Return the pointer
        return store;
    }

    /// Unasign the literal
    fn unassign(self: *@This(), literal: i32) void {
        self.falsey[@as(usize, @intCast(literal))] = 0;
    }

    /// Perform a restart (unassign all variables)
    fn restart(self: *@This()) void {
        while (@intFromPtr(self.assigned) > @intFromPtr(self.forced)) {
            // Remove all unforced false literals from false_stack
            self.assigned -= 1;
            self.unassign(self.assigned[0]);
        }
        // Reset the processed pointer
        self.processed = self.forced;
    }

    /// Mark the literal as true in the model
    fn assign(self: *@This(), reason: []const i32, forced: i32) void {
        const literal = reason[0]; // Let lit be the first literal in the reason
        // Mark lit as true and IMPLIED if forced
        index(self.falsey.ptr, literal).* = if (forced != 0) IMPLIED else 1;
        // Push it on the assignment stack
        self.assigned += 1;
        self.assigned[0] = -literal;
        // Set the reason clause of literal
        self.reason[@as(usize, @intCast(@abs(literal)))] = @as(i32, @intCast(1 + (@intFromPtr(reason.ptr) - @intFromPtr(self.db.ptr)) / @sizeOf(i32)));
        self.model[@as(usize, @intCast(@abs(literal)))] = @intFromBool(literal > 0);
    }

    // Add a watch pointer to a clause containing lit
    fn addWatch(self: *@This(), literal: i32, mem: i32) void {
        // By updating the database and the pointers
        self.db[@as(usize, @intCast(mem))] = self.first[@as(usize, @intCast(literal))];
        self.first[@as(usize, @intCast(literal))] = mem;
    }

    fn addClause(self: *@This(), in: []const i32, size: usize, irr: i32) ![*]i32 { // Adds a clause stored in *in of size size
        var i: usize = 0;
        const used = self.mem_used; // Store a pointer to the beginning of the clause
        const clause_mem = try self.getMemory(@as(i32, @intCast(size)) + 3);
        const clause = clause_mem[2..]; // Allocate memory for the clause in the database
        if (size > 1) {
            self.addWatch(in[0], used); // If the clause is not unit, then add
            self.addWatch(in[1], used + 1);
        } // Two watch pointers to the datastructure
        while (i < size) : (i += 1) {
            clause[i] = in[i];
        }
        clause[i] = 0; // Copy the clause from the buffer to the database
        if (irr != 0) {
            self.mem_fixed = self.mem_used;
        } else {
            self.num_lemmas += 1; // Update the statistics
        }
        return clause.ptr;
    } // Return the pointer to the clause in the database

    fn reduceDB(self: *@This(), k: i32) !void { // Removes "less useful" lemmas from DB
        while (self.num_lemmas > self.max_lemmas) {
            self.max_lemmas += 300; // Allow more lemmas in the future
        }
        self.num_lemmas = 0; // Reset the number of lemmas

        var i: i32 = -self.num_vars;
        while (i <= self.num_vars) : (i += 1) { // Loop over the variables
            if (i == 0) continue;
            var watch: [*]i32 = @ptrCast(index(self.first.ptr, i)); // Get the pointer to the first watched clause
            while (watch[0] != END) { // As long as there are watched clauses
                if (watch[0] < self.mem_fixed) {
                    watch = @ptrCast(index(self.db.ptr, watch[0])); // Remove the watch if it points to a lemma
                } else {
                    watch[0] = index(self.db.ptr, watch[0]).*;
                }
            }
        } // Otherwise (meaning an input clause) go to next watch

        const old_used = self.mem_used;
        self.mem_used = self.mem_fixed; // Virtually remove all lemmas
        i = self.mem_fixed + 2;
        while (i < old_used) : (i += 3) { // While the old memory contains lemmas
            var count: i32 = 0;
            const head = i; // Get the lemma to which the head is pointing
            while (self.db[@as(usize, @intCast(i))] != 0) {
                const lit = self.db[@as(usize, @intCast(i))]; // Count the number of literals
                i += 1;
                if (@intFromBool(lit > 0) == self.model[@as(usize, @intCast(@abs(lit)))]) {
                    count += 1;
                }
            } // That are satisfied by the current model
            if (count < k) {
                _ = try self.addClause(self.db[@as(usize, @intCast(head))..], @as(usize, @intCast(i - head)), 0);
            }
        }
    } // If the latter is smaller than k, add it back

    fn bump(self: *@This(), lit: i32) void { // Move the variable to the front of the decision list
        if (index(self.falsey.ptr, lit).* != IMPLIED) {
            index(self.falsey.ptr, lit).* = MARK; // MARK the literal as involved if not a top-level unit
            const var_idx = @abs(lit);
            if (var_idx != self.head) { // In case var is not already the head of the list
                self.prev[@as(usize, @intCast(self.next[@as(usize, @intCast(var_idx))]))] = self.prev[@as(usize, @intCast(var_idx))]; // Update the prev link, and
                self.next[@as(usize, @intCast(self.prev[@as(usize, @intCast(var_idx))]))] = self.next[@as(usize, @intCast(var_idx))]; // Update the next link, and
                self.next[@as(usize, @intCast(self.head))] = @as(i32, @intCast(var_idx)); // Add a next link to the head, and
                self.prev[@as(usize, @intCast(var_idx))] = self.head;
                self.head = @as(i32, @intCast(var_idx));
            }
        }
    } // Make var the new head

    fn implied(self: *@This(), lit: i32) i32 { // Check if lit(eral) is implied by MARK literals
        if (index(self.falsey.ptr, lit).* > MARK) {
            return index(self.falsey.ptr, lit).* & MARK; // If checked before return old result
        }
        if (self.reason[@as(usize, @intCast(@abs(lit)))] == 0) {
            return 0; // In case lit is a decision, it is not implied
        }
        var p: [*]i32 = self.db.ptr + @as(usize, @intCast(self.reason[@as(usize, @intCast(@abs(lit)))])) - 1; // Get the reason of lit(eral)
        p += 1;
        while (p[0] != 0) : (p += 1) { // While there are literals in the reason
            if ((index(self.falsey.ptr, p[0]).* ^ MARK) != 0 and self.implied(p[0]) == 0) { // Recursively check if non-MARK literals are implied
                index(self.falsey.ptr, lit).* = IMPLIED - 1;
                return 0;
            }
        } // Mark and return not implied (denoted by IMPLIED - 1)
        index(self.falsey.ptr, lit).* = IMPLIED;
        return 1;
    } // Mark and return that the literal is implied

    fn analyze(self: *@This(), clause_ptr: [*]i32) ![*]i32 { // Compute a resolvent from falsified clause
        var clause = clause_ptr;
        self.res += 1;
        self.num_conflicts += 1; // Bump restarts and update the statistic
        while (clause[0] != 0) {
            self.bump(clause[0]); // MARK all literals in the falsified clause
            clause += 1;
        }

        self.assigned -= 1;
        build: while (self.reason[@as(usize, @intCast(@abs(self.assigned[0])))] != 0) { // Loop on variables on falseStack until the last decision
            if (index(self.falsey.ptr, self.assigned[0]).* == MARK) { // If the tail of the stack is MARK
                var check = self.assigned; // Pointer to check if first-UIP is reached
                check -= 1;
                while (index(self.falsey.ptr, check[0]).* != MARK) : (check -= 1) { // Check for a MARK literal before decision
                    if (self.reason[@as(usize, @intCast(@abs(check[0])))] == 0) {
                        break :build; // Otherwise it is the first-UIP so break
                    }
                }
                clause = self.db.ptr + @as(usize, @intCast(self.reason[@as(usize, @intCast(@abs(self.assigned[0])))])); // Get the reason and ignore first literal
                while (clause[0] != 0) : (clause += 1) {
                    self.bump(clause[0]);
                }
            } // MARK all literals in reason
            self.unassign(self.assigned[0]);
            self.assigned -= 1;
        } // Unassign the tail of the stack

        // build:;
        var size: usize = 0;
        var lbd: i32 = 0;
        var flag: i32 = 0; // Build conflict clause; Empty the clause buffer
        self.processed = self.assigned;
        var p: [*]i32 = self.processed; // Loop from tail to front
        while (@intFromPtr(p) >= @intFromPtr(self.forced)) { // Only literals on the stack can be MARKed
            if (index(self.falsey.ptr, p[0]).* == MARK and self.implied(p[0]) == 0) { // If MARKed and not implied
                self.buffer[size] = p[0];
                size += 1;
                flag = 1;
            } // Add literal to conflict clause buffer
            if (self.reason[@as(usize, @intCast(@abs(p[0])))] == 0) {
                lbd += flag;
                flag = 0; // Increase LBD for a decision with a true flag
                if (size == 1) {
                    self.processed = p;
                }
            } // And update the processed pointer
            index(self.falsey.ptr, p[0]).* = 1;
            p -= 1;
        } // Reset the MARK flag for all variables on the stack

        self.fast -= self.fast >> 5;
        self.fast += lbd << 15; // Update the fast moving average
        self.slow -= self.slow >> 15;
        self.slow += lbd << 5; // Update the slow moving average

        while (@intFromPtr(self.assigned) > @intFromPtr(self.processed)) { // Loop over all unprocessed literals
            self.unassign(self.assigned[0]); // Unassign all lits between tail & head
            self.assigned -= 1;
        }
        self.unassign(self.assigned[0]); // Assigned now equal to processed
        self.buffer[size] = 0; // Terminate the buffer (and potentially print clause)
        return try self.addClause(self.buffer[0..size], size, 0);
    } // Add new conflict clause to redundant DB

    fn propagate(self: *@This()) !i32 { // Performs unit propagation
        var forced: i32 = self.reason[@as(usize, @intCast(@abs(self.processed[0])))]; // Initialize forced flag
        while (@intFromPtr(self.processed) < @intFromPtr(self.assigned)) { // While unprocessed false literals
            const lit = self.processed[0]; // Get first unprocessed literal
            self.processed += 1;
            var watch: [*]i32 = @ptrCast(index(self.first.ptr, lit)); // Obtain the first watch pointer
            while (watch[0] != END) { // While there are watched clauses (watched by lit)
                var unit: i32 = 1; // Let's assume that the clause is unit
                var clause = self.db.ptr + @as(usize, @intCast(watch[0])) + 1; // Get the clause from DB
                if ((clause - 2)[0] == 0) {
                    clause += 1; // Set the pointer to the first literal in the clause
                }
                if (clause[0] == lit) {
                    clause[0] = clause[1]; // Ensure that the other watched literal is in front
                }
                var i: usize = 2;
                while (unit != 0 and clause[i] != 0) : (i += 1) { // Scan the non-watched literals
                    if (index(self.falsey.ptr, clause[i]).* == 0) { // When clause[i] is not false, it is either true or unset
                        clause[1] = clause[i];
                        clause[i] = lit; // Swap literals
                        const store = watch[0];
                        unit = 0; // Store the old watch
                        watch[0] = self.db[@as(usize, @intCast(watch[0]))]; // Remove the watch from the list of lit
                        self.addWatch(clause[1], store);
                    } // Add the watch to the list of clause[1]
                }
                if (unit != 0) { // If the clause is indeed unit
                    clause[1] = lit;
                    watch = self.db.ptr + @as(usize, @intCast(watch[0])); // Place lit at clause[1] and update next watch
                    if (index(self.falsey.ptr, clause[0]).* != 0) {
                        continue; // If the other watched literal is satisfied continue
                    }
                    if (index(self.falsey.ptr, clause[0]).* == 0) { // If the other watched literal is falsified,
                        self.assign(clause[0..1], forced);
                    } // A unit clause is found, and the reason is set
                    else {
                        if (forced != 0) {
                            return UNSAT; // Found a root level conflict -> UNSAT
                        }
                        const lemma = try self.analyze(clause); // Analyze the conflict return a conflict clause
                        if (lemma[1] == 0) {
                            forced = 1; // In case a unit clause is found, set forced flag
                        }
                        self.assign(lemma[0..2], forced); // Needs slice for assign
                        break;
                    }
                }
            }
        } // Assign the conflict clause as a unit
        if (forced != 0) {
            self.forced = self.processed; // Set S->forced if applicable
        }
        return SAT;
    } // Finally, no conflict was found

    pub fn solve(self: *@This()) !i32 { // Determine satisfiability
        var decision = self.head;
        self.res = 0; // Initialize the solver
        while (true) { // Main solve loop
            const old_nLemmas = self.num_lemmas; // Store nLemmas to see whether propagate adds lemmas
            if (try self.propagate() == UNSAT) {
                return UNSAT; // Propagation returns UNSAT for a root level conflict
            }

            if (self.num_lemmas > old_nLemmas) { // If the last decision caused a conflict
                decision = self.head; // Reset the decision heuristic to head
                if (self.fast > @divTrunc(self.slow, 100) * 125) { // If fast average is substantially larger than slow average
                    //        printf("c restarting after %i conflicts (%i %i) %i\n", S->res, S->fast, S->slow, S->nLemmas > S->maxLemmas);
                    self.res = 0;
                    self.fast = @divTrunc(self.slow, 100) * 125;
                    self.restart(); // Restart and update the averages
                    if (self.num_lemmas > self.max_lemmas) {
                        try self.reduceDB(6);
                    }
                }
            } // Reduce the DB when it contains too many lemmas

            while (index(self.falsey.ptr, decision).* != 0 or index(self.falsey.ptr, -decision).* != 0) { // As long as the temporay decision is assigned
                decision = self.prev[@as(usize, @intCast(decision))];
            } // Replace it with the next variable in the decision list
            if (decision == 0) {
                return SAT; // If the end of the list is reached, then a solution is found
            }
            decision = if (self.model[@as(usize, @intCast(decision))] != 0) decision else -decision; // Otherwise, assign the decision variable based on the model
            index(self.falsey.ptr, -decision).* = 1; // Assign the decision literal to true (change to IMPLIED-1?)
            self.assigned[0] = -decision; // And push it on the assigned stack
            self.assigned += 1;
            decision = @intCast(@abs(decision));
            self.reason[@as(usize, @intCast(decision))] = 0;
        }
    } // Decisions have no reason clauses

    fn read_until_new_line(self: *@This(), input: anytype) !void {
        _ = self;
        var ch: u8 = 0;
        while (true) {
            ch = input.takeByte() catch |err| {
                if (err == error.EndOfStream) {
                    std.debug.print("parse error: unexpected EOF\n", .{});
                    std.process.exit(1);
                }
                return err;
            };
            if (ch == '\n') break;
        }
    }

    pub fn parse(self: *@This(), io: std.Io, filename: []const u8) !i32 { // Parse the formula and initialize
        var tmp: u8 = 0;
        var file = try std.Io.Dir.cwd().openFile(io, filename, .{});
        defer file.close(io);

        var buffer: [1024]u8 = undefined;
        var file_reader = file.reader(io, &buffer);
        const input = &file_reader.interface;

        while (true) {
            tmp = try input.takeByte();
            if (tmp == 'c') {
                try self.read_until_new_line(input);
            } else {
                break;
            }
        }

        const full_line = try input.takeDelimiter('\n');

        var it = std.mem.tokenizeAny(u8, full_line.?, " \r\t");
        _ = it.next();
        _ = it.next();
        const nVars = try std.fmt.parseInt(i32, it.next().?, 10); // Find the first non-comment line

        // ERROR: ATTEMPT TO USE NULL VALUE!!!!!!!!!!!!!!!!!!!!!!!!!
        const nClauses = try std.fmt.parseInt(i32, it.next().?, 10);

        try self.init(std.heap.page_allocator, nVars, nClauses); // Allocate the main datastructures
        self.mem_fixed = 0;
        self.res = 0;

        var nZeros = self.num_clauses;
        var size: usize = 0; // Initialize the number of clauses to read

        while (nZeros > 0) { // While there are clauses in the file
            const ch = input.takeByte() catch |err| {
                if (err == error.EndOfStream) break;
                return err;
            };

            if (ch == ' ' or ch == '\n' or ch == '\r') {
                continue;
            }
            if (ch == 'c') {
                try self.read_until_new_line(input);
                continue;
            }

            var lit_buf: [32]u8 = undefined;
            lit_buf[0] = ch;
            var lit_len: usize = 1;
            while (true) {
                const next_ch = input.takeByte() catch |err| {
                    if (err == error.EndOfStream) break;
                    return err;
                };
                if (next_ch == ' ' or next_ch == '\n' or next_ch == '\r') {
                    break;
                }
                lit_buf[lit_len] = next_ch;
                lit_len += 1;
            }

            const lit = try std.fmt.parseInt(i32, lit_buf[0..lit_len], 10); // Read a literal.

            if (lit == 0) { // If reaching the end of the clause
                const clause = try self.addClause(self.buffer[0..size], size, 1); // Then add the clause to data_base
                if (size == 0 or ((size == 1) and index(self.falsey.ptr, clause[0]).* != 0)) { // Check for empty clause or conflicting unit
                    return UNSAT; // If either is found return UNSAT
                }
                if ((size == 1) and index(self.falsey.ptr, clause[0]).* == 0) { // Check for a new unit
                    self.assign(clause[0..1], 1);
                } // Directly assign new units (forced = 1)
                size = 0;
                nZeros -= 1;
            } // Reset buffer
            else {
                self.buffer[size] = lit;
                size += 1;
            }
        } // Add literal to buffer
        return SAT;
    } // Return that no conflict was observed

};

fn index(ptr: [*]i32, idx: i32) *i32 {
    if (idx >= 0) {
        return &ptr[@intCast(idx)];
    } else {
        return @ptrCast(ptr - @as(usize, @intCast(-idx)));
    }
}

/// procedure for a standalone solver
pub fn main(init: std.process.Init) !void {
    var solver: Solver = undefined;

    const arena = init.arena.allocator();
    const args = try init.minimal.args.toSlice(arena);

    if (args.len <= 1) {
        std.debug.print("no input file provided\n", .{});
        return;
    } else if (try solver.parse(init.io, args[1]) == UNSAT) {
        std.debug.print("s UNSAT\n", .{});
    } else if (try solver.solve() == UNSAT) {
        std.debug.print("s UNSAT\n", .{});
    } else {
        std.debug.print("s SAT\n", .{});
    }

    std.debug.print("c statistics of {s}:\n", .{args[1]});
    std.debug.print("c - memory used: {}:\n", .{solver.mem_used});
    std.debug.print("c - conflicts: {}\n", .{solver.num_conflicts});
    std.debug.print("c - max lemmas: {}\n", .{solver.max_lemmas});
}
