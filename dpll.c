/*
 * Classical DPLL SAT Solver (From First Principles)
 * - No global variables
 * - Index-based loops only
 * - No pointer casting
 * - DRY principles applied
 * - String-based test harness for easy extension
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CNF_HEADER "p cnf "

/* ─────────────────────────────────────────────────────────────
 * Data Structures
 * ───────────────────────────────────────────────────────────── */

typedef struct {
    int    num_vars;
    int    num_clauses;
    int   *offsets;  /* size: num_clauses + 1 */
    int   *literals; /* flat array of literals (0s stripped during parse) */
} CNF;

typedef struct {
    const CNF *cnf;
    int        num_vars;
    int       *assign;   /* 1-based: 0=unassigned, 1=true, -1=false */
    int       *pure_vars;/* buffer for pure literal detection */
    int       *pure_vals;/* buffer for pure literal values */
    int       *pos_cnt;  /* occurrence count per positive literal */
    int       *neg_cnt;  /* occurrence count per negative literal */
} Solver;

/* ─────────────────────────────────────────────────────────────
 * Memory Management
 * ───────────────────────────────────────────────────────────── */

static void solver_init(Solver *s, CNF *c) {
    s->num_vars = c->num_vars;
    s->cnf      = c;
    s->assign   = (int *)calloc(c->num_vars + 1, sizeof(int));
    s->pure_vars = (int *)calloc(c->num_vars + 1, sizeof(int));
    s->pure_vals = (int *)calloc(c->num_vars + 1, sizeof(int));
    s->pos_cnt = (int *)calloc(c->num_vars + 1, sizeof(int));
    s->neg_cnt = (int *)calloc(c->num_vars + 1, sizeof(int));
}

static void solver_free(Solver *s) {
    free(s->assign);
    free(s->pure_vars);
    free(s->pure_vals);
    free(s->pos_cnt);
    free(s->neg_cnt);
}

static void cnf_free(CNF *c) {
    free(c->offsets);
    free(c->literals);
}

/* ─────────────────────────────────────────────────────────────
 * CNF from String Parser
 * ───────────────────────────────────────────────────────────── */

static CNF cnf_from_string(const char *str) {
    CNF c = {0};
    int num_vars = 0, num_clauses = 0;
    int total_lits = 0;
    const char *p = str;

    /* First pass: count variables, clauses, and total literals */
    while (*p) {
        while (*p == ' ' || *p == '\n' || *p == '\t') p++;
        if (*p == '\0') break;
        if (*p == 'c' || *p == '#') {
            while (*p && *p != '\n') p++;
            continue;
        }
        if (strncmp(p, CNF_HEADER, strlen(CNF_HEADER)) == 0) {
            int v = 0;
            (void)sscanf(p, "p cnf %d", &v);
            if (v > num_vars) num_vars = v;
            while (*p && *p != '\n') p++;
            continue;
        }
        num_clauses++;
        long val;
        char *end;
        while (*p) {
            val = strtol(p, &end, 10);
            p = end;
            while (*p == ' ' || *p == '\n' || *p == '\t') p++;
            if (val == 0) break;
            long abs_val = (val < 0) ? -val : val;
            if (abs_val > num_vars) num_vars = (int)abs_val;
            total_lits++;
        }
    }

    c.num_vars = num_vars;
    c.num_clauses = num_clauses;
    c.offsets  = (int *)calloc(num_clauses + 1, sizeof(int));
    c.literals = (int *)calloc(total_lits, sizeof(int));

    /* Second pass: fill arrays */
    p = str;
    int lit_idx = 0;
    int clause_idx = 0;
    c.offsets[0] = 0;
    while (*p) {
        while (*p == ' ' || *p == '\n' || *p == '\t') p++;
        if (*p == '\0') break;
        if (*p == 'c' || *p == '#') {
            while (*p && *p != '\n') p++;
            continue;
        }
        if (strncmp(p, CNF_HEADER, strlen(CNF_HEADER)) == 0) {
            int v;
            (void)sscanf(p, "p cnf %d", &v);
            while (*p && *p != '\n') p++;
            continue;
        }
        long val;
        char *end;
        while (*p) {
            val = strtol(p, &end, 10);
            p = end;
            while (*p == ' ' || *p == '\n' || *p == '\t') p++;
            if (val == 0) {
                c.offsets[++clause_idx] = lit_idx;
                break;
            }
            c.literals[lit_idx++] = (int)val;
        }
    }
    return c;
}

/* ─────────────────────────────────────────────────────────────
 * Core DPLL Helpers
 * ───────────────────────────────────────────────────────────── */

static int clause_satisfied(const int *cl, int start, int end, const int *assign) {
    for (int i = start; i < end; i++) {
        int lit = cl[i];
        if (assign[abs(lit)] == (lit > 0 ? 1 : -1)) return 1;
    }
    return 0;
}

static int clause_conflict(const int *cl, int start, int end, const int *assign) {
    for (int i = start; i < end; i++) {
        int lit = cl[i];
        int val = assign[abs(lit)];
        if (val == 0) return 0; // unresolved, not conflict
        if (val == (lit > 0 ? 1 : -1)) return 0; // satisfied
    }
    return 1; // all assigned false
}

static int find_unit(const int *cl, int start, int end, const int *assign) {
    int found = 0;
    int unit = 0;
    for (int i = start; i < end; i++) {
        int lit = cl[i];
        if (assign[abs(lit)] == 0) {
            if (found) return 0;
            found = 1;
            unit = lit;
        }
    }
    return found ? unit : 0;
}

/* ─────────────────────────────────────────────────────────────
 * Propagation & Pure Literals
 * ───────────────────────────────────────────────────────────── */

static int propagate_units(Solver *s) {
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int c = 0; c < s->cnf->num_clauses; c++) {
            int start = s->cnf->offsets[c];
            int end   = s->cnf->offsets[c + 1];
            if (clause_conflict(s->cnf->literals, start, end, s->assign)) return 0;
            if (!clause_satisfied(s->cnf->literals, start, end, s->assign)) {
                int unit = find_unit(s->cnf->literals, start, end, s->assign);
                if (unit != 0) {
                    s->assign[abs(unit)] = (unit > 0 ? 1 : -1);
                    changed = 1;
                }
            }
        }
    }
    return 1;
}

static void apply_pure_literals(Solver *s) {
    int *pos = s->pos_cnt;
    int *neg = s->neg_cnt;
    memset(pos, 0, (s->cnf->num_vars + 1) * sizeof(int));
    memset(neg, 0, (s->cnf->num_vars + 1) * sizeof(int));

    for (int c = 0; c < s->cnf->num_clauses; c++) {
        int start = s->cnf->offsets[c];
        int end   = s->cnf->offsets[c + 1];
        if (clause_satisfied(s->cnf->literals, start, end, s->assign)) continue;

        for (int i = start; i < end; i++) {
            int lit = s->cnf->literals[i];
            if (s->assign[abs(lit)] == 0) {
                if (lit > 0) pos[abs(lit)]++;
                else         neg[abs(lit)]++;
            }
        }
    }

    int pcount = 0;
    for (int v = 1; v <= s->cnf->num_vars; v++) {
        if (s->assign[v] != 0) continue;
        if (pos[v] > 0 && neg[v] == 0) {
            s->pure_vars[pcount] = v;
            s->pure_vals[pcount] =  1;
            pcount++;
        } else if (neg[v] > 0 && pos[v] == 0) {
            s->pure_vars[pcount] = v;
            s->pure_vals[pcount] = -1;
            pcount++;
        }
    }
    for (int i = 0; i < pcount; i++) {
        s->assign[s->pure_vars[i]] = s->pure_vals[i];
    }
}

/* ─────────────────────────────────────────────────────────────
 * Recursive DPLL Core
 * ───────────────────────────────────────────────────────────── */

static int dpll_solve(Solver *s) {
    int all_satisfied = 1;
    for (int c = 0; c < s->cnf->num_clauses; c++) {
        if (!clause_satisfied(s->cnf->literals, s->cnf->offsets[c], s->cnf->offsets[c+1], s->assign)) {
            all_satisfied = 0;
            break;
        }
        if (clause_conflict(s->cnf->literals, s->cnf->offsets[c], s->cnf->offsets[c+1], s->assign)) {
            return 0;
        }
    }
    if (all_satisfied) return 1;

    apply_pure_literals(s);
    if (!propagate_units(s)) return 0;

    for (int c = 0; c < s->cnf->num_clauses; c++) {
        if (clause_conflict(s->cnf->literals, s->cnf->offsets[c], s->cnf->offsets[c+1], s->assign)) {
            return 0;
        }
    }
    all_satisfied = 1;
    for (int c = 0; c < s->cnf->num_clauses; c++) {
        if (!clause_satisfied(s->cnf->literals, s->cnf->offsets[c], s->cnf->offsets[c+1], s->assign)) {
            all_satisfied = 0;
            break;
        }
    }
    if (all_satisfied) return 1;

    int var = 0;
    for (int v = 1; v <= s->cnf->num_vars; v++) {
        if (s->assign[v] == 0) { var = v; break; }
    }
    if (var == 0) return 0;

    s->assign[var] = 1;
    if (dpll_solve(s)) return 1;
    s->assign[var] = 0;

    s->assign[var] = -1;
    if (dpll_solve(s)) return 1;
    s->assign[var] = 0;

    return 0;
}

/* ─────────────────────────────────────────────────────────────
 * Test Harness
 * ───────────────────────────────────────────────────────────── */

static int test_cnf_string(const char *name, const char *cnf_str, int expected_sat) {
    CNF c = cnf_from_string(cnf_str);
    Solver s;
    solver_init(&s, &c);
    int result = dpll_solve(&s);
    solver_free(&s);
    cnf_free(&c);
    
    printf("%-30s: %s (expected %s) %s\n",
           name,
           result == 1 ? "SAT" : (result == 0 ? "UNSAT" : "ERROR"),
           expected_sat == 1 ? "SAT" : "UNSAT",
           result == expected_sat ? "PASS" : "FAIL");
    return result == expected_sat ? 0 : 1;
}

/* ─────────────────────────────────────────────────────────────
 * Individual Test Functions
 * ───────────────────────────────────────────────────────────── */

static void test_unit_propagation(void) {
    test_cnf_string("Unit Propagation",
        "1 0 -1 2 0", 1);
}

static void test_pure_literal(void) {
    test_cnf_string("Pure Literal",
        "1 2 0 1 -2 3 0", 1);
}

static void test_chain_implication_sat(void) {
    test_cnf_string("Chain Implication (SAT)",
        "1 2 0 -1 3 0 -2 3 0 -3 4 0 -4 1 0", 1);
}

static void test_chain_implication_unsat(void) {
    test_cnf_string("Chain Implication (UNSAT)",
        "1 0 -1 2 0 -1 -2 0 -2 3 0 -2 -3 0 -3 4 0 -3 -4 0 -4 0", 0);
}

static void test_empty_formula(void) {
    test_cnf_string("Empty Formula", "", 1);
}

static void test_single_clause_unsat(void) {
    test_cnf_string("Single Clause UNSAT", "-1\n", 0);
}

static void run_all_tests(void) {
    printf("Running DPLL test suite...\n");
    printf("─%s─\n", "----------------------------------------------");
    test_unit_propagation();
    test_pure_literal();
    test_chain_implication_sat();
    test_chain_implication_unsat();
    test_empty_formula();
    test_single_clause_unsat();
    printf("─%s─\n", "----------------------------------------------");
}

int main(void) {
    run_all_tests();

    FILE* f = fopen("out.cnf", "rb");
    if (!f) return 1;

    fseek(f, 0, SEEK_END);
    long len = ftell(f);
    rewind(f);

    char* buf = malloc(len + 1);
    if (!buf) {
        fclose(f);
        return 2;
    }

    int read = fread(buf, 1, len, f);
    buf[len] = 0;
    (void)read;

    fclose(f);

    CNF c = cnf_from_string(buf);
    Solver s;
    solver_init(&s, &c);
    int result = dpll_solve(&s);
    solver_free(&s);
    cnf_free(&c);

    if (result) {
        printf("SAT\n");
    } else {
        printf("UNSAT\n");
    }
    
    return EXIT_SUCCESS;
}

