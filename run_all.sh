#!/usr/bin/env bash
set -euo pipefail

SOLVER="./zig-out/bin/zat"
CNF_DIR="./test_cnf"
TMPFILE=$(mktemp)
PARALLEL=32
TIMEOUT=60

# Find all CNF files
find "$CNF_DIR" -type f \( -name "*.cnf" -o -name "*.dimacs" \) | sort > "$TMPFILE"

run_one() {
    timeout "${TIMEOUT}s" "$SOLVER" "$1"
    # "$SOLVER" "$1"
}

export -f run_one
export SOLVER TIMEOUT

xargs -a "$TMPFILE" -P "$PARALLEL" -I{} bash -c 'run_one "$@"' _ {}
rm -f "$TMPFILE"
