#!/bin/bash
# Promote every staging file that has gone quiet, commit and push, forever.
#   scripts/promote-loop.sh <corpus checkout> [library] [interval s] [quiescent s]
# The banking hook only stages records as they arrive; this loop turns the
# files it has finished with into trusted modules, one build per file.
set -u
CORPUS=$1; LIB=${2:-equational-theories}; INTERVAL=${3:-300}; QUIET=${4:-300}
ROOT=$(cd "$(dirname "$0")/.." && pwd); cd "$ROOT"
LIB_NS=$(python3 -c "import sys; sys.path.insert(0,'scripts'); from generate import pascal; print(pascal('$LIB'))")
while true; do
  out=$(python3 scripts/promote.py --corpus "$CORPUS" --library "$LIB" --quiescent "$QUIET" 2>&1); rc=$?
  last=$(printf '%s\n' "$out" | tail -1)
  echo "[$(date +%T)] rc=$rc $last"
  printf '%s\n' "$out" | grep "^NOT promoted" | cut -c1-300
  if printf '%s\n' "$out" | grep -q "^promoted \|^NOT promoted"; then
    for _ in 1 2 3 4 5; do
      git add -A -- data/staging data/trusted "Tengoku/$LIB_NS" "Tengoku/$LIB_NS.lean" Tengoku/All.lean 2>/dev/null \
        && git commit -q -m "Promote $LIB: $last" 2>/dev/null && break
      sleep 3
    done
    git push -q origin main 2>/dev/null || true
  fi
  sleep "$INTERVAL"
done
