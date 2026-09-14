#!/usr/bin/env bash
# Pin this checkout of the tree to the newest PUBLISHED build cache, so that
# `lake build Tengoku.All` is a pure replay: nothing compiles, ever.
#
#   scripts/pin.sh            # fetch → newest cache commit → check it out → unpack its cache → replay-build
#   scripts/pin.sh --check    # change nothing: print "current <sha>" (exit 0) or "newer <sha>" (exit 3)
#
# The Leak services run this at image build, at container start, from their
# `tengoku_sync` tool and on POST /refresh (which the nightly cache workflow
# calls right after it publishes). Safe to run repeatedly: a tree already at
# the newest cache commit with its build present is a no-op.
set -euo pipefail
cd "$(dirname "$0")/.."

git fetch -q origin main
# Ask with the newest cache.sh: an older pinned copy may list caches in the
# wrong order. (Restored by the checkout below; harmless if we stop early.)
git checkout -q origin/main -- scripts/cache.sh
latest="$(scripts/cache.sh latest)"
head="$(git rev-parse HEAD)"
built=""
[ -n "$(find .lake/build/lib -name All.olean -path '*Tengoku/All.olean' 2>/dev/null | head -n 1)" ] && built=1

if [ "${1:-}" = "--check" ]; then
  git checkout -q -- scripts/cache.sh 2>/dev/null || true
  if [ "$latest" = "$head" ] && [ -n "$built" ]; then echo "current $latest"; exit 0; fi
  echo "newer $latest"; exit 3
fi
if [ "$latest" = "$head" ] && [ -n "$built" ] && [ "${TENGOKU_FORCE:-0}" != "1" ]; then
  git checkout -q -- scripts/cache.sh 2>/dev/null || true
  echo "already pinned to $latest (build present)"; exit 0
fi

echo "pinning the tree to cache commit $latest (was ${head:0:12})"
git checkout -q -f "$latest"
scripts/cache.sh get
lake build Tengoku.All
echo "pinned to $latest"
