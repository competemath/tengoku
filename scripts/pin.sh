#!/usr/bin/env bash
# Pin this checkout of the tree to the newest PUBLISHED build cache. Nothing
# is ever compiled here: the replay check runs with `--no-build`, so Lake can
# only confirm the cache covers the tree, or fail.
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
tag="$(scripts/cache.sh latest-tag)"
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

echo "pinning the tree to $tag (commit $latest, was ${head:0:12})"
git checkout -q -f "$latest"
scripts/cache.sh get
# Verify the replay WITHOUT letting Lake compile anything: if the cache did not
# cover the tree exactly, this fails loudly instead of building.
lake build Tengoku.All --no-build
echo "pinned to $latest"
# The pinned commit may predate these helper scripts: keep the newest copies
# from main so the next run (and the services' /refresh) can find them. Done
# last, in one compound command, so bash never reads past it.
{ git checkout -q origin/main -- scripts/cache.sh scripts/pin.sh 2>/dev/null || true; exit 0; }
