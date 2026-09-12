#!/usr/bin/env bash
# Tengoku build cache — stored on the repository as GitHub Release assets, so
# nobody has to build the tree from scratch.
#
#   scripts/cache.sh get [<commit>]   # download + unpack the cache for HEAD (or a commit)
#   scripts/cache.sh put              # pack .lake/build and publish it for HEAD
#
# A cache is keyed by the tree's commit: release tag `cache-<sha>`; `get` walks
# back through the current branch's ancestry until it finds a published cache
# (an older cache is still a valid starting point — Lake rebuilds only what
# changed). Assets are zstd tarballs split into <2GB parts (GitHub's limit).
set -euo pipefail
cd "$(dirname "$0")/.."
REPO="${TENGOKU_REPO:-competemath/tengoku}"
cmd="${1:-}"

need() { command -v "$1" >/dev/null 2>&1 || { echo "missing: $1" >&2; exit 1; }; }
need gh; need zstd; need tar

case "$cmd" in
  put)
    sha="$(git rev-parse HEAD)"
    tag="cache-$sha"
    [ -d .lake/build ] || { echo "nothing to publish: .lake/build missing" >&2; exit 1; }
    tmp="$(mktemp -d)"
    echo "packing .lake/build for $sha …"
    tar -C .lake -cf - build | zstd -T0 -3 -q | split -b 1900m - "$tmp/tengoku-cache.tar.zst.part-"
    ls -la "$tmp"
    if gh release view "$tag" -R "$REPO" >/dev/null 2>&1; then
      gh release delete "$tag" -R "$REPO" --yes
    fi
    gh release create "$tag" -R "$REPO" --title "build cache $sha" --notes "Compiled .lake/build for $sha ($(cat lean-toolchain)). Fetch with scripts/cache.sh get." "$tmp"/tengoku-cache.tar.zst.part-*
    rm -rf "$tmp"
    echo "published $tag"
    ;;
  get)
    want="${2:-HEAD}"
    tmp="$(mktemp -d)"
    found=""
    # Walk ancestry (newest first) for a published cache.
    for sha in $(git rev-list --max-count=200 "$want"); do
      if gh release view "cache-$sha" -R "$REPO" >/dev/null 2>&1; then found="$sha"; break; fi
    done
    [ -n "$found" ] || { echo "no published cache in the last 200 commits of $want" >&2; exit 1; }
    echo "fetching cache-$found …"
    gh release download "cache-$found" -R "$REPO" -D "$tmp" -p 'tengoku-cache.tar.zst.part-*'
    mkdir -p .lake
    cat "$tmp"/tengoku-cache.tar.zst.part-* | zstd -d -q | tar -C .lake -xf -
    rm -rf "$tmp"
    echo "unpacked cache-$found into .lake/build (Lake rebuilds only what differs from HEAD)"
    ;;
  *)
    echo "usage: $0 get [<commit>] | put" >&2; exit 2 ;;
esac
