#!/usr/bin/env bash
# Tengoku build cache — stored on the repository as GitHub Release assets, so
# nobody has to build the tree from scratch.
#
#   scripts/cache.sh get [<commit>]   # download + unpack the newest cache that is an ancestor of HEAD (or <commit>)
#   scripts/cache.sh latest           # print the commit of the newest published cache (pin a checkout to it:
#                                     #   git checkout $(scripts/cache.sh latest) && scripts/cache.sh get — then
#                                     #   `lake build` is a pure replay and compiles nothing)
#   scripts/cache.sh put              # pack .lake/build and publish it for HEAD (needs `gh` logged in)
#
# A cache is keyed by the tree's commit: release tag `cache-<sha>`. `get`
# picks the newest published cache whose commit is an ancestor of the wanted
# one — an older cache is still a valid starting point, Lake rebuilds only
# what changed since. Assets are zstd tarballs split into <2GB parts
# (GitHub's limit). `get` needs no GitHub account: the repository is public,
# so it reads the release list and the assets anonymously (curl); `gh` is
# used when it is installed and logged in.
set -euo pipefail
cd "$(dirname "$0")/.."
REPO="${TENGOKU_REPO:-competemath/tengoku}"
cmd="${1:-}"

need() { command -v "$1" >/dev/null 2>&1 || { echo "missing: $1" >&2; exit 1; }; }
need zstd; need tar; need git

have_gh() { command -v gh >/dev/null 2>&1 && gh auth status >/dev/null 2>&1; }

# Every published cache tag, newest first.
list_cache_tags() {
  if have_gh; then
    gh release list -R "$REPO" --limit 200 --json tagName,createdAt \
      --jq '[.[] | select(.tagName | startswith("cache-"))] | sort_by(.createdAt) | reverse | .[].tagName'
  else
    need curl
    local page=1
    while :; do
      local out
      out="$(curl -fsSL -H 'Accept: application/vnd.github+json' ${GH_TOKEN:+-H "Authorization: Bearer $GH_TOKEN"} \
        "https://api.github.com/repos/$REPO/releases?per_page=100&page=$page")"
      printf '%s' "$out" | grep -o '"tag_name": *"cache-[0-9a-f]*"' | sed -E 's/.*"(cache-[0-9a-f]+)"/\1/'
      printf '%s' "$out" | grep -q '"tag_name"' || break
      page=$((page + 1))
      [ "$page" -le 10 ] || break
    done
  fi
}

# Download every part of one cache release into $2.
download_cache() {
  local tag="$1" dir="$2"
  if have_gh; then
    gh release download "$tag" -R "$REPO" -D "$dir" -p 'tengoku-cache.tar.zst.part-*'
  else
    need curl
    local urls
    urls="$(curl -fsSL -H 'Accept: application/vnd.github+json' ${GH_TOKEN:+-H "Authorization: Bearer $GH_TOKEN"} \
      "https://api.github.com/repos/$REPO/releases/tags/$tag" \
      | grep -o '"browser_download_url": *"[^"]*tengoku-cache.tar.zst.part-[^"]*"' | sed -E 's/.*"(https[^"]+)"/\1/')"
    [ -n "$urls" ] || { echo "no cache parts on $tag" >&2; exit 1; }
    for u in $urls; do
      echo "  $u"
      curl -fL --retry 3 -o "$dir/$(basename "$u")" "$u"
    done
  fi
}

case "$cmd" in
  put)
    need gh
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
    # Keep the newest KEEP caches; each is gigabytes and `get` only ever needs
    # a recent one (Lake rebuilds the difference).
    KEEP="${TENGOKU_CACHE_KEEP:-5}"
    list_cache_tags | tail -n +"$((KEEP + 1))" \
      | while read -r old; do [ -n "$old" ] && gh release delete "$old" -R "$REPO" --yes --cleanup-tag && echo "pruned $old"; done || true
    ;;
  latest)
    tag="$(list_cache_tags | head -n 1)"
    [ -n "$tag" ] || { echo "no published cache" >&2; exit 1; }
    echo "${tag#cache-}"
    ;;
  get)
    want="$(git rev-parse "${2:-HEAD}")"
    tmp="$(mktemp -d)"
    found=""
    # Newest cache first; the first one whose commit is an ancestor of what we
    # want is the best starting point. (A shallow clone cannot answer
    # ancestry — clone with --filter=blob:none or enough depth.)
    for tag in $(list_cache_tags); do
      sha="${tag#cache-}"
      if git merge-base --is-ancestor "$sha" "$want" 2>/dev/null; then found="$tag"; break; fi
    done
    [ -n "$found" ] || { echo "no published cache is an ancestor of $want (are the caches published? is this clone deep enough for ancestry?)" >&2; exit 1; }
    echo "fetching $found …"
    download_cache "$found" "$tmp"
    mkdir -p .lake
    cat "$tmp"/tengoku-cache.tar.zst.part-* | zstd -d -q | tar -C .lake -xf -
    rm -rf "$tmp"
    echo "unpacked $found into .lake/build (Lake rebuilds only what differs from $want)"
    ;;
  *)
    echo "usage: $0 get [<commit>] | latest | put" >&2; exit 2 ;;
esac
