#!/usr/bin/env bash
# Copyright (c) 2026 VegasCore contributors. All rights reserved.
# Released under MIT license as described in the file LICENSE.

# Bump the Lean toolchain + pinned Mathlib rev, and update the GameTheory
# submodule (recursively, including its own fixed-point-theorems-lean4
# submodule) to the latest pushed commit.
#
# Usage: scripts/bump-lean-mathlib.sh v4.32.0
#
# This only does the mechanical text substitution + submodule/manifest
# refresh. After running it you still need to `lake build` and fix any
# resulting breakage.
set -euo pipefail

if [ $# -ne 1 ]; then
  echo "Usage: $0 <version>  (e.g. v4.32.0)" >&2
  exit 1
fi

version="$1"
case "$version" in
  v*) ;;
  *) echo "Version must look like 'v4.32.0' (leading 'v')" >&2; exit 1 ;;
esac

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
submodule="$root/GameTheory"

update_toolchain() {
  local file="$1"
  printf 'leanprover/lean4:%s\n' "$version" > "$file"
  echo "updated $file"
}

update_mathlib_rev_toml() {
  local file="$1"
  sed -i -E "0,/^rev = \"v[0-9]+\.[0-9]+\.[0-9]+\"\$/s//rev = \"${version}\"/" "$file"
  echo "updated $file"
}

# `lake update` shells out to git over HTTPS for every dependency and
# regularly hits transient "Failed to connect to github.com port 443"
# errors. Retry a bunch of times before giving up for good.
retry_lake_update() {
  local dir="$1"
  local max_attempts=10
  local attempt=1
  while [ "$attempt" -le "$max_attempts" ]; do
    echo "[$dir] lake update mathlib (attempt $attempt/$max_attempts)..."
    if (cd "$dir" && lake update mathlib); then
      echo "[$dir] lake update mathlib succeeded on attempt $attempt"
      return 0
    fi
    echo "[$dir] lake update mathlib failed on attempt $attempt"
    attempt=$((attempt + 1))
    sleep 5
  done
  echo "[$dir] lake update mathlib failed after $max_attempts attempts" >&2
  return 1
}

echo "Syncing GameTheory submodule (recursively) to latest origin/main..."
(cd "$submodule" && git fetch origin && git checkout origin/main && git submodule update --init --recursive)

# VegasCore does not own the GameTheory bump: GameTheory bumps its own Lean
# toolchain + Mathlib pin in its own repo. Here we only follow its
# already-pushed commit, so verify it actually landed the target version
# instead of silently building against a stale one.
submodule_toolchain="$(cat "$submodule/lean-toolchain")"
if [ "$submodule_toolchain" != "leanprover/lean4:${version}" ]; then
  echo "error: GameTheory submodule is on toolchain '$submodule_toolchain'," \
    "expected 'leanprover/lean4:${version}'. Bump GameTheory itself first" \
    "(and push it) before bumping VegasCore." >&2
  exit 1
fi
submodule_mathlib_rev="$(grep -oE 'mathlib.*@ git "v[0-9]+\.[0-9]+\.[0-9]+"' "$submodule/lakefile.lean" | grep -oE 'v[0-9]+\.[0-9]+\.[0-9]+')"
if [ "$submodule_mathlib_rev" != "$version" ]; then
  echo "error: GameTheory submodule pins Mathlib '$submodule_mathlib_rev'," \
    "expected '${version}'. Bump GameTheory itself first (and push it)" \
    "before bumping VegasCore." >&2
  exit 1
fi
echo "GameTheory submodule already on Lean/Mathlib ${version}, good."

# lake-manifest.json caches each dependency's config filename. If GameTheory
# switched build config format (lakefile.toml <-> lakefile.lean) since this
# manifest was last regenerated, `lake update` fails looking for a file that
# no longer exists. Self-heal by pointing the cached entry at whichever
# config file the submodule actually has.
manifest="$root/lake-manifest.json"
if [ -f "$submodule/lakefile.lean" ]; then
  actual_config="lakefile.lean"
elif [ -f "$submodule/lakefile.toml" ]; then
  actual_config="lakefile.toml"
else
  echo "error: GameTheory submodule has no lakefile.lean or lakefile.toml" >&2
  exit 1
fi
sed -i -E "/\"name\": \"GameTheory\",/,+4 s/\"configFile\": \"[^\"]*\"/\"configFile\": \"${actual_config}\"/" "$manifest"
echo "manifest GameTheory configFile -> $actual_config"

update_toolchain "$root/lean-toolchain"
update_mathlib_rev_toml "$root/lakefile.toml"

echo
echo "Updating manifest + cache..."
retry_lake_update "$root"
(cd "$root" && lake exe cache get)

echo
echo "Done."
