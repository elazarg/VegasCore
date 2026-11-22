#!/usr/bin/env bash
# Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE).

# Bump the Lean toolchain and the pinned Mathlib and GameTheory tags together.
#
# Usage: scripts/bump-lean-mathlib.sh v4.32.0 [gametheory-tag]
#
# The GameTheory tag defaults to the version and must already be pushed, on the
# same toolchain and Mathlib. This only does the mechanical text substitution and
# manifest refresh. After running it you still need to `lake --wfail build` and
# fix any resulting breakage.
set -euo pipefail

if [ $# -lt 1 ] || [ $# -gt 2 ]; then
  echo "Usage: $0 <version> [gametheory-tag]  (e.g. v4.32.0)" >&2
  exit 1
fi

version="$1"
case "$version" in
  v*) ;;
  *) echo "Version must look like 'v4.32.0' (leading 'v')" >&2; exit 1 ;;
esac
foundation_tag="${2:-$version}"

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$root"
foundation_url="https://github.com/elazarg/GameTheory"
foundation=".lake/packages/GameTheory"

# VegasCore does not own the GameTheory bump: check that it landed before
# editing anything here.
if ! git ls-remote --exit-code "$foundation_url" "refs/tags/$foundation_tag" > /dev/null; then
  echo "error: cannot find GameTheory tag '$foundation_tag'." \
    "Bump and tag GameTheory itself first (and push it)." >&2
  exit 1
fi

set_rev() {
  sed -i -E "/^name = \"$1\"\$/,/^rev = /s/^rev = \".*\"\$/rev = \"$2\"/" lakefile.toml
  echo "lakefile.toml: $1 -> $2"
}

printf 'leanprover/lean4:%s\n' "$version" > lean-toolchain
set_rev mathlib "$version"
set_rev GameTheory "$foundation_tag"
# Links into the foundation name the pinned tag; the documentation check enforces it.
git grep -lzF "$foundation_url/" -- '*.md' |
  xargs -0 sed -i -E "s#($foundation_url/(blob|tree)/)v[^/)]+#\1$foundation_tag#g"
sed -i -E "/GameTheory\/tree\//s/\[\`v[^\`]+\`\]/[\`$foundation_tag\`]/" README.md

# `lake update` shells out to git over HTTPS for every dependency and
# regularly hits transient "Failed to connect to github.com port 443"
# errors. Retry a bunch of times before giving up for good.
#
# Mathlib's post-update hook would unpack several GB of artifacts even where the
# checkout is about to be replaced by one that already has them, so skip it.
max_attempts=10
for ((attempt = 1; ; attempt++)); do
  echo "lake update mathlib GameTheory (attempt $attempt/$max_attempts)..."
  if MATHLIB_NO_CACHE_ON_UPDATE=1 lake update mathlib GameTheory; then break; fi
  if [ "$attempt" -ge "$max_attempts" ]; then
    echo "lake update failed after $max_attempts attempts" >&2
    exit 1
  fi
  sleep 5
done

if ! cmp -s lean-toolchain "$foundation/lean-toolchain" ||
    ! grep -qF "\"mathlib\" @ git \"$version\"" "$foundation/lakefile.lean"; then
  echo "error: GameTheory $foundation_tag is not on Lean and Mathlib $version." >&2
  exit 1
fi

if lake build --no-build Mathlib > /dev/null 2>&1; then
  echo "Mathlib artifacts already present."
else
  lake exe cache get
fi

echo
echo "Done."
