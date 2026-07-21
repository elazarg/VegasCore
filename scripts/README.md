# Maintenance scripts

Run these tools from the repository root.

- `scripts/bump-lean-mathlib.sh v4.32.0` updates the Lean toolchain and
  Mathlib pins, advances the recursive `GameTheory` submodule, refreshes Lake
  manifests, and verifies that the dependency pins agree. Review the resulting
  changes and run `lake build` afterward.
- `python lean-defs.py Vegas` prints the Lean declaration surface below the
  supplied files or directories while omitting imports and proof bodies. With
  no arguments it scans the current directory recursively. It is a reading and
  review aid; it does not participate in the build.
