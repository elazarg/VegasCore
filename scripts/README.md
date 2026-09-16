# Maintenance scripts

Run these tools from the repository root.

- `python scripts/check-module-boundaries.py` checks local import resolution,
  default-build reachability, complete directory aggregators, cycles in the
  module and sibling-directory dependency graphs, and the semantic layer
  contracts. Graph semantics are independent of the pending backend; the backend
  is independent of source/compiler modules; shared expressions and the verified
  tower are independent of the surface prototype. Cycle reports include witness
  imports; acyclicity supplements rather than replaces the direction rules.
  Every tracked Lean source belongs to a configured library; production
  libraries may not import test libraries.

- `lake --wfail build Paper` checks the single paper audit in root `Paper.lean`.
  Its proved statements delegate directly to repository theorems. Every audit
  theorem has a guarded axiom pin directly below it; axiom-print commands occur
  only in this file. Precisely stated prospective end-to-end declarations
  may be admitted, but no such declaration counts as a proof.
- `python -m unittest discover -s scripts -p 'test_*.py'` checks the maintenance
  tooling, including module boundaries, documentation references, centralized
  options, admission policy, and capstone axiom-pin coverage.

- `python scripts/check-lean-options.py` rejects source-local `set_option`
  directives in every project Lean source tree and checks that both implicit-binder
  options are disabled and warnings are errors. It also rejects proof admissions
  outside root `Paper.lean`, confines axiom prints to that file, and requires a
  guarded axiom report directly below every capstone. Shared elaboration and lint settings
  belong in `lakefile.toml`; separately managed dependencies keep their own
  package configuration.
- `scripts/bump-lean-mathlib.sh v4.32.0` updates the Lean toolchain and
  Mathlib pins, advances the recursive `GameTheory` submodule, refreshes Lake
  manifests, and verifies that the dependency pins agree. Review the resulting
  changes and run `lake build` afterward.
- `python lean-defs.py Vegas` prints the Lean declaration surface below the
  supplied files or directories while omitting imports and proof bodies. With
  no arguments it scans the current directory recursively. It is a reading and
  review aid; it does not participate in the build.
- `python scripts/check-doc-references.py` fails if a Lean docstring cites a
  name that does not exist. Docstrings here carry real load -- which theorem
  does the work, which hypothesis a result needs, which witness refutes a
  converse -- and a citation that stops resolving after a rename turns that
  guidance into misdirection with nothing in the build noticing. It checks
  backticked tokens whose last component is lower-case and whose name is
  qualified or underscored; type names, tactics, and prose are untouched.
  In tracked Markdown it also checks exact root-qualified Lean file paths in
  inline code and relative `.md`/`.lean` links. Abbreviated paths, link anchors,
  and external resources are outside this check; it is not a full Markdown
  parser or a line-number accuracy audit.
  All tracked Markdown is checked, without directory-specific exemptions.
  A non-Git export explicitly reports that the tracked Markdown inventory is
  unavailable; a Git inventory failure in a checkout is an error.
