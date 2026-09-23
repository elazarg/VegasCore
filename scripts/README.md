# Maintenance scripts

Run these tools from the repository root.

- `python scripts/experiments/coalescing.py` exhaustively checks pure SPE in
  split, coalesced, and interleaved finite design games. It computes proper
  roots from information-set closure and tests whole-policy deviations.
  [Action boundaries and subgame perfection](../docs/action-coalescing.md)
  states the results and the remaining native-service proof obligations.

- `python scripts/check-module-boundaries.py` checks local import resolution,
  default-build reachability, complete directory aggregators, cycles in the
  module and sibling-directory dependency graphs, and the semantic layer
  contracts. Graph semantics are independent of the pending backend; the backend
  is independent of source/compiler modules; shared expressions and the verified
  tower are independent of the surface prototype. Cycle reports include witness
  imports; acyclicity supplements rather than replaces the direction rules.
  A source under an unclassified top-level `Vegas.*` layer is an error, so a new
  layer cannot silently bypass the dependency table.
  Every tracked Lean source belongs to a configured library; production
  libraries may not import test libraries.

- `python scripts/report-open-obligations.py` lists every result recorded as
  missing with a `-- OPEN OBLIGATION: <title>` Lean line comment, followed by
  its description on the directly following `--` lines. It never fails: CI shows
  each obligation as a warning annotation on every run, and a local
  `pre-commit` hook that runs it prints them on every commit. Use it for a
  result that cannot yet be stated precisely; a precisely stated prospective
  theorem belongs in `Paper.lean` as described below. Remove the marker in the
  commit that proves the result.
- `lake --wfail build Paper` checks the single paper audit in root `Paper.lean`.
  Its proved statements delegate directly to repository theorems. Every audit
  theorem has a guarded axiom pin directly below it; axiom-print commands occur
  only in this file. Warning-strict compilation rejects an ordinary admission.
  A precisely stated prospective theorem may use an admission only inside a
  top-level `#guard_msgs ... in` command that checks the expected warning; no
  such theorem counts as proved.
- `python -m unittest discover -s scripts -p 'test_*.py'` checks the maintenance
  tooling, including module boundaries, documentation references, centralized
  options, admission policy, and capstone axiom-pin coverage.

- `python scripts/check-lean-options.py` rejects source-local `set_option`
  commands anywhere outside comments and strings in every project Lean source
  tree, and checks that both implicit-binder options are disabled and warnings
  are errors. It also rejects bespoke `axiom` declarations, `unsafe`,
  `native_decide`, and `implemented_by` in production and test sources. Proof
  admissions are forbidden except for the explicitly warning-guarded
  `Paper.lean` case above. Axiom-print commands are confined to that file, with
  one guarded report directly below every capstone. Shared elaboration and lint
  settings belong in `lakefile.toml`; separately managed dependencies keep
  their own package configuration.
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
  qualified, underscored, camelCase, or suffixed with `?`/`!`; type names, tactics, and prose are
  untouched. Qualified static names resolve in the citation's namespace and
  opened namespaces, preserving every supplied component. Explicit project-root
  names must match exactly. An unqualified name must be unique; lowercase local
  receiver notation such as `graph.sequentialize` resolves its complete member
  suffix because the receiver itself is not statically indexable.
  In tracked Markdown it also checks these Lean-name citations, exact
  root-qualified Lean file paths in inline code, and relative `.md`/`.lean`
  links. Link anchors and external resources are outside this check; it is not
  a full Markdown parser or a line-number accuracy audit.
  All tracked Markdown is checked, without directory-specific exemptions.
  A non-Git export explicitly reports that the tracked Markdown inventory is
  unavailable; a Git inventory failure in a checkout is an error.
