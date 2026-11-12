# Validation and inventory scripts

Run the strict build and checks from the repository root:

```powershell
lake --wfail build
python scripts/check-paper-audit.py
python scripts/check-module-boundaries.py
python scripts/check-lean-options.py
python scripts/check-doc-references.py
python -m unittest discover -s scripts -p 'test_*.py'
python -m unittest scripts.paper_audit_tests
```

The strict build rejects compiler warnings and Lake warnings, including replayed
warnings from cached builds. Local Lean files use explicit module headers and
public imports; exposed public sections retain definition unfolding. Lean exports
the checked transitive axiom dependencies used by the paper audit.
Module checks validate imports, aggregator coverage and architectural layers.
Source policy rejects admissions, axiom declarations and trust escapes and enforces
central options. The separate Lean-native paper audit runs after the build: it
uses Lean's parser and elaborated declaration types, requires every authored
Prop-typed declaration (including definitions and abbreviations of proofs) to
have an adjacent exact guarded pin, and checks its actual axioms. Proofs stored
inside data are not counted separately; a pinned result using such data still
has its complete transitive axiom dependencies checked. Generated equation and
elaborator helpers require no separate pins; `where` and `let rec` helpers are
not permitted in Paper. Result parameters need explicit types.

The audit permits fresh local identifier shorthands and ordinary opens of Vegas,
GameTheory and Interaction namespaces, including term-level opens. It rejects
classes, scoped opens, shadowing notation, attributes and syntax extensions.
Notation names are checked again when declarations or opens change their scope.
Data defaults and documented structure fields are supported; proof-valued field
defaults must be stated as separate named results. Each file uses its own exact
import header and pristine import environment, before validator declarations.
Before auditing, `lake --wfail build --no-build Paper Tools` rejects missing or
stale proof artifacts and cached warnings. The isolated driver uses no loader overrides and never
rebuilds those artifacts. Every Lean
subprocess has a visible 180-second timeout; no cross-process mutex is needed.
Native mutation fixtures check coverage, adjacency and explicit statements
independently. CI runs ordinary script tests before the Lean build and the
native audit tests afterward.

Documentation checks resolve active citations and Markdown paths; external
sources pinned by full commit IDs refer to their own tree.

`python scripts/report-unreached.py` reports declaration reachability from
Paper, examples and tests. Its lexical approximations are investigation leads;
the build validates removals. `python scripts/proof-inventory.py --help` describes
the declaration and proof-window inventory. `python lean-defs.py <files>`
prints declaration surfaces without proofs.

Broader proof experiments and research scripts are available through the
[archive index](../docs/archives.md).
