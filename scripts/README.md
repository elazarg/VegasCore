# Validation and inventory scripts

Run the strict build and checks from the repository root:

```powershell
lake build
python scripts/check-paper-audit.py
python scripts/check-module-boundaries.py
python scripts/check-lean-options.py
python scripts/check-doc-references.py
python -m unittest discover -s scripts -p 'test_*.py'
```

Module checks validate imports, aggregator coverage and architectural layers.
Source policy rejects admissions, axiom declarations and trust escapes and enforces
central options. The separate Lean-native paper audit runs after the build: it
uses Lean's parser and elaborated declaration types, requires every authored
proof (including proof-valued definitions and abbreviations) to have an adjacent
exact guarded pin, and checks its actual axioms. It permits fresh local identifier
shorthands but rejects instance-changing opens, shadowing notation, attributes
and syntax extensions. Data defaults and documented structure fields are supported;
proof-valued field defaults must be stated as separate named results. Its import driver is isolated from the paper and needs
no unsafe loader or theorem-source exceptions. Native mutation fixtures check
coverage, adjacency and explicit statements independently.
Documentation checks resolve active citations and Markdown paths; external
sources pinned by full commit IDs refer to their own tree.

`python scripts/report-unreached.py` reports declaration reachability from
Paper, examples and tests. Its lexical approximations are investigation leads;
the build validates removals. `python scripts/proof-inventory.py --help` describes
the declaration and proof-window inventory. `python lean-defs.py <files>`
prints declaration surfaces without proofs.

Broader proof experiments and research scripts are available through the
[archive index](../docs/archives.md).
