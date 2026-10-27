# Validation and inventory scripts

Run the strict build and checks from the repository root:

```powershell
lake build
python scripts/check-module-boundaries.py
python scripts/check-lean-options.py
python scripts/check-doc-references.py
python -m unittest discover -s scripts -p 'test_*.py'
```

Module checks validate imports, aggregator coverage and architectural layers.
Source policy rejects admissions, axiom declarations and trust escapes, enforces
central options and checks exact standard-axiom pins for Paper theorems.
Documentation checks resolve active citations and Markdown paths; external
sources pinned by full commit IDs refer to their own tree.

`python scripts/report-unreached.py` reports declaration reachability from
Paper, examples and tests. Its lexical approximations are investigation leads;
the build validates removals. `python scripts/proof-inventory.py --help` describes
the declaration and proof-window inventory. `python lean-defs.py <files>`
prints declaration surfaces without proofs.

Broader proof experiments and research scripts are available through the
[archive index](../docs/archives.md).
