# Validation scripts

Run from the repository root after the full warning-strict build:

```powershell
python scripts/check-module-boundaries.py
python scripts/check-lean-options.py
python scripts/check-doc-references.py
python scripts/check-se-evidence.py
python -m unittest discover -s scripts -p 'test_*.py'
```

The module check validates active import resolution, build-root coverage,
aggregators and architectural boundaries. The source-policy check rejects
unchecked proof admissions and local option overrides. Documentation checks
resolve active Lean names and Markdown links. The SE evidence check inspects
actual declaration dependencies of the checked calendar theorem.

Investigation scripts are preserved in the [archive](../archive/se-generalization/README.md).
They are reference material and are not part of the default test or build roots.
