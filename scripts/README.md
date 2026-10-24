# Validation scripts

Run from the repository root after the full warning-strict build:

```powershell
python scripts/check-module-boundaries.py
python scripts/check-lean-options.py
python scripts/check-doc-references.py
python -m unittest discover -s scripts -p 'test_*.py'
```

The module check validates active import resolution, build-root coverage,
aggregators and architectural boundaries. The source-policy check keeps
options central, rejects proof admissions, axiom declarations and trust escape
hatches, and requires an exact standard-axiom pin after every Paper theorem.
Documentation checks resolve active Lean names and Markdown links; a citation
inside a link to the `research-tree` tag names that tag's tree.

`python scripts/report-unreached.py` lists the modules none of whose
declarations a Paper theorem, a test or an example uses, largest first. Names
mentioned in test and example source count as uses, since `example` commands
leave no declaration to follow. It reports only; `--strict` makes a nonempty
list fail. Uses through notation or tactics elsewhere are invisible to it, so
the build confirms each removal.

The [experiments](experiments) directory holds the investigation scripts that
research notes cite. They are reference material and are not part of the
default test or build roots.

`python scripts/proof-inventory.py --output ephemeral/proof-review` inventories
tracked Lean source, including the separately managed GameTheory tree. It writes
module/declaration CSV files, a layer summary, and cross-file matches of exact
eight-line proof windows. Body recognition is lexical and includes tactic-valued
definitions; windows overlap. Use matches to select proofs for review, not as
counts of removable lines. The [proof review](../docs/proof-review.md) explains
the measurement and its limits. The inventory never edits Lean source.

`python scripts/check-proof-review-probes.py` replays the isolated Lean sources
in the [checked-probe appendix](../docs/proof-review/checked-probes.md) after the
ordinary build. It uses the built central Lake setup and writes only temporary
files. `--list` lists the experiments; `--probe NAME` checks a single one. This
validates review statements without treating them as merged production APIs.
