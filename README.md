# VegasCore

VegasCore is a Lean 4 foundation for executable games with partial information.
Its full-language compilation path is:

```text
failure-aware sequential source
  -> typed immutable graph
  -> public pending-message application
```

The first edge has checked exact outcome and arbitrary unilateral-deviation
laws, and Nash/same-error epsilon-Nash equivalence at compiled profiles.
It covers every `SourceProgram` constructor, without finite-domain,
guard-feasibility, or failure-dominance premises. The source includes explicit
binding and disclosure failure, heterogeneous publication results, deferred
guards, private initial inputs, own-action recall, and dependent public chance.

The message host executes the typed graph directly using the shared
`Interaction` pool, ideal opaque commitments, public validation, and relative
deadlines. Its local transition laws and mixed-feature transport tests are
checked. Its prescribed-policy translation, whole-run honest law, and
arbitrary-deviation certificate remain to be proved. Thus the full-language
Nash theorem currently reaches the graph, not the pending-message runtime.

A restricted `WFProgram` / `Vegas.EventGraph` candidate backend separately has
checked end-to-end public outcome and unilateral-deviation utility bounds,
composed through a graph-relative certificate. It preserves and reflects
same-error epsilon-Nash at generated profiles under explicit deadline-relative
service and pointwise source quitting conditions. It requires homogeneous,
sample-free graphs, universally accepting commitment guards, and
commitment-produced disclosures. That certificate does not cover the revised
failure-aware source. See [the active tower](docs/active-tower.md) for the
theorems and exact assumptions.

Outcomes, executable payouts, and player utilities are separate interfaces.
Source-outcome guarantees do not automatically cover preferences over native
traffic or costs. Computational commitment security, concrete entropy, and
ledger/EVM refinement require further target edges.

The active libraries are `GameTheoryExtensions`, `Interaction`, `Vegas`,
the retained tests, and the source/native paper audit. See
[the artifact guide](ARTIFACT.md), [module boundaries](docs/module-architecture.md),
and [compilation design](docs/compilation-design.md).

## Build

```text
git submodule update --init --recursive
lake exe cache get
python scripts/check-doc-references.py
python scripts/check-lean-options.py
python scripts/check-module-boundaries.py
python -m unittest discover -s scripts -p "test_*.py"
lake --wfail build
```

GameTheory is a pinned, separately maintained software dependency. General
game-theoretic simulation results live under GameTheory namespaces; Vegas owns
the source language, event-graph compiler, and its native integration.

## Paper target and proof status

The single active `Paper.lean` audit selects paper-visible capstones and
important lemmas, all directly delegated to proved repository theorems with
axiom pins. Supporting proofs stay in their owning modules; archives do not
contribute proof coverage. The current theorem boundary is listed in
[the active tower](docs/active-tower.md). The
[road ahead](docs/a-road-ahead.md) sets the full-language and executable-target
milestones, and the [typed message proof plan](docs/typed-message-edge.md)
separates the operational host from the remaining strategic argument.

The [source rationale](docs/source-design-rationale.md) records the semantics
choices and their small examples and counterexamples. The corresponding
[migration plan](docs/source-semantics-migration.md) separates the checked
source-to-graph results from the remaining runtime integration.

A successful Lean build checks the active proof terms. It is not evidence that
the separate manuscript's claims are all established. `paper-claims.json`
distinguishes direct audit mappings, supporting results without a paper audit,
and explicitly unverified manuscript claims. Strict checking requires direct
audits; coverage checking alone does not establish the manuscript's claims.
These statuses are not a count or a worklist of missing theorems. Reference
material supplies neither proofs nor audit obligations.

Readable source material for porting is preserved in the
[proof reference archive](archive/fused/README.md), outside all active libraries.
