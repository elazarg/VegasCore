# VegasCore proof and artifact guide

This artifact checks sequential-source, event-graph, and public pending-message
results. It does not verify the rich frontend, a blockchain ledger, deployed
contract, or EVM. See the [active tower](docs/active-tower.md) for exact source
coverage and the [road ahead](docs/a-road-ahead.md) for the broader target.

## Reproduction

Use the pinned Lean toolchain and dependency revisions:

```text
git submodule update --init --recursive
lake exe cache get
python scripts/check-doc-references.py
python scripts/check-lean-options.py
python scripts/check-module-boundaries.py
python -m unittest discover -s scripts -p "test_*.py"
lake --wfail build
python scripts/check-paper-claims.py --allow-unverified
```

Do not run `lake update` to reproduce a pinned revision. The cache is a build
optimization; the subsequent build checks the active proof terms.

## Reading route

| Question | Main location |
| --- | --- |
| Source syntax and written-order execution | `Vegas/Core/Basic.lean`, `SmallStep.lean`, `Strategy.lean` |
| Typed graph compilation | `Vegas/Compile/Compiler.lean`, `Vegas/EventGraph/` |
| Exact strategic source/graph correspondence | `Vegas/Game/SourceGraph.lean` |
| Pending messages and candidate commitments | `Interaction/MessageApplication.lean`, `Interaction/SealedCandidateResolution.lean` |
| Graph-relative candidate strategic edge | `Vegas/Game/SealedCandidate.lean` |
| Source outcomes and pending-message Nash | `Vegas/Game/SourcePublicCandidate.lean` |
| Source-only quitting condition | `Vegas/Core/SourceQuitPrefix.lean` |
| Generic compositional incentive bounds | `GameTheoryExtensions/Core/UtilitySimulation.lean` |
| Paper-visible capstones and important lemmas | `Paper.lean` |

Read each owning theorem and its definitions, not just its audit restatement.
The source/graph theorem covers all checked core programs. The pending-message
theorem has the narrower sealed-fragment and service hypotheses stated in the
[active tower](docs/active-tower.md#end-to-end-candidate-theorem).

## Paper audit

`Paper.lean` is a compact direct-delegation audit, not an inventory of support
lemmas. Every declaration has an axiom pin. Supporting probability, extraction,
provenance, and coupling proofs remain checked in their owning modules even
when they have no separate paper wrapper.

`paper-claims.json` distinguishes direct audit mappings, supporting material
without a direct paper audit, and unverified manuscript claims. The latter
categories do not count as directly audited claims. Strict checking rejects
both, as well as admitted audit declarations. This does not assert that an
omitted supporting repository lemma is unproved.

`--allow-unverified` checks registry coverage against the direct audit and
pinned manuscript snapshot while allowing those categories. Passing it is
not proof of draft parity. `--allow-missing-paper` permits a clone without the
separate manuscript, in which case prose coverage is unchecked. Neither mode
reads archived code or creates proof obligations from it.

The live manuscript is the separate `overleaf/` Git repository. Its mathematical
claims are broader and partly different from the current native theorem.
A successful Lean build does not establish them all.

## Representative integration tests

- `VegasTests/SealedPayout.lean` derives native incentives from legal source
  execution for a nonconstant programmed payout, including candidate-host play.
- `VegasTests/SealedProfilePayout.lean` separates fixed-opponent incentive
  conditions from uniform bounds and instantiates a quantitative Nash bound.
- `VegasTests/SealedCandidatePrefix.lean` uses an earlier public disclosure to
  vary the baseline and instantiates the source-prefix deviation theorem.
- `VegasTests/SealedPublicUtility.lean` supplies a nonconstant public-outcome
  utility that cannot factor through the program's payouts.
- `VegasTests/SealedCandidateDeadline.lean` protects an unchanged player under
  delayed service and an arbitrary other-player policy.
- `VegasTests/GuardValidation.lean` checks public guard validation and guarded
  candidate invariants. It is not an end-to-end guarded Nash theorem.
- `VegasTests/SourceQuitPrefix.lean` uses source chance to separate incentive
  premises. It is source-only: the sealed backend does not support samples.

These examples exercise theorem instances and distinguish assumptions. They do
not replace the universally quantified compiler statements.

## Trust boundary

Axiom pins report Lean's standard logical axioms. Production libraries may not
import the audit or contain admissions. Build-root and module-boundary checks
cover active code; archives supply no proof coverage.

The native commitment table is an ideal functionality with proved hiding and
binding properties, not a concrete cryptographic construction. Authentication,
deadline-relative service, and the finite-round invocation model are explicit
parts of the target contract. Local player views include pending messages
delivered before inclusion; the environment sees the full pool.

Support correspondence, honest outcome equality, and arbitrary-deviation
utility bounds have distinct conclusions. Only the latter together with honest
utility agreement establishes Nash preservation. The current selective-quitting
bound does not imply exact deviation outcome equality or another player's
arbitrary worst-case outcome guarantee.

The repository does not treat an executable compiler, encoding lemma, test
vector, or partial VM proof as whole-program refinement. Concrete execution
must identify both deployed code and its operational host.
