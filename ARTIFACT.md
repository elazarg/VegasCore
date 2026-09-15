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
| Full failure-aware source and its safety | `Vegas/Source/Basic.lean`, `Semantics.lean`, `Safety.lean` |
| Typed graph semantics and compilation | `Vegas/Graph/`, `Vegas/Compile/GraphCompiler.lean` |
| Exact full-source/graph strategic certificate | `Vegas/Game/GraphCompilation.lean`, `GraphSetup.lean` |
| Full typed public-message host and local laws | `Vegas/Graph/MessageApplication.lean`, `MessageStepLaw.lean`, `MessageInvariant.lean` |
| Actual player-policy compiler and execution laws | `Vegas/Graph/MessagePolicies.lean`, `MessageBindingLaw.lean`, `MessageResolutionLaw.lean` |
| Binding-origin certificate and verifier provenance | `Vegas/Compile/GraphBindingDiscipline.lean`, `Vegas/Graph/MessageBindingProvenance.lean` |
| Whole-prefix policy memory projection | `Vegas/Graph/MessageHistoryExtension.lean` |
| Reserved service and arbitrary-policy termination | `Vegas/Graph/MessageService.lean`, `MessageServiceTermination.lean` |
| Shared-private-setup predrawing | `Interaction/MessageApplicationPredrawTransport.lean` |
| Concrete full-language pending target | `Vegas/Game/GraphMessages.lean` (completion proved; honest/deviation laws unproved) |
| Pending messages and candidate commitments | `Interaction/MessageApplication.lean`, `Interaction/CommitmentCandidates.lean` |
| Restricted graph-relative candidate strategic edge | `Vegas/Game/SealedCandidate.lean` |
| Restricted source-to-pending Nash | `Vegas/Game/SourcePublicCandidate.lean` |
| Source-only quitting condition | `Vegas/Core/SourceQuitPrefix.lean` |
| Generic compositional incentive bounds | `GameTheoryExtensions/Core/UtilitySimulation.lean` |
| Paper-visible capstones and important lemmas | `Paper.lean` |

Read each owning theorem and its definitions, not just its audit restatement.
The full-source/graph theorem covers every `SourceProgram` constructor. The
pending-message strategic theorem still concerns the restricted `WFProgram`
candidate backend, with hypotheses stated in the
[active tower](docs/active-tower.md#restricted-candidate-certificate).

## Paper audit

`Paper.lean` is a compact direct-delegation audit, not an inventory of support
lemmas. Three pending-message capstones are explicitly admitted, with expected
diagnostics and `sorryAx` pins. They name the actual compiler and native game;
they are not proved results or assumptions available to library proofs.
Every declaration has an axiom pin. Supporting probability, extraction,
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

- `VegasTests/SourceSemantics.lean` proves complete laws for a failure-aware
  program with heterogeneous values, deferred guards, initial secrets, chance,
  and failure-sensitive settlement.
- `VegasTests/GraphMessages.lean` executes that compiled graph through actual
  submission, recipient-local delivery, inclusion, and timeout. It checks
  successful and failed payouts and preservation of the completed outcome
  across later ticks; it is not a whole-program strategy law.
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
correspondence have distinct conclusions. Nash preservation requires deviation
control as well as honest agreement, either through exact laws or sufficient
utility bounds. The restricted selective-quitting bound does not imply exact
deviation outcome equality or another player's arbitrary worst-case outcome
guarantee.

The repository does not treat an executable compiler, encoding lemma, test
vector, or partial VM proof as whole-program refinement. Concrete execution
must identify both deployed code and its operational host.
