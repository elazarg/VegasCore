# Codebase review and dispositions

The architecture, game-theory API and proof-mining review identified redundant
proof obligations, useful general results hidden inside specialized proofs,
module ownership problems, and missing compilation and runtime refinement
edges. The safe API and implementation fixes are checked and published. The
remaining compilation edges and broader equilibrium results remain open.

The existing layer structure is coherent: reusable probability and game theory
belong in GameTheory, runtime-general protocol adapters in GameTheoryExtensions,
message execution in Interaction, and source/compiler/service instantiations in
Vegas. The review favored exposing and instantiating existing machinery over
replacing it. The independent GameTheory pass inspected architecture and
declaration surfaces across 616 Lean files; it was not a line-by-line proof audit
or a validation of every standalone module.

This records the findings and their disposition as of 2026-10-10. It includes
the additional compiler defects discovered while addressing the review.
No source or runtime model, commit/reveal/sample/withdraw language, owner-controlled
target or checklist box was changed. Existing results were retained or
generalized; no open obligation was replaced with a weaker conclusion.

## Architecture and compilation

### Surface language and checked source compilation

**Finding:** The surface prototype lowers to `SurfaceCore`, while the checked
compiler starts from the failure-aware `SourceProgram`. These are disconnected
entry points. Guard feasibility and nullable values do not specify the source
language's publication-failure behavior.

**Disposition: Open, with the boundary documented.**
[ToCore](../Vegas/Language/ToCore.lean) and
[compilation design](compilation-design.md) state the missing bridge. A checked
translation needs an approved interpretation of failure and guard timing.
That interpretation was not chosen implicitly during the cleanup.

### Expression dependency soundness

**Finding:** `IExpr` required dependency soundness as supplied fields even though
its local-evaluator coherence already implied it. The concrete expression
implementation duplicated those proofs.

**Disposition: Addressed in `8b35ead9`.**
[ExprInterface](../Vegas/Foundation/ExprInterface.lean) now derives expression
and law dependency soundness as namespace theorems. Duplicate concrete proofs
and instance fields were removed from [Simple](../Vegas/Expr/Simple.lean).
The syntax and evaluators are unchanged.

### Independent event commutation

**Finding:** The reusable commutation API was specialized to events with
distinct strategic owners. It did not expose the underlying kernel result or
an ownerless chance-event instance.

**Disposition: Addressed in `f4532ca5`.**
[KernelCommutation](../Vegas/EventGraph/KernelCommutation.lean) proves store
commutation for independent event action kernels. Stability is required only
along supported first actions and their supported intermediate configurations.
Own-recall commutation additionally requires that no player owns both events.
Chance events use the actual chance evaluator. Existing
[strategic commutation](../Vegas/EventGraph/PolicyCommutation.lean) derives from
this API with its conclusions preserved.

### Scheduler visibility at concrete backends

**Finding:** The abstract scheduler sees the full pending pool, network history,
ledger and submission counters. Some concrete backends offer less information.
A restricted command menu alone does not show that the scheduler can implement
the required probabilities from its available observation.

**Disposition: Partially addressed in `f4532ca5`.**
[ReactiveSchedulerObservation](../Interaction/ReactiveSchedulerObservation.lean)
provides exact scheduler-law factorization through an observation and preserves
the complete finite execution law for arbitrary raw player policies. The
[pending lottery](../Interaction/PendingErasureSelection.lean) instantiates it
using pending identifiers. A concrete backend still must prove that its actual
information implements the selected law. No general blockchain visibility or
cryptographic realization theorem is claimed.

### Support guarantees and probability guarantees

**Finding:** Scheduler support refinement, service coverage and information-law
preservation serve different purposes. Their composition must not implicitly
turn an allowed-command guarantee into a posterior or equilibrium theorem.

**Disposition: Addressed as an API and documentation boundary in `f4532ca5`.**
Support refinement remains in its owning modules. Exact probability-law
factorization has a separate adapter. [Compilation design](compilation-design.md)
and [module architecture](module-architecture.md) state the additional
information and payoff obligations. This separation establishes no new
backend-wide equilibrium result by itself.

### Service specification ownership

**Finding:** `SourceServiceSpec` lived in a proof-heavy local-comparison module.
Consumers needing service data consequently imported continuation comparison
proofs, obscuring the data boundary.

**Disposition: Addressed in `f4532ca5`.**
[SourceServiceSpec](../Vegas/Game/SourceServiceSpec.lean) owns the unchanged
record, instances, models, scheduler, fuel and readouts.
[LocalComparison](../Vegas/Game/SourceServiceLocalComparison.lean) imports that
data. [AsyncServiceSpec](../Vegas/Game/AsyncServiceSpec.lean) depends directly on
the specification module. No service model changed.

## Game theory APIs and terminology

GameTheory is an independent project. Its changes were checked in their
affected modules and fixtures, committed as `8bb3fc27`, and pushed on
`review/proof-api-strengthening`. VegasCore records that revision in `ff27e874`.
No independent-project-wide GameTheory validation target was imposed.

### Agreement at actual decision sites

**Finding:** Policies contain coordinates that do not affect actual decisions.
Agreement at meaningful decision sites, and independence from fallback choices,
were implicit rather than available as a coherent strategic equivalence API.

**Disposition: Addressed in GameTheory `8bb3fc27`.**
[DecisionPlan](../GameTheory/GameTheory/Protocol/DecisionPlan.lean) exposes pure
and behavioral agreement at decisions and preserves finite continuation laws.
[BehavioralTerminal](../GameTheory/GameTheory/Protocol/BehavioralTerminal.lean)
extends the result to terminal laws.

### Equilibrium invariance under fallback choices

**Finding:** Irrelevant fallback coordinates should have no strategic effect,
but the execution-law observations had not been carried through the equilibrium
interfaces.

**Disposition: Addressed in GameTheory `8bb3fc27`.**
[Strategic](../GameTheory/GameTheory/Protocol/Strategic.lean) proves compiled-law
and Nash invariance.
[Sequential](../GameTheory/GameTheory/Analysis/Protocol/Sequential.lean) proves
target-convergence, consistency, sequential-rationality and terminal-SE
equivalences, including fallback independence. The SE results retain the same
history beliefs, perturbation witness and whole-policy value guards.

### Local comparison congruence

**Finding:** Local optimality congruence asked for equality at every policy
coordinate, including alternatives outside the allowed comparison set.

**Disposition: Addressed in GameTheory `8bb3fc27`.**
[Context](../GameTheory/GameTheory/Protocol/Context.lean) requires agreement
only at the incumbent or an allowed alternative. Local optimality has the same
conclusion under this smaller hypothesis.

### Supported choice integrability

**Finding:** Supported-choice comparisons demanded integrability of more
continuations than the particular comparison used. That limited reuse with
general outcome spaces and obscured the extended-value treatment of deviations.

**Disposition: Addressed in GameTheory `8bb3fc27`, with VegasCore callers adapted
in `ff27e874`.**
[SupportedChoices](../GameTheory/GameTheory/Analysis/Protocol/SupportedChoices.lean)
derives integrability of supported branches from the incumbent mixture.
Optimality and uniform-gap results require incumbent and chosen-comparator
integrability. Other whole-policy deviations retain their value guards.
The [fixtures](../GameTheory/GameTheory/Analysis/Protocol/SupportedChoicesTest.lean)
and affected Vegas examples were updated.

### Strong Nash coalition terminology

**Finding:** Documentation could suggest unrestricted coalitions where the
formal definition uses finite coalitions.

**Disposition: Addressed in GameTheory `8bb3fc27`.**
[Equilibrium](../GameTheory/GameTheory/Core/Equilibrium.lean) states the finite
coalition scope. The equilibrium definition was not changed.

### Probability support terminology

**Finding:** GameTheory agent guidance described PMFs as finitely supported,
although ordinary PMFs do not impose that restriction.

**Disposition: Addressed in GameTheory `8bb3fc27`.**
[GameTheory guidance](../GameTheory/AGENTS.md) distinguishes ordinary PMFs from
explicit finite-support assumptions. No probability model changed.

## Proof mining and theorem strengthening

### Limiting Bayes cross identity

**Finding:** A general limiting cross identity was buried in a zero-product
exclusion proof. The narrower conclusion concealed a reusable result that
retains nonzero timing factors.

**Disposition: Addressed in `ff27e874`.**
[AsymptoticLikelihood](../GameTheoryExtensions/Analysis/Protocol/AsymptoticLikelihood.lean)
exports `AsymptoticHistoryLikelihood.belief_cross_identity`; the exclusion result
is a corollary. The identity does not require a positive limiting type weight.

### Conditional domination positivity

**Finding:** Conditional domination bounds and convergence required target
positivity even though source positivity and domination already supplied it.

**Disposition: Addressed in `ff27e874`.**
[PassageRestrictionExtension](../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean)
derives target positivity and removes the redundant caller obligation. Bounds
and convergence conclusions are preserved.

### Proportional Bayes transport positivity

**Finding:** Raw information-mass positivity was a separate premise despite
following from proportional mass equality, positive scale and source mass.

**Disposition: Addressed in `ff27e874`.**
[ProportionalBeliefTransport](../GameTheoryExtensions/Analysis/Protocol/ProportionalBeliefTransport.lean)
derives the premise internally. Callers and fixtures were adapted without
changing the transported law or conclusion.

### Generic probability domination

**Finding:** Supported bind domination and its total-variation consequence
were private inside a behavioral protocol module, despite being probability
results independent of that setting.

**Disposition: Addressed in `ff27e874`.**
[Expectation](../GameTheoryExtensions/Math/Probability/Expectation.lean) owns
the public bind-domination theorem, generalized to different input and output
carriers. [TotalVariation](../GameTheoryExtensions/Math/Probability/TotalVariation.lean)
owns the domination-to-TV result.
[SupportedChoiceDomination](../GameTheoryExtensions/Analysis/Protocol/SupportedChoiceDomination.lean)
uses those owning APIs.

### Finite plans and general outcomes

**Finding:** Positive collection over finitely many complete contingent plans
also assumed finite outcomes. The finite minimum argument needs finitely many
plans and well-defined expected charges, not a finite outcome carrier.

**Disposition: Addressed in `ff27e874`.**
[PositiveCollection](../GameTheoryExtensions/Analysis/PositiveCollection.lean)
allows arbitrary outcome types with per-plan payoff integrability. Former
finite-outcome applications obtain that integrability from existing machinery,
so the previous scope remains available.

## Additional reactive compiler findings

### Redrawing a silent sampled decision

**Finding:** In the separate generic reactive graph-policy compiler, a sampled
decision that emitted no packet was not recorded as submitted. A later
activation could redraw it. A half-probability send choice repeated twice can
produce a three-quarter eventual send probability, changing the intended law.

**Disposition: Fixed and proved in `f4532ca5`.**
[ReactivePolicy](../Vegas/Pending/ReactivePolicy.lean) recognizes authentic
silent decisions at ready owned events and suppresses redraw.
[ReactivePolicyFacts](../Vegas/Pending/ReactivePolicyFacts.lean) proves positive
posterior provenance, recall/memory alignment and retention through consistent
own-history extensions. Behavioral silence follows without assuming memory
retention as a premise.

### Conditioning and retention of intention memory

**Finding:** Append-only private memory did not itself prove that an intention
survives in every supported behavioral posterior after conditioning on recall.
Assuming that retention would leave a gap in the no-redraw argument.

**Disposition: Addressed with checked theorems in `f4532ca5`.**
[ReactiveImplementation](../Interaction/ReactiveImplementation.lean) extracts a
supported predecessor memory and a matching response transition from positive
posterior support. [ReactivePolicyFacts](../Vegas/Pending/ReactivePolicyFacts.lean)
uses that provenance to prove alignment, initialization and persistence of the
silent-decision flag. The compiled behavioral silence theorem derives the
retention property rather than requiring it.

### Original recall after an ineffective TRUE resolution

**Finding:** A silent TRUE resolution intention could become a physical
failure/FALSE without an accepting receipt, losing recall of the original
action in reconstructed policy information.

**Disposition: Fixed in `f4532ca5`, with checked local restoration facts.**
[ReactivePolicy](../Vegas/Pending/ReactivePolicy.lean) restores matching authentic
silent resolution intentions; [ReactivePolicyFacts](../Vegas/Pending/ReactivePolicyFacts.lean)
checks restoration and rejects unsupported matches. This is a policy
implementation fix within the existing model. General source-observation
reconstruction remains a separate obligation.

### Whole source correspondence for the reactive compiler

**Finding:** Equality between compiled play and a prescribed private
implementation does not establish that either realizes the source program.

**Disposition: Open, with a checked subpart.**
Posterior retention and silent-decision handling are now proved.
The explicit open obligation in [ReactivePolicy](../Vegas/Pending/ReactivePolicy.lean)
remains: reconstruct source observations and original actions, realize decisions
through protected service, and compose with compiler and unilateral-deviation
laws. The existing implementation-realization theorem is not presented as
this missing source correspondence.

### Off-path recovery optimality

**Finding:** Initialized law equality and support-safe recovery do not establish
rationality at every off-path continuation.

**Disposition: Open.**
[ReactivePolicyFacts](../Vegas/Pending/ReactivePolicyFacts.lean) proves the local
inclusion-incentive result with a fixed downstream continuation premise.
That premise still needs a service instantiation and the full continuation
argument. No native subgame-perfect or sequential-equilibrium compiler result
was inferred from initialized equality alone.

## Result scope and remaining research

The review confirmed these distinctions; they are not missing lemmas to be
replaced with new definitions.

| Scope finding | Disposition |
| --- | --- |
| The calendar theorem gives existential native-SE realization under its authentic audit and coverage assumptions. | Confirmed. The [checked compilation stack](se-compilation-stack.md) retains this scope; it does not establish arbitrary-builder preservation. |
| Native obstruction fixes one source SE before choosing an arbitrarily reliable admissible service, excludes every native SE, and supplies native SE existence. | Confirmed. The [native obstruction account](commit-reveal-research/native-se-obstruction.md) retains the actual quantifiers, strict collateral thresholds and complete-audit scope. |
| Fixed-horizon outage separation and the native incentive-and-belief obstruction are different negative results. | Confirmed. Neither is used as a substitute for the other. |
| Incremental collection and exhausted-escrow continuation rationality already have owning APIs. | Reuse guidance. They were not missing results and were not reimplemented. |
| Arbitrary asynchronous-builder SE preservation beyond the fixed calendar is unproved. | Open. The owner-controlled [async checklist](se-async-checklist.md), target and methodology remain unchanged. |
| Stronger native obstruction with smaller deposits or partial audits is unproved. | Open research. Existing negative results were not broadened by assertion. |
| A generic failed-binding source-SE extension for the full language is unproved. | Open research. The [concrete forfeiture fixture](../Vegas/Examples/LateOpeningRuntimeSourceForfeiture.lean) retains its established scope. |

## Dependency cleanup and project boundaries

The independent GameTheory Mathlib cache had 2,441 tracked modified files,
mostly line-ending churn, including thirteen `hidden` to `sealed` substitutions.
It was restored to its own existing HEAD without changing its dependency
revision. The substitutions and timestamps suggest an earlier broad rename
that reached dependency sources; the exact command and actor are not established.

The active VegasCore Mathlib cache had unchanged tracked sources but contained
an untracked nested duplicate checkout. Its duplicate directories and nested
Git metadata were moved reversibly to an ignored backup after path and
tracked-file checks. Both Mathlib working trees are clean. These are cache
cleanups, not source commits.

GameTheory remains separately managed. Its review branch was created from the
pinned revision; its independent main branch was not overwritten. Root
validation checks VegasCore targets and their transitive dependencies. Targeted
checks of changed GameTheory modules do not make the independent project a
VegasCore validation target.

## Published checkpoints and verification

| Project | Commit | Checked change |
| --- | --- | --- |
| VegasCore | `8b35ead9` | Derived expression dependency soundness. |
| GameTheory | `8bb3fc27` on `review/proof-api-strengthening` | Decision-site equilibrium invariance, localized comparison assumptions and terminology. |
| VegasCore | `ff27e874` | Likelihood, domination and collection strengthenings; GameTheory revision and caller integration. |
| VegasCore | `f4532ca5` | Service data separation, kernel and scheduler adapters, silent-decision fixes and posterior retention. |

All four checkpoints were committed and pushed. Verification of the integrated
tree passed the warning-strict VegasCore build:

```text
lake --wfail build GameTheoryExtensions GameTheoryExtensionsTests Interaction InteractionTests Vegas VegasTests Paper
```

The build completed 4,914 jobs, including the existing native uniform/source
SE obstruction and Paper. The 72 script tests, module-boundary check, central
Lean-option check, documentation-reference check, load-bearing SE-evidence
check and whitespace checks passed. Changed GameTheory modules and their
supported-choice fixture were also checked directly; the fixture dependency
closure completed 3,738 jobs.

Those checks certify the addressed changes. They do not close any item marked
open above.
