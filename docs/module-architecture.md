# Module architecture

| Layer | Responsibility |
| --- | --- |
| GameTheory | Separately managed probability and game-theory foundation. |
| GameTheoryExtensions | Protocol limits, belief transport, enforcement and probability adapters. |
| Interaction | Signed message networks, partial observation, recall, execution and evidence. |
| Vegas.Foundation and Vegas.Expr | Typed contexts, values and expressions. |
| Vegas.Source | The source language, source information and evaluation. |
| Vegas.EventGraph | Typed dependencies, source-event execution and observations. |
| Vegas.Pending | Runtime packet submission, inclusion, deadlines and pending-message laws. |
| Vegas.Compile | Source-to-graph compiler and correspondence. |
| Vegas.Game | Strategic composition and the checked calendar SE proof. |
| Test libraries and Paper | Regressions and the calendar theorem's axiom pins. |

The [active plan](se-schedule-generalization.md) governs arbitrary-builder work.
The [calendar checklist](se-proof-checklist.md) records checked evidence. The
[archive](../archive/se-generalization/README.md) is searchable reference material,
outside the Lean source and default build roots.

Search with rg and inspect signatures with lean-defs.py before adding machinery.
Useful existing boundaries are the
[source runtime](../Vegas/Game/RevealService.lean),
[compiler observation relation](../Vegas/Compile/EventGraphObservation.lean),
[final-record verdict](../Vegas/Pending/ReactiveSettledVerdict.lean),
[asynchronous contract](../Vegas/Pending/ReactiveAsyncContract.lean),
[scheduler support refinement](../Vegas/Pending/ReactiveAsyncRefinement.lean),
[complete public traffic at raw decisions](../Interaction/ReactiveCompleteObservation.lean),
[behavioral commutation](../Vegas/EventGraph/PolicyCommutation.lean),
[whole-continuation enforcement](../GameTheoryExtensions/Analysis/Enforcement.lean),
[local comparison limit](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean),
[copied-site limit with component completion](../GameTheoryExtensions/Analysis/Protocol/CopiedSiteLimit.lean),
[consistent completion over component laws](../GameTheoryExtensions/Analysis/Protocol/ComponentCompletion.lean),
[proportional belief transport](../GameTheoryExtensions/Analysis/Protocol/ProportionalBeliefTransport.lean),
[posterior exclusion from factored reach weights](../GameTheoryExtensions/Analysis/Protocol/ConsistentLikelihood.lean),
[relative likelihood errors at unreached decisions](../GameTheoryExtensions/Analysis/Protocol/AsymptoticLikelihood.lean),
[finite-prefix scheduler agreement](../Interaction/ReactiveSchedulerPrefix.lean),
[public pending selection under packet erasure](../Interaction/PendingErasureSelection.lean),
[menu restriction](../GameTheoryExtensions/Protocol/MenuRestriction.lean),
[intended game](../Vegas/Source/IntendedGame.lean),
[choices drawn from an observation-local readout](../GameTheoryExtensions/Math/Probability/ObservedChoice.lean),
[conditional survival through bounded adaptive opportunities](../GameTheoryExtensions/Math/Probability/Survival.lean),
[survival in scheduler rounds and bounded stopping](../Interaction/ReactiveSurvival.lean),
[explicit probabilistic service in the native evaluator](../Interaction/ReactiveOutage.lean),
[fixed-horizon compiled-outcome obstruction](../Vegas/Game/ProbabilisticServiceObstruction.lean),
[final immutable disclosure readout](../Vegas/Examples/CommittedResolutionBobReadout.lean),
[actual final-disclosure continuation law](../Vegas/Examples/CommittedResolutionBobDecision.lean),
[positive collection over finite contingent plans](../GameTheoryExtensions/Analysis/PositiveCollection.lean),
[finite reliability gaps and disclosure incentives](../GameTheoryExtensions/Analysis/DisclosureReliability.lean),
[finite-deposit SE extension under a terminal audit](../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean),
[the owner's information through its own phase](../Vegas/Pending/ReactiveOwnerPhase.lean),
[permitted deviations phase by phase](../Vegas/Game/SourceServiceDeviationLaw.lean),
[whole-policy deviations under a restriction](../GameTheoryExtensions/Analysis/Protocol/RetainedDeviation.lean),
[the first-turn coupling against one deviator](../Vegas/Game/ServiceTimingCoupling.lean),
[one deviator against an arbitrary builder, phase by phase](../Vegas/Game/AsyncDeviationLaw.lean),
[one deviator up to withholding on a reveal-relaxed graph](../Vegas/Game/AsyncWithholdLaw.lean),
and [depth-free extension](../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean).

Behavioral commutation preserves the typed store and original own recall;
native traffic and conditional beliefs need their own argument. Enforcement
uses actual gain and change in charge probability; it does not construct the
runtime's collection mechanism or assessment.
Likelihood adapters require grouped weights of actual compatible histories;
absolute error bounds do not control beliefs when the observation mass also
vanishes. Erasure-independent selection supplies no service contract by itself.

Imports expose results; they do not establish that the headline theorem uses
those results. The SE evidence check examines declaration dependencies. New
adapters need actual runtime premises, not hypotheses restating desired
posteriors, comparisons or equilibrium existence.
