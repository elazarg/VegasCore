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
[behavioral commutation](../Vegas/EventGraph/PolicyCommutation.lean),
[whole-continuation enforcement](../GameTheoryExtensions/Analysis/Enforcement.lean),
[local comparison limit](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean),
[copied-site limit with component completion](../GameTheoryExtensions/Analysis/Protocol/CopiedSiteLimit.lean),
[consistent completion over component laws](../GameTheoryExtensions/Analysis/Protocol/ComponentCompletion.lean),
[proportional belief transport](../GameTheoryExtensions/Analysis/Protocol/ProportionalBeliefTransport.lean),
[menu restriction](../GameTheoryExtensions/Protocol/MenuRestriction.lean),
[intended game](../Vegas/Source/IntendedGame.lean),
[choices drawn from an observation-local readout](../GameTheoryExtensions/Math/Probability/ObservedChoice.lean),
[the owner's information through its own phase](../Vegas/Pending/ReactiveOwnerPhase.lean),
[permitted deviations phase by phase](../Vegas/Game/SourceServiceDeviationLaw.lean),
[whole-policy deviations under a restriction](../GameTheoryExtensions/Analysis/Protocol/RetainedDeviation.lean),
[the first-turn coupling against one deviator](../Vegas/Game/SourceServiceDeviationCoupling.lean),
and [depth-free extension](../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean).

Behavioral commutation preserves the typed store and original own recall;
native traffic and conditional beliefs need their own argument. Enforcement
uses actual gain and change in charge probability; it does not construct the
runtime's collection mechanism or assessment.

Imports expose results; they do not establish that the headline theorem uses
those results. The SE evidence check examines declaration dependencies. New
adapters need actual runtime premises, not hypotheses restating desired
posteriors, comparisons or equilibrium existence.
