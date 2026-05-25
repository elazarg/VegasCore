# Semantics Spine

This file is an implementation-facing map from Lean definitions and theorems to
the paper-facing semantic claims. It records the current semantic surface:
checked programs, source-free event graphs, native frontier games,
presentation bridges, and runtime refinement.

## Core Compilation

Checked programs compile to source-free event graphs.

- `Vegas.WFProgram.claim_compiles_to_wellFormed_eventGraph`
- `Vegas.WFProgram.claim_checked_program_has_checkpoint_progress`
- `Vegas.WFProgram.claim_terminal_outcome_is_source_payoff`

The graph is the dependency object. Source names and source syntax are compiler
inputs, not graph identity.

## Source Visibility

Source payoffs are public, and source commit guards are typed over the acting
player's view.

- `Vegas.evalPayoffs_eq_of_erasePubEnv_eq`
- `Vegas.commitGuard_eval_eq_of_viewEnv_eq`
- `Vegas.commitGuard_eval_eq_of_visible_values_eq`

## Frontier Game

The native strategic denotation is the completed frontier game built from the
compiled event graph.

- `program.pureFrontierGame`
- `program.behavioralFrontierGame`
- `program.mixedPureFrontierGame`
- `program.frontierSemantics`

Source payoff adequacy enters at the completed frontier kernel:

- `program.pureFrontierOutcomeKernel_sourceMap`
- `program.behavioralFrontierOutcomeKernel_sourceMap`
- `program.claim_pure_frontier_outcome_kernel_is_source_projection`
- `program.claim_behavioral_frontier_outcome_kernel_is_source_projection`

## FOSG Denotation

FOSG is the standard behavioral game-form presentation for checked programs.
The payoff-facing FOSG history kernel uses FOSG histories, but reads utility
from the final compiled machine payoff. For checked programs, separate source
adequacy theorems identify that compiled payoff with the source payoff
projection on completed runs.

- `program.frontierFOSG`
- `program.frontierFOSGMachinePayoffHistoryKernelGame`
- `program.frontierFOSG_sourcePayoff_udist_behavioral`
- `program.frontierFOSG_sourcePayoff_udist_restrictedBehavioral`
- `Vegas.Export.frontierFOSG`
- `Vegas.Export.frontierFOSG_sourcePayoffGame_udist_behavioralGame`

For source-independent graph users, the generic path is the graph
`frontierRoundView` plus the generic `Machine.RoundView` FOSG/EFG bridges.
There is no separate graph-native export facade.

- `Vegas.EventGraph.frontierRoundView`
- `Vegas.GameBridge.FOSG.FromRoundView`
- `Vegas.GameBridge.EFG.FromRoundView`

## EFG Presentation

EFG is a serialized presentation layer for finite bounded round views. It is
not the primary strategic denotation, but its payoff kernel is proved to
preserve the same source payoff utility law.

- `program.frontierPlainEFG`
- `program.frontierPlainEFGMachinePayoffKernelGame`
- `program.frontier_plain_efg_sourcePayoff_udist_behavioral`
- `program.frontier_plain_efg_sourcePayoff_udist_pure`
- `Vegas.Export.frontierPlainEFG`
- `Vegas.Export.frontierPlainEFG_efgOutcomeKernel_sourceFOSG`
- `Vegas.Export.frontierPlainEFG_efgUdist_sourceFOSG`
- `Vegas.Export.frontierPlainEFG_efgUdist_payoffGame`
- `Vegas.Export.frontierPlainEFG_payoffGame_udist_sourceFOSG`
- `Vegas.Export.frontierPlainEFG_sourcePayoffGame_udist_behavioralGame`
- `Vegas.Export.frontierPlainEFG_sourcePayoffGame_udist_pureGame`
- `Vegas.Export.frontierPlainEFGMixedPureProfile`
- `Vegas.Export.frontierPlainEFG_sourcePayoffGame_udist_mixedPureGame`

For source-independent graph users, the corresponding finite-state
serialization hooks are the generic RoundView/EFG bridge:

- `Vegas.EFGBridge.DecisionSpineThenChance`
- `Vegas.EFGBridge.DecisionSpineThenChance.choosePlayersFrom`
- `Vegas.EFGBridge.DecisionSpineThenChance.fromHistory_succ_nonterminal`
- `Vegas.EFGBridge.FullTreeShape`
- `Vegas.EFGBridge.FullTreeShape.fromHistory`

## Kuhn

Kuhn realization is stated at the checked-program frontier level, where players
can reason about the code-derived game surface.

- `program.frontierCompleteOutcomeKuhn`
- `program.frontierKuhnStrategicEquivalence`
- `program.mixedPureFrontier_behavioralDeviation_to_mixedPure`
- `program.mixedPureFrontier_mixedDeviation_to_behavioral`
- `program.behavioralFrontier_deviation_to_mixedPure`
- `program.mixedPureFrontier_udist_of_behavioral`
- `program.behavioralFrontier_to_correlatedPure_kernel`
- `program.behavioralFrontier_to_correlatedPure_eu_of_bounded`
- `program.behavioralToMixedPureFrontierNashDeviationSimulation`
- `program.canonicalMixedPureToBehavioralFrontierDeviationSimulation`
- `program.claim_kuhn_uses_canonical_roundView_information`
- `program.claim_behavioral_strategies_are_roundView_local`

The main non-equilibrium package is
`program.frontierKuhnStrategicEquivalence`: it records the canonical
mixed-pure-to-behavioral and behavioral-to-mixed-pure translations, outcome
kernel preservation in both directions, and one-player deviation matching
across the two strategy presentations. The Nash-safe statements are corollaries
of this deviation-level content; they are not the primary Kuhn formulation.
The information model is the canonical completed-frontier `RoundView`:
behavioral strategies are functions of player views in that model.

For source-independent graph users, construct the shared round view with
`Vegas.EventGraph.frontierRoundView`. The Kuhn facts live on
`Vegas.Machine.RoundView`; graph users apply that generic API to the resulting
view rather than using graph-specific Kuhn wrappers:

- `Vegas.Machine.RoundView.kuhn_mixed_to_behavioral_optionOutcome`
- `Vegas.Machine.RoundView.kuhn_behavioral_to_mixedPure_optionOutcome`
- `Vegas.Machine.RoundView.mixedPureToBehavioralProfile_optionOutcome`
- `Vegas.Machine.RoundView.mixedPureToBehavioralProfile_unilateral_deviation_optionOutcome`

## Runtime Refinement

Runtime refinement relates a lower operational machine to the primitive
EventGraph machine. Strategic preservation requires an additional
strategy-indexed adequacy bridge saying the specification primitive event-batch
law realizes the checked frontier trace distribution and the implementation law
is compatible with it.

- `Machine.StochasticRefinement`
- `Machine.StochasticRefinement.EventBatchLawFamilyLift`
- `Machine.audited.refinement`
- `Machine.audited.liftEventBatchLawFamily`
- `program.behavioralFrontierEventBatchTraceKernel`
- `program.behavioralFrontierTraceSurface`
- `program.pureFrontierTraceSurface`
- `program.mixedPureFrontierTraceSurface`
- `WFProgram.TraceSpecEventBatchLaw`
- `specLaw.traceGame_udist_surface`
- `WFProgram.RuntimeTraceAdequacy`
- `WFProgram.RuntimeTraceAdequacy.identity`
- `WFProgram.RuntimeTraceAdequacy.audited`
- `bridge.implTraceGame_udist_surface`
- `bridge.implTraceGame_nash_of_surface_nash`
- `program.claim_runtime_refinement_preserves_behavioral_udist`
- `program.claim_runtime_refinement_pulls_back_behavioral_nash`

The trace-adequate specification event-batch law is an explicit backend or
analysis obligation. The primitive machine trace type does not by itself carry
enough round-view strategy history to construct that law automatically.

## Build-Tested Examples

The default `lake build` target imports `VegasTests`, which imports
`Vegas.Examples`. The current example map is:

| Module | Semantic Path |
| --- | --- |
| `Vegas.Examples.DependencySemantics` | source-to-EventGraph dependency and validation checks |
| `Vegas.Examples.MatchingPennies` | simultaneous hidden-commit game and finite frontier surface |
| `Vegas.Examples.MontyHall` | staged information, reveals, FOSG/EFG payoff adequacy |
| `Vegas.Examples.SolutionConcepts` | solution-concept wrappers and Vickrey truthfulness smoke tests |
| `Vegas.Examples.EFGTranslation` | serialized FOSG-to-EFG decision-spine shape |
| `Vegas.Examples.Claims` | paper-facing claims instantiated on checked games |
| `Vegas.Examples.Refinement` | identity and encoded non-identity machine refinement checks |

## Solution Concepts

The checked-program solution-concept surface includes EU-specialized
predicates and preference-parametric hooks:

- `program.PureFrontierNashFor`
- `program.PureFrontierBestResponseFor`
- `program.PureFrontierDominantFor`
- `program.PureFrontierCorrelatedEqFor`
- `program.PureFrontierCoarseCorrelatedEqFor`
- `program.BehavioralFrontierNashFor`
- `program.BehavioralFrontierBestResponseFor`
- `program.BehavioralFrontierDominantFor`
- `program.BehavioralFrontierCorrelatedEqFor`
- `program.BehavioralFrontierCoarseCorrelatedEqFor`

The theorem index records that the ordinary frontier predicates are exactly
the corresponding `*For` predicates instantiated with `PureFrontierEuPref`,
`PureFrontierEuStrictPref`, `BehavioralFrontierEuPref`, and
`BehavioralFrontierEuStrictPref`.
