# Semantics Spine

This is a research map from the checked source language to compiled games and
runtime theorems. `Vegas.Spec` pins the corresponding definitions and flagship
claims in Lean.

## Compilation and execution

- `Vegas.WFProgram.claim_compiles_to_wellFormed_eventGraph`
- `Vegas.WFProgram.claim_checked_program_has_checkpoint_progress`
- `Vegas.WFProgram.claim_terminal_outcome_is_source_payoff`
- `Vegas.ToEventGraph.compile`
- `Vegas.ToEventGraph.PrimitiveMachine`
- `Vegas.Machine.EventBatchLaw`

The compiler produces a source-free dependency graph. Primitive execution is
schedule-agnostic; event-batch laws supply the scheduling policy.

## Native compiled game

- `program.frontierSemantics`
- `program.pureFrontierGame`
- `program.behavioralFrontierGame`
- `program.mixedPureFrontierGame`
- `program.pureFrontierOutcomeKernel_sourceMap`
- `program.behavioralFrontierOutcomeKernel_sourceMap`
- `program.claim_pure_frontier_outcome_kernel_is_source_projection`
- `program.claim_behavioral_frontier_outcome_kernel_is_source_projection`

The completed frontier game is the native strategic denotation. Its source
adequacy theorems identify terminal machine outcomes with the source payoff
projection.

## Presentations

FOSG and EFG are presentations of the native round view, not independent game
semantics.

- `program.frontierFOSG`
- `program.frontierFOSGMachinePayoffHistoryKernelGame`
- `program.frontierFOSG_payoff_udist_behavioral`
- `Vegas.Export.frontierFOSG_historyGame_udist_behavioralGame`
- `program.frontierPlainEFG`
- `program.frontierPlainEFGMachinePayoffKernelGame`
- `Vegas.Theorems.EFG.WFProgram.frontier_plain_efg_payoff_udist_behavioral`
- `Vegas.Export.frontierPlainEFG_payoffGame_udist_behavioralGame`

## Strategy transport

- `program.frontierKuhnStrategicEquivalence`
- `program.mixedPureFrontier_behavioralDeviation_to_mixedPure`
- `program.behavioralFrontier_deviation_to_mixedPure`
- `program.pureToBehavioralFrontierMorphism`
- `program.pureToBehavioralFrontierMorphism_eu`

These statements preserve outcome kernels or unilateral deviations between
strategy presentations; equilibrium results are consequences of those stronger
relations.

## Runtime trace adequacy

- `Vegas.Machine.StochasticRefinement`
- `Vegas.WFProgram.TraceGameSurface`
- `Vegas.WFProgram.TraceSpecEventBatchLaw`
- `Vegas.WFProgram.RuntimeTraceAdequacy`
- `program.claim_runtime_refinement_preserves_behavioral_udist`
- `program.claim_runtime_refinement_pulls_back_behavioral_nash`

A general runtime theorem requires a strategy-indexed specification event-batch
law because primitive traces need not reconstruct the complete frontier
information history. `Vegas.Examples.Refinement.constantPayoffSpecLaw` is a
concrete compiled-program witness, and
`Vegas.Examples.Refinement.constantPayoff_audited_preserves_behavioral_udist`
carries it through the
audited runtime without assuming such a law.

## Build-tested examples

- `Vegas.Examples.MatchingPennies`: hidden simultaneous commitments and source
  payoff adequacy.
- `Vegas.Examples.MontyHall`: staged information and FOSG/EFG adequacy.
- `Vegas.Examples.Refinement`: compiled trace law plus concrete and generic
  runtime refinements.
- `Vegas.Examples.Claims`: research claims instantiated on checked games.
