import Vegas.Core.Theorems.Graph
import Vegas.Core.Theorems.Progress
import Vegas.Core.Theorems.Visibility
import Vegas.Core.Theorems.Outcome
import Vegas.Core.Theorems.Strategy
import Vegas.Core.Theorems.Kuhn
import Vegas.Core.Theorems.FOSG
import Vegas.Core.Theorems.EFG
import Vegas.Core.Theorems.Refinement

/-!
# Paper-facing theorem index

This module states the main paper-facing claims proved by the theorem modules.
The lower theorem modules contain the detailed proof surfaces; this file keeps
the end-to-end story visible:

* checked programs compile to well-formed event graphs;
* checked guard legality gives graph/checkpoint progress;
* compiled outcomes agree with source payoffs;
* frontier/FOSG denotations preserve utility distributions;
* Kuhn realization connects behavioral play to product mixed pure play;
* runtime refinements preserve strategic utility distributions once supplied
  with an adequate strategy-indexed runtime law family.
-/

namespace Vegas

namespace WFProgram

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

omit [Fintype P] in
/-- Checked programs compile to well-formed source-free event graphs. -/
theorem claim_compiles_to_wellFormed_eventGraph
    (program : WFProgram P L) :
    (ToEventGraph.compile program.core).graph.WF :=
  program.compiledGraph_wf

omit [Fintype P] in
/-- Checked guard legality supplies progress for the primitive downset
checkpoint model. -/
theorem claim_checked_program_has_checkpoint_progress
    (program : WFProgram P L)
    {state : (ToEventGraph.primitiveDownsetCheckpointModel program).State}
    (hterminal :
      ¬ (ToEventGraph.primitiveDownsetCheckpointModel program).terminal
        state) :
    ∃ dst,
      (ToEventGraph.primitiveDownsetCheckpointModel program).allowed
        state dst :=
  program.primitiveDownsetCheckpoint_progress hterminal

omit [Fintype P] in
/-- Primitive-machine terminal outcomes agree with the source payoff
projection reconstructed from the terminal compiled graph store. -/
theorem claim_terminal_outcome_is_source_payoff
    (program : WFProgram P L)
    (state :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).State)
    (hterminal :
      (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).terminal state) :
    (ToEventGraph.PrimitiveMachine
        (ToEventGraph.compile program.core)).outcome state =
      some (ToEventGraph.sourceOutcomeAtTerminal program.core state
        (by
          simpa [ToEventGraph.PrimitiveMachine,
            ToEventGraph.primitiveMachineSpec] using hterminal)) :=
  ToEventGraph.primitiveOutcome_eq_sourceAtTerminal
    program.core state hterminal

/-- The pure completed-frontier outcome kernel is exactly the canonical run
distribution pushed through the checked program's source payoff projection. -/
theorem claim_pure_frontier_outcome_kernel_is_source_projection
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.PureFrontierProfile) :
    program.frontierSemantics.pure.optionOutcomeKernel profile =
      PMF.map
        (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
        ((program.frontierSemantics.pure.view).runDist
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core))
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core))
          ((program.frontierSemantics.pure.view).legalPureToBehavioral
            (ToEventGraph.completionBound
              (ToEventGraph.compile program.core)) profile)) :=
  program.pureFrontierOutcomeKernel_sourceMap profile

/-- The behavioral completed-frontier outcome kernel is exactly the canonical
run distribution pushed through the checked program's source payoff
projection. -/
theorem claim_behavioral_frontier_outcome_kernel_is_source_projection
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierSemantics.behavioral.optionOutcomeKernel profile =
      PMF.map
        (ToEventGraph.sourceOutcomeOptionAtHistory program.core)
        ((program.frontierSemantics.behavioral.view).runDist
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core))
          (ToEventGraph.completionBound
            (ToEventGraph.compile program.core)) profile) :=
  program.behavioralFrontierOutcomeKernel_sourceMap profile

/-- The payoff-facing FOSG denotation and the native behavioral frontier game
have the same joint utility distribution. -/
theorem claim_fosg_utility_distribution_adequacy
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierFOSGMachinePayoffHistoryKernelGame.udist
        (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
          program.frontierSemantics.behavioral.view
          program.frontierSemantics.horizon (fun _ => 0)
          profile).extend =
      program.behavioralFrontierGame.udist profile :=
  program.frontierFOSG_sourcePayoff_udist_behavioral profile

/-- The payoff-facing serialized EFG denotation has the checked program's
source payoff utility law after translating native behavioral frontier
profiles through the FOSG/EFG bridge. -/
theorem claim_efg_utility_distribution_adequacy
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.frontierPlainEFGMachinePayoffKernelGame.udist
        (program.frontierPlainEFGTranslateProfile
          (Machine.RoundView.ToFOSG.behavioralProfileOfBoundedBehavioralProfile
            program.frontierSemantics.behavioral.view
            program.frontierSemantics.horizon (fun _ => 0)
            profile).extend) =
      program.behavioralFrontierGame.udist profile :=
  Theorems.EFG.WFProgram.frontier_plain_efg_sourcePayoff_udist_behavioral
    program profile

/-- Behavioral frontier profiles induce product mixed pure frontier profiles
with the same joint utility distribution. -/
theorem claim_kuhn_behavioral_to_mixedPure_udist
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.BehavioralFrontierProfile) :
    program.mixedPureFrontierGame.udist
        (program.behavioralFrontierToMixedPure profile) =
      program.behavioralFrontierGame.udist profile :=
  program.mixedPureFrontier_udist_of_behavioral profile

/-- The Kuhn bridge is stated over the canonical frontier `RoundView`
information model.  Its information states are player event histories, and
the checked program supplies observable menus for that model. -/
theorem claim_kuhn_uses_canonical_roundView_information
    (program : WFProgram P L) [FiniteDomains program] :
    program.frontierSemantics.games.view.MenusObservable
      program.frontierSemantics.horizon :=
  program.frontierSemantics.menus

/-- Behavioral frontier strategies are local to canonical `RoundView` player
views: histories with the same player view induce the same strategy
distribution. -/
theorem claim_behavioral_strategies_are_roundView_local
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} (strategy : program.BehavioralFrontierStrategy player)
    {left right : program.BehavioralFrontierHistory}
    (hview : left.playerView player = right.playerView player) :
    strategy.1
        ((program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player left) =
      strategy.1
        ((program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player right) :=
  program.behavioralFrontierStrategy_eq_of_playerView_eq strategy hview

/-- Runtime refinements preserve the checked behavioral frontier utility
distribution once the runtime supplies an adequate strategy-indexed event-batch
law family. -/
theorem claim_runtime_refinement_preserves_behavioral_udist
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (behavioralFrontierTraceSurface program) R)
    (profile : program.BehavioralFrontierProfile) :
    bridge.implTraceGame.udist profile =
      program.behavioralFrontierGame.udist profile :=
  by
    simpa [behavioralFrontierTraceSurface] using
      bridge.implTraceGame_udist_surface profile

/-- Runtime refinements preserve the checked pure frontier utility
distribution once supplied with an adequate strategy-indexed event-batch law
family. This is the finite pure-strategy solver surface. -/
theorem claim_runtime_refinement_preserves_pure_udist
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (pureFrontierTraceSurface program) R)
    (profile : program.PureFrontierProfile) :
    bridge.implTraceGame.udist profile =
      program.pureFrontierGame.udist profile :=
  by
    simpa [pureFrontierTraceSurface] using
      bridge.implTraceGame_udist_surface profile

/-- Runtime refinements preserve the checked product mixed-pure frontier
utility distribution once supplied with an adequate strategy-indexed
event-batch law family. -/
theorem claim_runtime_refinement_preserves_mixed_pure_udist
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (mixedPureFrontierTraceSurface program) R)
    (profile : program.MixedPureFrontierProfile) :
    bridge.implTraceGame.udist profile =
      program.mixedPureFrontierGame.udist profile :=
  by
    simpa [mixedPureFrontierTraceSurface] using
      bridge.implTraceGame_udist_surface profile

/-- Under the same adequacy and bounded-utility hypotheses, behavioral
frontier Nash profiles pull back to the implementation trace game. -/
theorem claim_runtime_refinement_pulls_back_behavioral_nash
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (behavioralFrontierTraceSurface program) R)
    {CImpl CSpec CFrontier : P → ℝ}
    (hbdImpl :
      ∀ player trace,
        |Machine.eventBatchTraceUtility Impl (fun _ => 0) trace player| ≤
          CImpl player)
    (hbdSpec :
      ∀ player trace,
        |Machine.eventBatchTraceUtility
            (ToEventGraph.PrimitiveMachine
              (ToEventGraph.compile program.core))
            (fun _ => 0) trace player| ≤ CSpec player)
    (hbdFrontier :
      ∀ player outcome,
        |program.behavioralFrontierGame.utility outcome player| ≤
          CFrontier player)
    {profile : program.BehavioralFrontierProfile}
    (hNash : program.BehavioralFrontierNash profile) :
    bridge.implTraceGame.IsNash profile :=
  by
    simpa [behavioralFrontierTraceSurface] using
      bridge.implTraceGame_nash_of_surface_nash
        hbdImpl hbdSpec hbdFrontier hNash

/-- Under the same adequacy and bounded-utility hypotheses, pure frontier
Nash profiles pull back to the implementation trace game. -/
theorem claim_runtime_refinement_pulls_back_pure_nash
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (pureFrontierTraceSurface program) R)
    {CImpl CSpec CFrontier : P → ℝ}
    (hbdImpl :
      ∀ player trace,
        |Machine.eventBatchTraceUtility Impl (fun _ => 0) trace player| ≤
          CImpl player)
    (hbdSpec :
      ∀ player trace,
        |Machine.eventBatchTraceUtility
            (ToEventGraph.PrimitiveMachine
              (ToEventGraph.compile program.core))
            (fun _ => 0) trace player| ≤ CSpec player)
    (hbdFrontier :
      ∀ player outcome,
        |program.pureFrontierGame.utility outcome player| ≤
          CFrontier player)
    {profile : program.PureFrontierProfile}
    (hNash : program.PureFrontierNash profile) :
    bridge.implTraceGame.IsNash profile :=
  by
    simpa [pureFrontierTraceSurface] using
      bridge.implTraceGame_nash_of_surface_nash
        hbdImpl hbdSpec hbdFrontier hNash

/-- Under the same adequacy and bounded-utility hypotheses, product
mixed-pure frontier Nash profiles pull back to the implementation trace game. -/
theorem claim_runtime_refinement_pulls_back_mixed_pure_nash
    (program : WFProgram P L) [FiniteDomains program]
    {Impl : Machine P}
    {R :
      Machine.StochasticRefinement Impl
        (ToEventGraph.PrimitiveMachine
          (ToEventGraph.compile program.core))}
    (bridge :
      RuntimeTraceAdequacy program
        (mixedPureFrontierTraceSurface program) R)
    {CImpl CSpec CFrontier : P → ℝ}
    (hbdImpl :
      ∀ player trace,
        |Machine.eventBatchTraceUtility Impl (fun _ => 0) trace player| ≤
          CImpl player)
    (hbdSpec :
      ∀ player trace,
        |Machine.eventBatchTraceUtility
            (ToEventGraph.PrimitiveMachine
              (ToEventGraph.compile program.core))
            (fun _ => 0) trace player| ≤ CSpec player)
    (hbdFrontier :
      ∀ player outcome,
        |program.mixedPureFrontierGame.utility outcome player| ≤
          CFrontier player)
    {profile : program.MixedPureFrontierProfile}
    (hNash : program.MixedPureFrontierNash profile) :
    bridge.implTraceGame.IsNash profile :=
  by
    simpa [mixedPureFrontierTraceSurface] using
      bridge.implTraceGame_nash_of_surface_nash
        hbdImpl hbdSpec hbdFrontier hNash

end WFProgram

end Vegas
