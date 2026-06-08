/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Strategic
import Vegas.Frontier.Games

/-!
# Source strategic adequacy for frontier histories

This module connects the source-native strategic game to the compiled frontier
history surface.  The profile-translation theorem between source-local
strategies and frontier behavioral strategies sits above this layer; the
replay theorems here are the concrete source/graph facts that such a theorem
must use.
-/

namespace Vegas

open GameTheory
open Math.Probability

namespace WFProgram

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Initial source configuration of a checked program. -/
def sourceInitialConfig (program : WFProgram P L) : SourceConfig P L :=
  ToEventGraph.sourceStart program.core

/-- Source-native strategic game for a checked program, using the program's
own normalization proof. -/
noncomputable def sourceStrategicGame
    (program : WFProgram P L) (horizon : Nat) (cutoff : Payoff P) :
    KernelGame P :=
  sourceTraceKernelGame
    (ToEventGraph.sourceStart program.core)
    program.core.normalized horizon cutoff

@[simp] theorem sourceStrategicGame_outcomeKernel
    (program : WFProgram P L) (horizon : Nat) (cutoff : Payoff P)
    (profile : (program.sourceStrategicGame horizon cutoff).Profile) :
    (program.sourceStrategicGame horizon cutoff).outcomeKernel profile =
      SourceStrategicHistory.traceDist
        (ToEventGraph.sourceStart program.core)
        program.core.normalized profile horizon := rfl

/-- A terminal source strategic history replays into a reachable terminal
compiled graph state whose store reconstructs the terminal source
environment. -/
theorem sourceStrategicHistory_reachableConfig
    (program : WFProgram P L)
    (state :
      SourceStrategicHistory (L := L)
        (ToEventGraph.sourceStart program.core))
    (hterminal : state.history.current.IsTerminal) :
    let result := ToEventGraph.buildResult program.core
    ∃ cfg : EventGraph.ReachableConfig result.graph,
      EventGraph.Terminal result.graph cfg.1 ∧
      ToEventGraph.StoreReconstructs program.core cfg.1.store
        state.history.current := by
  have hrun :
      SourceConfig.LabeledStar
        (ToEventGraph.sourceStart program.core)
        state.history.labels state.history.current := by
    simpa [state.start_eq] using state.history.run
  simpa using
    ToEventGraph.sourceRun_reachableConfig program.core hrun hterminal

/-- Every terminal source strategic outcome in the finite-horizon source game
has a reachable terminal compiled replay.  The support hypothesis records that
the history came from the strategic kernel; the replay fact itself follows from
the executable source history stored in the outcome. -/
theorem sourceStrategicGame_support_reachableConfig
    (program : WFProgram P L) (horizon : Nat) (cutoff : Payoff P)
    (profile : (program.sourceStrategicGame horizon cutoff).Profile)
    {state :
      SourceStrategicHistory (L := L)
        (ToEventGraph.sourceStart program.core)}
    (_hsupport :
      state ∈
        ((program.sourceStrategicGame horizon cutoff).outcomeKernel
          profile).support)
    (hterminal : state.history.current.IsTerminal) :
    let result := ToEventGraph.buildResult program.core
    ∃ cfg : EventGraph.ReachableConfig result.graph,
      EventGraph.Terminal result.graph cfg.1 ∧
      ToEventGraph.StoreReconstructs program.core cfg.1.store
        state.history.current :=
  program.sourceStrategicHistory_reachableConfig state hterminal

end WFProgram

namespace ToEventGraph
namespace FrontierGameSemantics

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}
variable {program : WFProgram P L} [FiniteDomains program]

/-- Source-payoff projection of a completed behavioral checkpoint history.

This is the checkpoint-aligned source outcome surface: histories are the
canonical frontier checkpoint histories, while outcomes are read back through
the compiler's source payoff projection. -/
noncomputable def sourceCheckpointBehavioralOutcome
    (semantics : FrontierGameSemantics program)
    (history : semantics.BehavioralHistory) :
    Option (Outcome P) :=
  ToEventGraph.sourceOutcomeOptionAtHistory program.core history

/-- Source-checkpoint behavioral kernel: run the canonical behavioral frontier
history kernel, then read each completed checkpoint history through the source
payoff projection.  The strategy carrier is checkpoint-local, matching the
canonical frontier information surface rather than raw source `LStep`
linearizations. -/
noncomputable def sourceCheckpointBehavioralKernel
    (semantics : FrontierGameSemantics program)
    (profile : semantics.behavioralGame.Profile) :
    PMF (Option (Outcome P)) :=
  PMF.map (semantics.sourceCheckpointBehavioralOutcome)
    (semantics.behavioralHistoryKernel profile)

/-- Utility for source-checkpoint optional outcomes.  The `none` branch is the
bounded cutoff branch and has zero support at the completed horizon. -/
noncomputable def sourceCheckpointOptionUtility
    (_semantics : FrontierGameSemantics program) :
    Option (Outcome P) → Payoff P
  | some outcome => fun who => (outcome who : ℝ)
  | none => 0

/-- Checkpoint-aligned source behavioral game.

This is the source-facing strategic game that matches the canonical frontier
checkpoint information surface.  Its outcomes are not primitive-machine
outcomes; they are source payoff outcomes reconstructed from completed
checkpoint histories. -/
noncomputable def sourceCheckpointBehavioralGame
    (semantics : FrontierGameSemantics program) :
    KernelGame P where
  Strategy := semantics.behavioralGame.Strategy
  Outcome := Option (Outcome P)
  utility := semantics.sourceCheckpointOptionUtility
  outcomeKernel := semantics.sourceCheckpointBehavioralKernel

@[simp] theorem sourceCheckpointBehavioralGame_outcomeKernel
    (semantics : FrontierGameSemantics program)
    (profile : semantics.sourceCheckpointBehavioralGame.Profile) :
    semantics.sourceCheckpointBehavioralGame.outcomeKernel profile =
      semantics.sourceCheckpointBehavioralKernel profile := rfl

/-- The checkpoint-aligned source behavioral kernel is exactly the option-valued
completed behavioral frontier kernel. -/
theorem sourceCheckpointBehavioralKernel_eq_optionOutcomeKernel
    (semantics : FrontierGameSemantics program)
    (profile : semantics.behavioralGame.Profile) :
    semantics.sourceCheckpointBehavioralKernel profile =
      semantics.behavioral.optionOutcomeKernel profile := by
  simpa [sourceCheckpointBehavioralKernel,
    sourceCheckpointBehavioralOutcome] using
    (semantics.behavioralOptionOutcomeKernel_eq_sourceMap profile).symm

/-- The checkpoint-aligned source behavioral kernel is the completed behavioral
frontier outcome kernel observed through `some`. -/
theorem sourceCheckpointBehavioralKernel_eq_map_some_behavioralOutcomeKernel
    (semantics : FrontierGameSemantics program)
    (profile : semantics.behavioralGame.Profile) :
    semantics.sourceCheckpointBehavioralKernel profile =
      PMF.map some (semantics.behavioralGame.outcomeKernel profile) := by
  rw [semantics.sourceCheckpointBehavioralKernel_eq_optionOutcomeKernel profile]
  change
    semantics.behavioral.optionOutcomeKernel profile =
      PMF.map some
        (eraseNonePMF (semantics.behavioral.optionOutcomeKernel profile)
          (fun result hresult =>
            semantics.behavioral.optionOutcomeKernel_support_some
              profile hresult))
  rw [eraseNonePMF_map_some]

/-- Checkpoint-aligned source behavioral play and canonical behavioral
frontier play are Nash-deviation bisimilar when both are observed as optional
source payoff outcomes. -/
noncomputable def sourceCheckpointBehavioralNashDeviationBisimulation
    (semantics : FrontierGameSemantics program) :
    KernelGame.NashDeviationBisimulation
      semantics.sourceCheckpointBehavioralGame semantics.behavioralGame
      (Option (Outcome P)) where
  viewG := { observe := id }
  viewH := { observe := some }
  rel := fun sourceProfile frontierProfile =>
    sourceProfile = frontierProfile
  law_eq := by
    intro sourceProfile frontierProfile hrel
    subst frontierProfile
    dsimp [GameForm.OutcomeView.law]
    exact
      (PMF.map_id
        (semantics.sourceCheckpointBehavioralKernel sourceProfile)).trans
        (semantics.sourceCheckpointBehavioralKernel_eq_map_some_behavioralOutcomeKernel
          sourceProfile)
  simulate_target_deviation := by
    intro sourceProfile frontierProfile hrel who frontierDeviation
    subst frontierProfile
    refine ⟨frontierDeviation, ?_⟩
    dsimp [GameForm.OutcomeView.law]
    exact
      (PMF.map_id
        (semantics.sourceCheckpointBehavioralKernel
          (Function.update sourceProfile who frontierDeviation))).trans
        (semantics.sourceCheckpointBehavioralKernel_eq_map_some_behavioralOutcomeKernel
          (Function.update sourceProfile who frontierDeviation))
  simulate_source_deviation := by
    intro sourceProfile frontierProfile hrel who sourceDeviation
    subst frontierProfile
    refine ⟨sourceDeviation, ?_⟩
    dsimp [GameForm.OutcomeView.law]
    exact
      (PMF.map_id
        (semantics.sourceCheckpointBehavioralKernel
          (Function.update sourceProfile who sourceDeviation))).trans
        (semantics.sourceCheckpointBehavioralKernel_eq_map_some_behavioralOutcomeKernel
          (Function.update sourceProfile who sourceDeviation))

/-- A supported behavioral frontier history at the completion horizon replays
to a terminal source run in source order, with the same terminal store
reconstructing the source environment. -/
theorem behavioralHistory_support_sourceRun
    (semantics : FrontierGameSemantics program)
    (profile : semantics.behavioralGame.Profile)
    {history : semantics.BehavioralHistory}
    (hsupport :
      history ∈
        (semantics.behavioralHistoryKernel profile).support) :
    ∃ labels : List (Label P L),
      ∃ final : SourceConfig P L,
        SourceConfig.LabeledStar
          (ToEventGraph.sourceStart program.core) labels final ∧
        final.IsTerminal ∧
        ToEventGraph.StoreReconstructs program.core
          history.lastState.state.1.store final := by
  letI :
      ∀ player,
        Fintype
          (Option
            ((frontierRoundView
              (ToEventGraph.compile program.core)
              (frontierPresentation
                (ToEventGraph.compile program.core)
                (compile_guardLive program))
              semantics.behavioral.semantics).Act player)) := by
    intro player
    letI :
        ∀ node : Fin (ToEventGraph.compile program.core).graph.nodeCount,
          Fintype
            (L.Val
              ((ToEventGraph.compile program.core).graph.nodeRow node).ty) :=
      semantics.behavioral.nodeFintype
    dsimp [frontierRoundView, EventGraph.frontierRoundView]
    infer_instance
  have hterminal :
      EventGraph.Terminal (ToEventGraph.compile program.core).graph
        history.lastState.state.1 := by
    exact
      FrontierRoundSemantics.runDist_support_terminal_of_completionBound
        semantics.behavioral.semantics profile
        (by
          simpa [FrontierGameSemantics.behavioralHistoryKernel,
            FrontierGameSemantics.behavioral,
            FrontierGameSemantics.horizon,
            CompletedFrontierBehavioralKernelGame.view,
            CompletedFrontierKuhnGames.behavioral,
            CompletedFrontierKuhnGames.view] using hsupport)
  simpa [ToEventGraph.compile, ToEventGraph.buildResult] using
    ToEventGraph.sourceRun_of_reachableConfig program.core
      history.lastState.state hterminal

/-- Pure frontier histories replay to source runs via their degenerate
behavioral realization. -/
theorem pureHistory_support_sourceRun
    (semantics : FrontierGameSemantics program)
    (profile : semantics.pureGame.Profile)
    {history : semantics.PureHistory}
    (hsupport :
      history ∈
        (semantics.pureHistoryKernel profile).support) :
    ∃ labels : List (Label P L),
      ∃ final : SourceConfig P L,
        SourceConfig.LabeledStar
          (ToEventGraph.sourceStart program.core) labels final ∧
        final.IsTerminal ∧
        ToEventGraph.StoreReconstructs program.core
          history.lastState.state.1.store final := by
  letI :
      ∀ player,
        Fintype
          (Option
            ((frontierRoundView
              (ToEventGraph.compile program.core)
              (frontierPresentation
                (ToEventGraph.compile program.core)
                (compile_guardLive program))
              semantics.pure.semantics).Act player)) := by
    intro player
    letI :
        ∀ node : Fin (ToEventGraph.compile program.core).graph.nodeCount,
          Fintype
            (L.Val
              ((ToEventGraph.compile program.core).graph.nodeRow node).ty) :=
      semantics.pure.nodeFintype
    dsimp [frontierRoundView, EventGraph.frontierRoundView]
    infer_instance
  have hterminal :
      EventGraph.Terminal (ToEventGraph.compile program.core).graph
        history.lastState.state.1 := by
    exact
      FrontierRoundSemantics.runDist_support_terminal_of_completionBound
        semantics.pure.semantics
        ((semantics.pure.view).legalPureToBehavioral
          semantics.horizon profile)
        (by
          simpa [FrontierGameSemantics.pureHistoryKernel,
            FrontierGameSemantics.pure,
            FrontierGameSemantics.horizon,
            CompletedFrontierPureKernelGame.view,
            CompletedFrontierKuhnGames.pure,
            CompletedFrontierKuhnGames.view] using hsupport)
  simpa [ToEventGraph.compile, ToEventGraph.buildResult] using
    ToEventGraph.sourceRun_of_reachableConfig program.core
      history.lastState.state hterminal

end FrontierGameSemantics
end ToEventGraph

namespace WFProgram

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Program-facing checkpoint-aligned source behavioral game.  It uses the
canonical frontier checkpoint information surface and reads completed histories
through the compiler's source payoff projection. -/
noncomputable def sourceCheckpointBehavioralGame
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame P :=
  program.frontierSemantics.sourceCheckpointBehavioralGame

@[simp] theorem sourceCheckpointBehavioralGame_outcomeKernel
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.sourceCheckpointBehavioralGame.Profile) :
    program.sourceCheckpointBehavioralGame.outcomeKernel profile =
      program.frontierSemantics.sourceCheckpointBehavioralKernel profile := rfl

/-- Program-facing law equality: the source-checkpoint behavioral kernel is the
canonical behavioral frontier kernel observed through `some`. -/
theorem sourceCheckpointBehavioralGame_outcomeKernel_eq_map_some
    (program : WFProgram P L) [FiniteDomains program]
    (profile : program.sourceCheckpointBehavioralGame.Profile) :
    program.sourceCheckpointBehavioralGame.outcomeKernel profile =
      PMF.map some
        (program.behavioralFrontierGame.outcomeKernel profile) :=
  program.frontierSemantics
    |>.sourceCheckpointBehavioralKernel_eq_map_some_behavioralOutcomeKernel
      profile

/-- Program-facing source-checkpoint/behavioral-frontier Nash-deviation
bisimulation. -/
noncomputable def sourceCheckpointBehavioralFrontierNashDeviationBisimulation
    (program : WFProgram P L) [FiniteDomains program] :
    KernelGame.NashDeviationBisimulation
      program.sourceCheckpointBehavioralGame program.behavioralFrontierGame
      (Option (Outcome P)) :=
  program.frontierSemantics
    |>.sourceCheckpointBehavioralNashDeviationBisimulation

end WFProgram

end Vegas
