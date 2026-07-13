/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.SourceFrontier.Strategic

/-!
# Source/frontier replay facts

Replay facts connect executable source histories and completed frontier
checkpoint histories to the same compiled graph states.
-/

namespace Vegas

open GameTheory

namespace WFProgram

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every source strategic history prefix has a reachable compiled graph prefix
in canonical source order, with the current source environment reconstructed by
the compiler dictionary for the remaining source continuation. -/
theorem sourceStrategicHistory_prefixReplay
    (program : WFProgram P L)
    (state :
      SourceStrategicHistory (L := L)
        (ToEventGraph.sourceStart program.core)) :
    Nonempty
      (ToEventGraph.SourcePrefixReplay program.core
        state.history.current) := by
  have hrun :
      SourceConfig.LabeledStar
        (ToEventGraph.sourceStart program.core)
        state.history.labels state.history.current := by
    simpa [state.start_eq] using state.history.run
  exact ToEventGraph.sourcePrefixReplay_exists program.core hrun

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
        (by exact hsupport)
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
        (by exact hsupport)
  simpa [ToEventGraph.compile, ToEventGraph.buildResult] using
    ToEventGraph.sourceRun_of_reachableConfig program.core
      history.lastState.state hterminal

end FrontierGameSemantics
end ToEventGraph

end Vegas
