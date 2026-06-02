import Vegas.Frontier.Games
import Vegas.EventGraph.Batch
import Vegas.EventGraph.Frontier

/-!
# Execution and frontier facts

These theorems present the native strategic execution surface of compiled
event graphs: completed frontier rounds have primitive-event replay
certificates, and legal frontier strategies choose only available moves.
-/

namespace Vegas

namespace EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## Primitive schedule invariance -/

/-- Local diamond for two distinct available primitive graph events: executing
either event first can be completed by the other event, and the two two-event
schedules reach the same raw graph configuration. -/
theorem eventGraph_adjacent_schedule_diamond
    {G : Graph P L} (hwf : G.WF)
    {src : ReachableConfig G}
    (left right : AvailableEvent G src.1)
    (hne : left.node ≠ right.node)
    {leftNext rightNext : Config G}
    (hleft :
      leftNext ∈ (stepAvailableEvent G src.1 left).support)
    (hright :
      rightNext ∈ (stepAvailableEvent G src.1 right).support) :
    ∃ leftFinal rightFinal : ReachableConfig G,
      Nonempty (BatchStep G src leftFinal) ∧
      Nonempty (BatchStep G src rightFinal) ∧
      leftFinal.1 = rightFinal.1 :=
  BatchStep.two_event_swap hwf left right hne hleft hright

/-- The local schedule diamond preserves the public checkpoint observation and
every player's graph observation. -/
theorem eventGraph_adjacent_schedule_observation_invariant
    {G : Graph P L} (hwf : G.WF)
    {src : ReachableConfig G}
    (left right : AvailableEvent G src.1)
    (hne : left.node ≠ right.node)
    {leftNext rightNext : Config G}
    (hleft :
      leftNext ∈ (stepAvailableEvent G src.1 left).support)
    (hright :
      rightNext ∈ (stepAvailableEvent G src.1 right).support) :
    ∃ leftFinal rightFinal : ReachableConfig G,
      Nonempty (BatchStep G src leftFinal) ∧
      Nonempty (BatchStep G src rightFinal) ∧
      publicObserve G leftFinal.1 = publicObserve G rightFinal.1 ∧
      ∀ player : P,
        observe G leftFinal.1 player = observe G rightFinal.1 player :=
  BatchStep.two_event_swap_observations
    hwf left right hne hleft hright

/-- Adjacent-swap schedule invariance remains valid after an already executed
batch prefix and after replaying any later primitive batch tail. -/
theorem eventGraph_adjacent_schedule_invariant_after_prefix
    {G : Graph P L} (hwf : G.WF)
    {src mid : ReachableConfig G}
    (batchPrefix : Nonempty (BatchStep G src mid))
    (left right : AvailableEvent G mid.1)
    (hne : left.node ≠ right.node)
    {leftNext rightNext : Config G}
    (hleft :
      leftNext ∈ (stepAvailableEvent G mid.1 left).support)
    (hright :
      rightNext ∈ (stepAvailableEvent G mid.1 right).support) :
    ∃ leftFinal rightFinal : ReachableConfig G,
      Nonempty (BatchStep G mid leftFinal) ∧
      Nonempty (BatchStep G mid rightFinal) ∧
      leftFinal.1 = rightFinal.1 ∧
      ∀ {dst : ReachableConfig G}, BatchStep G leftFinal dst →
        ∃ dst' : ReachableConfig G,
          Nonempty (BatchStep G src dst) ∧
          Nonempty (BatchStep G src dst') ∧
          publicObserve G dst'.1 = publicObserve G dst.1 ∧
          (∀ player : P,
            observe G dst'.1 player = observe G dst.1 player) :=
  BatchStep.two_event_swap_after_prefix_with_tail_observations
    hwf batchPrefix left right hne hleft hright

end EventGraph

namespace WFProgram

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Every supported canonical frontier round has an executable primitive-event
batch certificate. -/
theorem frontierRounds_operationallyCertified
    (program : WFProgram P L) [FiniteDomains program] :
    program.frontierSemantics.games.view.OperationallyCertified :=
  program.frontierView_operationallyCertified

omit [Fintype P] in
/-- Checked programs inherit the graph-level adjacent-schedule diamond for
their compiled primitive event graph. -/
theorem compiledGraph_adjacent_schedule_diamond
    (program : WFProgram P L)
    {src : EventGraph.ReachableConfig
      (ToEventGraph.compile program.core).graph}
    (left right :
      EventGraph.AvailableEvent
        (ToEventGraph.compile program.core).graph src.1)
    (hne : left.node ≠ right.node)
    {leftNext rightNext :
      EventGraph.Config (ToEventGraph.compile program.core).graph}
    (hleft :
      leftNext ∈
        (EventGraph.stepAvailableEvent
          (ToEventGraph.compile program.core).graph src.1 left).support)
    (hright :
      rightNext ∈
        (EventGraph.stepAvailableEvent
          (ToEventGraph.compile program.core).graph src.1 right).support) :
    ∃ leftFinal rightFinal :
        EventGraph.ReachableConfig
          (ToEventGraph.compile program.core).graph,
      Nonempty
        (EventGraph.BatchStep
          (ToEventGraph.compile program.core).graph src leftFinal) ∧
      Nonempty
        (EventGraph.BatchStep
          (ToEventGraph.compile program.core).graph src rightFinal) ∧
      leftFinal.1 = rightFinal.1 :=
  EventGraph.eventGraph_adjacent_schedule_diamond
    (G := (ToEventGraph.compile program.core).graph)
    (ToEventGraph.compile program.core).graphWF
    left right hne hleft hright

omit [Fintype P] in
/-- Checked programs inherit graph-level public/private observation invariance
for adjacent swaps of independent primitive events. -/
theorem compiledGraph_adjacent_schedule_observation_invariant
    (program : WFProgram P L)
    {src : EventGraph.ReachableConfig
      (ToEventGraph.compile program.core).graph}
    (left right :
      EventGraph.AvailableEvent
        (ToEventGraph.compile program.core).graph src.1)
    (hne : left.node ≠ right.node)
    {leftNext rightNext :
      EventGraph.Config (ToEventGraph.compile program.core).graph}
    (hleft :
      leftNext ∈
        (EventGraph.stepAvailableEvent
          (ToEventGraph.compile program.core).graph src.1 left).support)
    (hright :
      rightNext ∈
        (EventGraph.stepAvailableEvent
          (ToEventGraph.compile program.core).graph src.1 right).support) :
    ∃ leftFinal rightFinal :
        EventGraph.ReachableConfig
          (ToEventGraph.compile program.core).graph,
      Nonempty
        (EventGraph.BatchStep
          (ToEventGraph.compile program.core).graph src leftFinal) ∧
      Nonempty
        (EventGraph.BatchStep
          (ToEventGraph.compile program.core).graph src rightFinal) ∧
      EventGraph.publicObserve
          (ToEventGraph.compile program.core).graph leftFinal.1 =
        EventGraph.publicObserve
          (ToEventGraph.compile program.core).graph rightFinal.1 ∧
      ∀ player : P,
        EventGraph.observe
            (ToEventGraph.compile program.core).graph leftFinal.1 player =
          EventGraph.observe
            (ToEventGraph.compile program.core).graph rightFinal.1 player :=
  EventGraph.eventGraph_adjacent_schedule_observation_invariant
    (G := (ToEventGraph.compile program.core).graph)
    (ToEventGraph.compile program.core).graphWF
    left right hne hleft hright

/-- Pure frontier strategies choose available moves at reachable completed
frontier histories. -/
theorem pureFrontierStrategy_available
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} (strategy : program.PureFrontierStrategy player)
    (history : program.PureFrontierHistory) :
    strategy.1
        ((program.frontierSemantics.pure.view).reachableInfoStateOfHistory
            program.frontierSemantics.horizon player history) ∈
      (program.frontierSemantics.pure.view).boundedAvailableMoves
          program.frontierSemantics.horizon history player :=
  program.pureFrontierStrategy_chooses_available strategy history

/-- Behavioral frontier strategies assign positive probability only to
available moves at reachable completed frontier histories. -/
theorem behavioralFrontierStrategy_available
    (program : WFProgram P L) [FiniteDomains program]
    {player : P} (strategy : program.BehavioralFrontierStrategy player)
    (history : program.BehavioralFrontierHistory)
    {move : Option ((program.frontierSemantics.behavioral.view).Act player)}
    (hmove :
      move ∈
        (strategy.1
          ((program.frontierSemantics.behavioral.view).reachableInfoStateOfHistory
              program.frontierSemantics.horizon player history)).support) :
    move ∈
      (program.frontierSemantics.behavioral.view).boundedAvailableMoves
          program.frontierSemantics.horizon history player :=
  program.behavioralFrontierStrategy_supports_available
    strategy history hmove

end WFProgram

end Vegas
