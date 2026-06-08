import Vegas.Frontier.Games
import Vegas.EventGraph.Batch
import Vegas.EventGraph.Fence
import Vegas.EventGraph.Frontier
import Vegas.EventGraph.Linearization

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

omit [Fintype P] in
/-- Full primitive schedules of the checked program's compiled graph all reach
the canonical completion when they write the same per-node values. This packages
the graph-confluence result at the checked-program surface. -/
theorem compiledGraph_scheduleComplete_eq_canonicalCompletion
    (program : WFProgram P L)
    (w :
      Fin (ToEventGraph.compile program.core).graph.nodeCount →
        EventGraph.TypedValue L)
    {order : List (Fin (ToEventGraph.compile program.core).graph.nodeCount)}
    (horder :
      (ToEventGraph.compile program.core).graph.IsFullOrder order) :
    (EventGraph.Config.initial
      (ToEventGraph.compile program.core).graph).scheduleComplete w order =
      EventGraph.Config.canonicalCompletion
        (ToEventGraph.compile program.core).graph w :=
  EventGraph.Config.scheduleComplete_eq_canonicalCompletion
    (ToEventGraph.compile program.core).graph w horder

omit [Fintype P] in
/-- Under an explicit readability fence, any two dependency-respecting full
linearizations of the checked program's compiled graph present a player the same
readable-output order. This is intentionally fenced; arbitrary compiled graphs
do not have universal readable-order invariance. -/
theorem compiledGraph_readableOrder_eq_of_fence
    (program : WFProgram P L)
    {who : P}
    {left right :
      List (Fin (ToEventGraph.compile program.core).graph.nodeCount)}
    (hleft :
      (ToEventGraph.compile program.core).graph.IsTopo left)
    (hright :
      (ToEventGraph.compile program.core).graph.IsTopo right)
    (hfence :
      (ToEventGraph.compile program.core).graph.Fence who) :
    (ToEventGraph.compile program.core).graph.readableOrder who left =
      (ToEventGraph.compile program.core).graph.readableOrder who right :=
  EventGraph.Graph.readableOrder_eq_of_fence hleft hright hfence

/-- Canonical pure frontier round histories are well-defined checkpoint
histories: their public view is exactly the checkpoint public view. -/
theorem pureFrontierHistory_checkpointHistory_publicView
    (program : WFProgram P L) [FiniteDomains program]
    (history : program.PureFrontierHistory) :
    (program.frontierSemantics.pure.boundedHistory_checkpointHistory
      history).publicView =
      history.publicView :=
  program.frontierSemantics.pure.boundedHistory_checkpointHistory_publicView
    history

/-- Canonical pure frontier round histories are well-defined checkpoint
histories: every player's round information state carries exactly the checkpoint
private observations, up to the frontier annotation erasure. -/
theorem pureFrontierHistory_checkpointHistory_playerView
    (program : WFProgram P L) [FiniteDomains program]
    (history : program.PureFrontierHistory) (player : P) :
    (program.frontierSemantics.pure.boundedHistory_checkpointHistory
      history).playerView player =
      (Machine.RoundView.InfoState.observationEvents
        (history.playerView player)).map Prod.fst :=
  program.frontierSemantics.pure.boundedHistory_checkpointHistory_playerView
    history player

/-- Canonical behavioral frontier round histories are well-defined checkpoint
histories: their public view is exactly the checkpoint public view. -/
theorem behavioralFrontierHistory_checkpointHistory_publicView
    (program : WFProgram P L) [FiniteDomains program]
    (history : program.BehavioralFrontierHistory) :
    (program.frontierSemantics.behavioral.boundedHistory_checkpointHistory
      history).publicView =
      history.publicView :=
  program.frontierSemantics.behavioral.boundedHistory_checkpointHistory_publicView
    history

/-- Canonical behavioral frontier round histories are well-defined checkpoint
histories: every player's round information state carries exactly the
checkpoint private observations, up to the frontier annotation erasure. -/
theorem behavioralFrontierHistory_checkpointHistory_playerView
    (program : WFProgram P L) [FiniteDomains program]
    (history : program.BehavioralFrontierHistory) (player : P) :
    (program.frontierSemantics.behavioral.boundedHistory_checkpointHistory
      history).playerView player =
      (Machine.RoundView.InfoState.observationEvents
        (history.playerView player)).map Prod.fst :=
  program.frontierSemantics.behavioral.boundedHistory_checkpointHistory_playerView
    history player

/-- The scoped schedule-confluence package that the frontier actually needs:
full primitive schedules are confluent to canonical completion, and canonical
frontier histories are well-defined checkpoint histories. -/
def ScheduleConfluenceFrontierRoundWellDefined
    (program : WFProgram P L) [FiniteDomains program] : Prop :=
  (∀
    (w :
      Fin (ToEventGraph.compile program.core).graph.nodeCount →
        EventGraph.TypedValue L)
    {order : List (Fin (ToEventGraph.compile program.core).graph.nodeCount)}
    (_horder :
      (ToEventGraph.compile program.core).graph.IsFullOrder order),
    (EventGraph.Config.initial
      (ToEventGraph.compile program.core).graph).scheduleComplete w order =
      EventGraph.Config.canonicalCompletion
        (ToEventGraph.compile program.core).graph w) ∧
  program.frontierSemantics.games.view.OperationallyCertified ∧
  (∀ history : program.PureFrontierHistory,
    (program.frontierSemantics.pure.boundedHistory_checkpointHistory
      history).publicView =
      history.publicView) ∧
  (∀ (history : program.PureFrontierHistory) (player : P),
    (program.frontierSemantics.pure.boundedHistory_checkpointHistory
      history).playerView player =
      (Machine.RoundView.InfoState.observationEvents
        (history.playerView player)).map Prod.fst) ∧
  (∀ history : program.BehavioralFrontierHistory,
    (program.frontierSemantics.behavioral.boundedHistory_checkpointHistory
      history).publicView =
      history.publicView) ∧
  (∀ (history : program.BehavioralFrontierHistory) (player : P),
    (program.frontierSemantics.behavioral.boundedHistory_checkpointHistory
      history).playerView player =
      (Machine.RoundView.InfoState.observationEvents
        (history.playerView player)).map Prod.fst)

/-- Scoped schedule-confluence package for checked programs. Primitive
full-schedule confluence is stated against the canonical completion, while the
frontier's order-sensitive information is certified through canonical
checkpoint histories rather than through arbitrary flat schedule order. -/
theorem compiledGraph_scheduleConfluence_frontierRound_wellDefined
    (program : WFProgram P L) [FiniteDomains program] :
    program.ScheduleConfluenceFrontierRoundWellDefined := by
  refine ⟨?_, program.frontierView_operationallyCertified, ?_, ?_, ?_, ?_⟩
  · intro w order horder
    exact program.compiledGraph_scheduleComplete_eq_canonicalCompletion
      w horder
  · intro history
    exact program.pureFrontierHistory_checkpointHistory_publicView history
  · intro history player
    exact program.pureFrontierHistory_checkpointHistory_playerView
      history player
  · intro history
    exact program.behavioralFrontierHistory_checkpointHistory_publicView
      history
  · intro history player
    exact program.behavioralFrontierHistory_checkpointHistory_playerView
      history player

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
