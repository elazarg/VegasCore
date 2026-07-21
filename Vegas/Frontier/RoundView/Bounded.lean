import Vegas.Frontier.RoundView.Canonical

/-!
# Bounded frontier round semantics and outcome support

The `FrontierRoundSemantics` namespace: bounded-step availability, checkpoint
steps, terminality at the completion bound, and outcome-support theorems, plus
the `eraseNonePMF` option-erasure helpers.
-/

namespace Vegas

namespace ToEventGraph

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

namespace FrontierRoundSemantics

variable {compiled : CompiledProgram P L}
variable {presentation : EventGraph.CheckpointPresentation compiled.graph}

private noncomputable abbrev View
    (semantics : FrontierRoundSemantics compiled presentation) :
    (PrimitiveMachine compiled).RoundView :=
  frontierRoundView compiled presentation semantics

private theorem boundedStep_transition_support
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (step : (View semantics).BoundedStep horizon) :
    (View semantics).transition step.src.state
        ((View semantics).boundedActionToAction horizon step.src step.act)
        step.dst.state ≠ 0 := by
  classical
  let view := View semantics
  have hmem :
      step.dst ∈
        (view.boundedTransition horizon step.src step.act).support := by
    exact (PMF.mem_support_iff _ _).2 step.support
  rw [Machine.RoundView.boundedTransition] at hmem
  rcases (PMF.mem_support_map_iff _ _ _).mp hmem with
    ⟨next, hnext, hdst⟩
  have hstate : next = step.dst.state := by
    simpa [Machine.BoundedState.succ] using congrArg
      (fun bounded : (PrimitiveMachine compiled).BoundedState horizon =>
        bounded.state) hdst
  rw [← hstate]
  exact (PMF.mem_support_iff _ _).1 hnext

private theorem boundedStep_eventBatch_eq_semantics
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (step : (View semantics).BoundedStep horizon) :
    (View semantics).eventBatch step.src.state step.act.1 step.dst.state =
      semantics.eventBatch step.src.state
        ((View semantics).boundedActionToAction horizon step.src step.act)
        step.dst.state := by
  classical
  let action :=
    (View semantics).boundedActionToAction horizon step.src step.act
  change
    (if hlegal :
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) step.src.state step.act.1 then
      semantics.eventBatch step.src.state ⟨step.act.1, hlegal⟩
        step.dst.state
    else []) =
      semantics.eventBatch step.src.state action step.dst.state
  have hlegal :
      JointActionLegal (FrontierAct compiled)
        (frontierActive compiled)
        (PrimitiveMachine compiled).terminal
        (frontierAvailableActions compiled) step.src.state step.act.1 := by
    exact action.2
  rw [dif_pos hlegal]
  have haction :
      (⟨step.act.1, hlegal⟩ :
        {a : JointAction (FrontierAct compiled) //
          JointActionLegal (FrontierAct compiled)
            (frontierActive compiled)
            (PrimitiveMachine compiled).terminal
            (frontierAvailableActions compiled) step.src.state a}) =
        action := by
    exact Subtype.ext rfl
  exact congrArg
    (fun legalAction =>
      semantics.eventBatch step.src.state legalAction step.dst.state)
    haction

/-- The primitive event batch recorded by a supported bounded frontier round
really is an available primitive machine run from the source checkpoint to the
destination checkpoint. -/
theorem boundedStep_eventBatch_availableRun
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (step : (View semantics).BoundedStep horizon) :
    (PrimitiveMachine compiled).AvailableRunFrom step.src.state
      ((View semantics).eventBatch step.src.state step.act.1 step.dst.state)
      step.dst.state := by
  rw [boundedStep_eventBatch_eq_semantics semantics step]
  exact
    (semantics.certifies
      ((View semantics).boundedActionToAction horizon step.src step.act)
      (boundedStep_transition_support semantics step)).availableRun

/-- The frontier round view is operationally certified: every supported
strategic round transition records a primitive event batch that replays that
transition on the underlying protocol machine. -/
theorem view_operationallyCertified
    (semantics : FrontierRoundSemantics compiled presentation) :
    (View semantics).OperationallyCertified := by
  classical
  intro state action dst hsupport
  let hlegal :
      JointActionLegal (FrontierAct compiled)
        (frontierActive compiled)
        (PrimitiveMachine compiled).terminal
        (frontierAvailableActions compiled) state action.1 := by
    exact action.2
  let action' :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a} :=
    ⟨action.1, hlegal⟩
  have hbatch :
      (View semantics).eventBatch state action.1 dst =
        semantics.eventBatch state action' dst := by
    change
      (if hlegal :
          JointActionLegal (FrontierAct compiled)
            (frontierActive compiled)
            (PrimitiveMachine compiled).terminal
            (frontierAvailableActions compiled) state action.1 then
        semantics.eventBatch state ⟨action.1, hlegal⟩ dst
      else []) =
        semantics.eventBatch state action' dst
    rw [dif_pos hlegal]
    rfl
  have hsupport' : semantics.transition state action' dst ≠ 0 := by
    exact hsupport
  rw [hbatch]
  exact (semantics.certifies action' hsupport').availableRun

/-- The primitive event batch recorded by a supported bounded frontier round
faithfully contains the strategic commit choices selected by that round's
joint action. -/
theorem boundedStep_eventBatch_realizesAction
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (step : (View semantics).BoundedStep horizon) :
    FrontierBatchRealizesAction compiled step.act.1
      ((View semantics).eventBatch step.src.state step.act.1
        step.dst.state) := by
  rw [boundedStep_eventBatch_eq_semantics semantics step]
  exact
    (semantics.certifies
      ((View semantics).boundedActionToAction horizon step.src step.act)
      (boundedStep_transition_support semantics step)).realizesAction

/-- The recorded primitive event batch for a supported bounded frontier round
is also a graph-level checkpoint batch certificate. -/
theorem boundedStep_checkpointStep
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (step : (View semantics).BoundedStep horizon) :
    EventGraph.CheckpointStep compiled.graph
      step.src.state step.dst.state :=
  EventGraph.ToMachine.checkpointStep_of_availableRunFrom
    (primitiveMachineSpec compiled)
    (boundedStep_eventBatch_availableRun semantics step)

/-- Every supported bounded frontier round follows the attached checkpoint
presentation policy. -/
theorem boundedStep_allowed
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (step : (View semantics).BoundedStep horizon) :
    presentation.policy.allowed step.src.state step.dst.state := by
  exact
    (semantics.certifies
      ((View semantics).boundedActionToAction horizon step.src step.act)
      (boundedStep_transition_support semantics step)).allowed

/-- Every supported bounded frontier round strictly advances the completed-node
downset of the underlying graph state. -/
theorem boundedStep_done_ssubset
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (step : (View semantics).BoundedStep horizon) :
    step.src.state.1.done ⊂ step.dst.state.1.done :=
  presentation.policy.advances
    (boundedStep_allowed semantics step)

private theorem stepChain_done_card_add_length_le
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat} :
    ∀ {start : (PrimitiveMachine compiled).BoundedState horizon}
      {steps : List ((View semantics).BoundedStep horizon)},
      (View semantics).StepChainFrom horizon start steps →
        start.state.1.done.card + steps.length ≤
          ((View semantics).lastStateFrom horizon start steps).state.1.done.card
  | start, [], _hchain => by
      simp [Machine.RoundView.lastStateFrom]
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      subst hsrc
      have hhead :
          step.src.state.1.done.card + 1 ≤
            step.dst.state.1.done.card :=
        Nat.succ_le_of_lt
          (Finset.card_lt_card
            (boundedStep_done_ssubset semantics step))
      have htailCard :
          step.dst.state.1.done.card + steps.length ≤
            ((View semantics).lastStateFrom horizon step.dst
              steps).state.1.done.card :=
        stepChain_done_card_add_length_le semantics htail
      simp [Machine.RoundView.lastStateFrom]
      omega

/-- A certified frontier history with one round per graph node must be
terminal. The proof uses only strict completed-downset progress; it is the
history-level totality fact behind the default `completionBound`. -/
theorem boundedHistory_terminal_of_length_completionBound
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (history : (View semantics).BoundedHistory horizon)
    (hlen : history.steps.length = completionBound compiled) :
    EventGraph.Terminal compiled.graph history.lastState.state.1 := by
  have hcardGe :
      compiled.graph.nodeCount ≤ history.lastState.state.1.done.card := by
    have hchain :=
      stepChain_done_card_add_length_le
        semantics history.chain
    have hinit :
        ((Machine.BoundedState.init
          (PrimitiveMachine compiled) horizon).state.1.done.card) = 0 := by
      simp [Machine.BoundedState.init, PrimitiveMachine,
        EventGraph.PrimitiveMachineOf,
        EventGraph.ToMachine.primitiveMachine, EventGraph.Config.initial]
    rw [← Machine.RoundView.BoundedHistory.lastState] at hchain
    rw [hinit, hlen] at hchain
    simpa [completionBound] using hchain
  have hcardLe :
      history.lastState.state.1.done.card ≤ compiled.graph.nodeCount := by
    calc
      history.lastState.state.1.done.card ≤
          (Finset.univ :
            Finset (Fin compiled.graph.nodeCount)).card :=
        Finset.card_le_card (by intro node _hnode; simp)
      _ = compiled.graph.nodeCount := by simp
  have hcard :
      history.lastState.state.1.done.card =
        (Finset.univ : Finset (Fin compiled.graph.nodeCount)).card := by
    apply le_antisymm
    · simpa using hcardLe
    · simpa using hcardGe
  have hdone :
      history.lastState.state.1.done =
        (Finset.univ : Finset (Fin compiled.graph.nodeCount)) := by
    apply Finset.eq_univ_of_card
    exact hcard
  intro node
  rw [hdone]
  exact Finset.mem_univ node

/-- Any supported default-length run of a certified frontier view ends in a
graph-terminal checkpoint. If the bounded runner stops early, it stopped at a
real machine terminal state; if it uses all bounded rounds, strict downset
progress completes every graph node. -/
theorem runDist_support_terminal_of_completionBound
    (semantics : FrontierRoundSemantics compiled presentation)
    [∀ player, Fintype (Option ((View semantics).Act player))]
    (β :
      (View semantics).BoundedBehavioralProfile
        (completionBound compiled))
    {history :
      (View semantics).BoundedHistory (completionBound compiled)}
    (hsupport :
      history ∈
        ((View semantics).runDist
          (completionBound compiled) (completionBound compiled) β).support) :
    EventGraph.Terminal compiled.graph history.lastState.state.1 := by
  classical
  have hterminalOrLength :=
    Machine.RoundView.BoundedHistory.runDistFrom_support_terminal_or_length_ge
        (View semantics) (completionBound compiled) β
        (completionBound compiled)
        (Machine.RoundView.BoundedHistory.nil
          (View semantics) (completionBound compiled))
        history
        (by
          simpa [Machine.RoundView.runDist] using hsupport)
  rcases hterminalOrLength with hboundedTerminal | hlengthGe
  · rcases hboundedTerminal with hmachineTerminal | hdepth
    · change EventGraph.Terminal compiled.graph
        history.lastState.state.1 at hmachineTerminal
      exact hmachineTerminal
    · have hlenGe :
          completionBound compiled ≤ history.steps.length := by
        rw [← (View semantics).history_depth
          (completionBound compiled) history]
        exact hdepth
      have hlenLe :
          history.steps.length ≤ completionBound compiled :=
        (View semantics).history_length_le
          (completionBound compiled) history
      exact
        boundedHistory_terminal_of_length_completionBound
          semantics history (le_antisymm hlenLe hlenGe)
  · have hlenGe :
        completionBound compiled ≤ history.steps.length := by
      simpa using hlengthGe
    have hlenLe :
        history.steps.length ≤ completionBound compiled :=
      (View semantics).history_length_le
        (completionBound compiled) history
    exact
      boundedHistory_terminal_of_length_completionBound
        semantics history (le_antisymm hlenLe hlenGe)

/-- Default-length behavioral outcome kernels for certified frontier views
never support `none`. -/
theorem boundedOutcomeFromBehavioral_support_some_completionBound
    (semantics : FrontierRoundSemantics compiled presentation)
    [∀ player, Fintype (Option ((View semantics).Act player))]
    (β :
      (View semantics).BoundedBehavioralProfile
        (completionBound compiled))
    {result : Option (PrimitiveMachine compiled).Outcome}
    (hsupport :
      result ∈
        ((View semantics).boundedOutcomeFromBehavioral
          (completionBound compiled) β
          (completionBound compiled)).support) :
    ∃ outcome, result = some outcome := by
  classical
  rcases (PMF.mem_support_map_iff _ _ _).mp hsupport with
    ⟨trace, htrace, hresult⟩
  rcases (PMF.mem_support_map_iff _ _ _).mp htrace with
    ⟨history, hhistory, htraceEq⟩
  have hterminal :
      EventGraph.Terminal compiled.graph history.lastState.state.1 :=
    runDist_support_terminal_of_completionBound
      semantics β (by
        simpa [Machine.RoundView.boundedEventBatchTraceFromBehavioral]
          using hhistory)
  have hresultEq :
      (PrimitiveMachine compiled).outcome history.lastState.state = result := by
    rw [← htraceEq] at hresult
    simpa [Machine.RoundView.boundedHistoryTrace] using hresult
  rcases EventGraph.ToMachine.terminalPayoffTotal
      (primitiveMachineSpec compiled) history.lastState.state hterminal with
    ⟨outcome, houtcomeEval⟩
  have houtcome :
      (PrimitiveMachine compiled).outcome history.lastState.state =
        some outcome := by
    rw [EventGraph.ToMachine.primitiveMachine_outcome_terminal
      (primitiveMachineSpec compiled) hterminal]
    exact houtcomeEval
  rw [houtcome] at hresultEq
  exact ⟨outcome, hresultEq.symm⟩

/-- Default-length pure outcome kernels for certified frontier views never
support `none`. -/
theorem boundedOutcomeFromPure_support_some_completionBound
    (semantics : FrontierRoundSemantics compiled presentation)
    [∀ player, Fintype (Option ((View semantics).Act player))]
    (π :
      (View semantics).BoundedPureProfile
        (completionBound compiled))
    {result : Option (PrimitiveMachine compiled).Outcome}
    (hsupport :
      result ∈
        ((View semantics).boundedOutcomeFromPure
          (completionBound compiled) π
          (completionBound compiled)).support) :
    ∃ outcome, result = some outcome := by
  simpa [Machine.RoundView.boundedOutcomeFromPure] using
    boundedOutcomeFromBehavioral_support_some_completionBound
      semantics
      ((View semantics).legalPureToBehavioral
        (completionBound compiled) π)
      hsupport

private theorem stepChain_eventBatches_availableRun
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat} :
    ∀ {start : (PrimitiveMachine compiled).BoundedState horizon}
      {steps : List ((View semantics).BoundedStep horizon)},
      (View semantics).StepChainFrom horizon start steps →
        (PrimitiveMachine compiled).AvailableRunBatchesFrom start.state
          (steps.map fun step =>
            (View semantics).eventBatch step.src.state step.act.1
              step.dst.state)
          ((View semantics).lastStateFrom horizon start steps).state
  | start, [], _hchain => by
      exact .nil start.state
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      have hhead :
          (PrimitiveMachine compiled).AvailableRunFrom start.state
            ((View semantics).eventBatch step.src.state step.act.1
              step.dst.state)
            step.dst.state := by
        subst hsrc
        exact boundedStep_eventBatch_availableRun semantics step
      have htailRun :
          (PrimitiveMachine compiled).AvailableRunBatchesFrom step.dst.state
            (steps.map fun step =>
              (View semantics).eventBatch step.src.state step.act.1
                step.dst.state)
            ((View semantics).lastStateFrom horizon step.dst steps).state :=
        stepChain_eventBatches_availableRun semantics htail
      exact .cons hhead htailRun

private noncomputable def stepChain_checkpointHistory
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat} :
    ∀ {start : (PrimitiveMachine compiled).BoundedState horizon}
      {steps : List ((View semantics).BoundedStep horizon)},
      (View semantics).StepChainFrom horizon start steps →
        presentation.History start.state
          ((View semantics).lastStateFrom horizon start steps).state
  | start, [], _hchain => by
      exact .nil start.state
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      subst hsrc
      let head : presentation.History step.src.state step.dst.state :=
        .snoc (.nil step.src.state) (boundedStep_allowed semantics step)
      let tail : presentation.History step.dst.state
          ((View semantics).lastStateFrom horizon step.dst steps).state :=
        stepChain_checkpointHistory semantics htail
      exact head.append tail

private theorem stepChain_checkpointHistory_publicView
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat} :
    ∀ {start : (PrimitiveMachine compiled).BoundedState horizon}
      {steps : List ((View semantics).BoundedStep horizon)}
      (hchain : (View semantics).StepChainFrom horizon start steps),
        (stepChain_checkpointHistory semantics hchain).publicView =
          Machine.RoundView.BoundedHistory.publicViewFrom
            (view := View semantics) steps
  | start, [], _hchain => by
      change
        (EventGraph.CheckpointPresentation.History.nil
          (view := presentation) start.state).publicView = []
      unfold EventGraph.CheckpointPresentation.History.publicView
      rfl
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      subst hsrc
      have ih := stepChain_checkpointHistory_publicView semantics htail
      simp only [stepChain_checkpointHistory,
        EventGraph.CheckpointPresentation.History.publicView_append,
        EventGraph.CheckpointPresentation.History.publicView,
        Machine.RoundView.BoundedHistory.publicViewFrom,
        Machine.RoundView.BoundedStep.publicObs,
        List.nil_append, List.singleton_append]
      congr 1

private theorem stepChain_checkpointHistory_playerView
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat} (player : P) :
    ∀ {start : (PrimitiveMachine compiled).BoundedState horizon}
      {steps : List ((View semantics).BoundedStep horizon)}
      (hchain : (View semantics).StepChainFrom horizon start steps),
        (stepChain_checkpointHistory semantics hchain).playerView player =
          steps.map fun step => step.privateObs player
  | start, [], _hchain => by
      change
        (EventGraph.CheckpointPresentation.History.nil
          (view := presentation) start.state).playerView player = []
      unfold EventGraph.CheckpointPresentation.History.playerView
      rfl
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      subst hsrc
      have ih := stepChain_checkpointHistory_playerView
        semantics player htail
      simp only [stepChain_checkpointHistory,
        EventGraph.CheckpointPresentation.History.playerView_append,
        EventGraph.CheckpointPresentation.History.playerView,
        Machine.RoundView.BoundedStep.privateObs,
        List.nil_append, List.singleton_append, List.map_cons]
      congr 1

/-- Event batches extracted from a bounded frontier history form an available
primitive batched machine run from the initial checkpoint to the history's
endpoint. -/
theorem boundedHistory_eventBatches_availableRun
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (history : (View semantics).BoundedHistory horizon) :
    (PrimitiveMachine compiled).AvailableRunBatchesFrom
      ((Machine.BoundedState.init (PrimitiveMachine compiled) horizon).state)
      ((View semantics).boundedHistoryEventBatches horizon history)
      history.lastState.state := by
  exact stepChain_eventBatches_availableRun semantics history.chain

/-- A supported default-length behavioral outcome has a concrete supported
bounded history behind it. The witness carries the operational facts needed by
adequacy theorems: available primitive batches, terminality, and agreement with
the primitive machine outcome. -/
theorem boundedOutcomeFromBehavioral_support_history_completionBound
    (semantics : FrontierRoundSemantics compiled presentation)
    [∀ player, Fintype (Option ((View semantics).Act player))]
    (β :
      (View semantics).BoundedBehavioralProfile
        (completionBound compiled))
    {outcome : (PrimitiveMachine compiled).Outcome}
    (hsupport :
      some outcome ∈
        ((View semantics).boundedOutcomeFromBehavioral
          (completionBound compiled) β
          (completionBound compiled)).support) :
    ∃ history :
        (View semantics).BoundedHistory (completionBound compiled),
      history ∈
        ((View semantics).runDist
          (completionBound compiled) (completionBound compiled) β).support ∧
      EventGraph.Terminal compiled.graph history.lastState.state.1 ∧
      (PrimitiveMachine compiled).outcome history.lastState.state =
        some outcome ∧
      (PrimitiveMachine compiled).AvailableRunBatchesFrom
        ((Machine.BoundedState.init
          (PrimitiveMachine compiled) (completionBound compiled)).state)
        ((View semantics).boundedHistoryEventBatches
          (completionBound compiled) history)
        history.lastState.state := by
  classical
  rcases (PMF.mem_support_map_iff _ _ _).mp hsupport with
    ⟨trace, htrace, hresult⟩
  rcases (PMF.mem_support_map_iff _ _ _).mp htrace with
    ⟨history, hhistory, htraceEq⟩
  have hterminal :
      EventGraph.Terminal compiled.graph history.lastState.state.1 :=
    runDist_support_terminal_of_completionBound
      semantics β (by
        simpa [Machine.RoundView.boundedEventBatchTraceFromBehavioral]
          using hhistory)
  have houtcome :
      (PrimitiveMachine compiled).outcome history.lastState.state =
        some outcome := by
    rw [← htraceEq] at hresult
    simpa [Machine.RoundView.boundedHistoryTrace] using hresult
  exact
    ⟨history, hhistory, hterminal, houtcome,
      boundedHistory_eventBatches_availableRun semantics history⟩

/-- Pure-strategy version of
`boundedOutcomeFromBehavioral_support_history_completionBound`. Pure runs are
the corresponding point-mass behavioral runs. -/
theorem boundedOutcomeFromPure_support_history_completionBound
    (semantics : FrontierRoundSemantics compiled presentation)
    [∀ player, Fintype (Option ((View semantics).Act player))]
    (π :
      (View semantics).BoundedPureProfile
        (completionBound compiled))
    {outcome : (PrimitiveMachine compiled).Outcome}
    (hsupport :
      some outcome ∈
        ((View semantics).boundedOutcomeFromPure
          (completionBound compiled) π
          (completionBound compiled)).support) :
    ∃ history :
        (View semantics).BoundedHistory (completionBound compiled),
      history ∈
        ((View semantics).runDist
          (completionBound compiled) (completionBound compiled)
          ((View semantics).legalPureToBehavioral
            (completionBound compiled) π)).support ∧
      EventGraph.Terminal compiled.graph history.lastState.state.1 ∧
      (PrimitiveMachine compiled).outcome history.lastState.state =
        some outcome ∧
      (PrimitiveMachine compiled).AvailableRunBatchesFrom
        ((Machine.BoundedState.init
          (PrimitiveMachine compiled) (completionBound compiled)).state)
        ((View semantics).boundedHistoryEventBatches
          (completionBound compiled) history)
        history.lastState.state := by
  simpa [Machine.RoundView.boundedOutcomeFromPure] using
    boundedOutcomeFromBehavioral_support_history_completionBound
      semantics
      ((View semantics).legalPureToBehavioral
        (completionBound compiled) π)
      hsupport

/-- Every bounded frontier-round history induces a checkpoint history in the
attached checkpoint presentation. This is the bridge from strategic round
histories back to schedule-agnostic checkpoint histories. -/
noncomputable def boundedHistory_checkpointHistory
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (history : (View semantics).BoundedHistory horizon) :
    presentation.History
      ((Machine.BoundedState.init (PrimitiveMachine compiled) horizon).state)
      history.lastState.state := by
  simpa [Machine.RoundView.BoundedHistory.lastState] using
    stepChain_checkpointHistory semantics history.chain

/-- The checkpoint history induced by a bounded frontier history has exactly
the same public observations as the bounded round history. -/
theorem boundedHistory_checkpointHistory_publicView
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (history : (View semantics).BoundedHistory horizon) :
    (boundedHistory_checkpointHistory semantics history).publicView =
      history.publicView := by
  exact
    stepChain_checkpointHistory_publicView semantics history.chain

/-- The checkpoint history induced by a bounded frontier history has exactly
the private observations carried by the bounded round information state. -/
theorem boundedHistory_checkpointHistory_playerView
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (history : (View semantics).BoundedHistory horizon)
    (player : P) :
    (boundedHistory_checkpointHistory semantics history).playerView player =
      (Machine.RoundView.InfoState.observationEvents
        (history.playerView player)).map Prod.fst := by
  change
    (stepChain_checkpointHistory semantics history.chain).playerView player =
      (Machine.RoundView.InfoState.observationEvents
        (history.playerView player)).map Prod.fst
  rw [stepChain_checkpointHistory_playerView semantics player history.chain]
  rw [Machine.RoundView.BoundedHistory.playerView]
  rw [Machine.RoundView.BoundedHistory.observationEvents_playerViewFrom]
  simp [Function.comp_def]

end FrontierRoundSemantics

omit [Fintype P] in
/-- Erase an option-valued outcome distribution when `none` has no support. -/
noncomputable def eraseNonePMF {α : Type}
    (dist : PMF (Option α))
    (htotal : ∀ result ∈ dist.support, ∃ value, result = some value) :
    PMF α :=
  dist.bindOnSupport fun result hresult =>
    match result with
    | some value => PMF.pure value
    | none =>
        False.elim <| by
          rcases htotal none hresult with ⟨value, hvalue⟩
          cases hvalue

omit [Fintype P] in
theorem mem_support_eraseNonePMF_iff {α : Type}
    {dist : PMF (Option α)}
    {htotal : ∀ result ∈ dist.support, ∃ value, result = some value}
    {value : α} :
    value ∈ (eraseNonePMF dist htotal).support ↔
      some value ∈ dist.support := by
  unfold eraseNonePMF
  rw [PMF.mem_support_bindOnSupport_iff]
  constructor
  · rintro ⟨result, hresult, hvalue⟩
    cases result with
    | none =>
        rcases htotal none hresult with ⟨witness, hwitness⟩
        cases hwitness
    | some witness =>
        rw [PMF.support_pure, Set.mem_singleton_iff] at hvalue
        simpa [hvalue] using hresult
  · intro hsome
    exact ⟨some value, hsome, by simp [PMF.support_pure]⟩

omit [Fintype P] in
theorem eraseNonePMF_apply {α : Type}
    {dist : PMF (Option α)}
    {htotal : ∀ result ∈ dist.support, ∃ value, result = some value}
    (value : α) :
    eraseNonePMF dist htotal value = dist (some value) := by
  unfold eraseNonePMF
  rw [PMF.bindOnSupport_apply]
  rw [tsum_eq_single (some value)]
  · by_cases hzero : dist (some value) = 0
    · simp [hzero]
    · simp [hzero, PMF.pure_apply]
  · intro result hne
    cases result with
    | none =>
        by_cases hzero : dist none = 0
        · simp [hzero]
        · have hsupport : none ∈ dist.support :=
            (PMF.mem_support_iff _ _).2 hzero
          rcases htotal none hsupport with ⟨witness, hwitness⟩
          cases hwitness
    | some witness =>
        by_cases hzero : dist (some witness) = 0
        · simp [hzero]
        · have hvalue : value ≠ witness := by
            intro heq
            subst heq
            exact hne rfl
          simp [hzero, PMF.pure_apply, hvalue]

omit [Fintype P] in
theorem eraseNonePMF_map_some {α : Type}
    {dist : PMF (Option α)}
    {htotal : ∀ result ∈ dist.support, ∃ value, result = some value} :
    PMF.map some (eraseNonePMF dist htotal) = dist := by
  apply PMF.ext
  intro result
  cases result with
  | none =>
      rw [PMF.map_apply]
      simp only [reduceCtorEq, ↓reduceIte, tsum_zero]
      by_cases hzero : dist none = 0
      · exact hzero.symm
      · have hsupport : none ∈ dist.support :=
          (PMF.mem_support_iff _ _).2 hzero
        rcases htotal none hsupport with ⟨witness, hwitness⟩
        cases hwitness
  | some value =>
      rw [PMF.map_apply]
      rw [tsum_eq_single value]
      · simp [eraseNonePMF_apply (htotal := htotal)]
      · intro other hne
        have hsome : some value ≠ some other := by
          intro h
          cases h
          exact hne rfl
        simp [hsome]

omit [Fintype P] in
theorem eraseNonePMF_map {α β : Type}
    {dist : PMF (Option α)}
    {htotal : ∀ result ∈ dist.support, ∃ value, result = some value}
    (f : α → β) (fallback : β) :
    PMF.map f (eraseNonePMF dist htotal) =
      PMF.map (fun
        | some value => f value
        | none => fallback) dist := by
  let optionF : Option α → β := fun
    | some value => f value
    | none => fallback
  calc
    PMF.map f (eraseNonePMF dist htotal)
        = PMF.map (optionF ∘ some) (eraseNonePMF dist htotal) := by
            rfl
    _ = PMF.map optionF (PMF.map some (eraseNonePMF dist htotal)) := by
            rw [PMF.map_comp]
    _ = PMF.map optionF dist := by
            rw [eraseNonePMF_map_some]

omit [Fintype P] in
theorem eraseNonePMF_expect {α : Type}
    {dist : PMF (Option α)}
    {htotal : ∀ result ∈ dist.support, ∃ value, result = some value}
    (utility : α → ℝ) (cutoff : ℝ) {C : ℝ}
    (hbd : ∀ value, |utility value| ≤ C) :
    Math.Probability.expect (eraseNonePMF dist htotal) utility =
      Math.Probability.expect dist (fun
        | some value => utility value
        | none => cutoff) := by
  let optionUtility : Option α → ℝ := fun
    | some value => utility value
    | none => cutoff
  have hpush :=
    Math.ProbabilityMassFunction.expect_pushforward_of_bounded_on_source
      (μ := eraseNonePMF dist htotal) (f := some) (φ := optionUtility)
      (hbd := hbd)
  have hmap :
      Math.ProbabilityMassFunction.pushforward
        (eraseNonePMF dist htotal) some = dist := by
    simpa [Math.ProbabilityMassFunction.pushforward] using
      eraseNonePMF_map_some (dist := dist) (htotal := htotal)
  rw [hmap] at hpush
  simpa [optionUtility] using hpush.symm


end ToEventGraph

end Vegas
