/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.ActionSplitting
import Vegas.Game.RevealServiceState
import Vegas.Pending.ReactiveContinuationObservation
import Vegas.Game.RevealServiceCalendarState
import Vegas.EventGraph.PrivateInputs
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactiveServiceProgress
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.EventSequentialTiming
import Vegas.Source.RevealSequence
import Vegas.Source.SetupProtocol

/-! # Checkpoint invariants for the actual revelation service

The relation records facts about the existing source configuration and native
execution. In particular, native response recall and network inputs remain
untouched. Only published envelopes may remain pending between source events.
No strategic correspondence or optimal assessment is a field of this relation.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Source/application correspondence and source-determined public metadata.
Pending copies, private leak lists and response recall are auxiliary execution
data; no condition here identifies or erases them. -/
structure PublicCheckpoint (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (initial : State L setup.context) {Γ : SourceCtx Player L}
    (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (rank : Nat) (execution : (application setup leaks).Execution) : Prop where
  emptyRegistry : source.registry = []
  openable : source.state.BindingsOpenable
  agrees : refs.Agrees source.state execution.application.config.store
  history : decodeHistory setup.program
    (execution.application.config.history.map
      (setup.eventGraph.fromModeCompletion .sequential)) = source.history
  ordered : execution.application.config.cut.IsPrefix rank
  invariant : EventGraphRuntime.State.Invariant (graph := graph setup)
    (setup.eventInputs initial) execution.application
  binding : execution.application.BindingInvariant
  accepted : execution.application.accepted =
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).accepted
  candidates : execution.application.candidates =
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).candidates
  timely : ∀ event, event.val = rank → ((graph setup).actor? event).isSome = true →
    execution.application.WithinDeadline (runtime setup) event
  reveals : setup.program.RevealOnly
  covered : refs.CoversPrefix setup.program rank
  ledger : execution.network.ledger = publicationLedger
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).accepted
    ((graph setup).publicObserve execution.application.config)
  receipts : execution.receipts = publicationReceipts
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).accepted
    ((graph setup).publicObserve execution.application.config)
  counters : execution.network.nextSerial = publicationSerial
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).accepted
    ((graph setup).publicObserve execution.application.config)
  clock : execution.application.clock = clockAt rank
  activated : execution.application.activatedAt = checkpointActivations setup
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).accepted
    ((graph setup).publicObserve execution.application.config) rank

/-- The fixed one-owner service additionally has empty private leak lists.
This specialization is useful for that calendar's exact observation theorem;
delayed-inclusion rosters instead retain their published private leak history. -/
structure Checkpoint (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (initial : State L setup.context) {Γ : SourceCtx Player L}
    (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (rank : Nat) (execution : (application setup leaks).Execution) : Prop
    extends PublicCheckpoint setup leaks initial source refs rank execution where
  pending : ∀ message ∈ execution.network.pending,
    message.id ∈ execution.network.ledger.map Message.id
  leaked : execution.network.leaked = fun _ => []
  inputs : ∀ input ∈ execution.network.inputs,
    input.id ∈ execution.network.ledger.map Message.id
  serials : execution.network.SerialsBeforeNext
  recall : execution.InputRecall (application setup leaks)

/-- The induction starts at every supplied valid source state, without any
independence restriction on its private cells. -/
theorem checkpoint_initial (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (reveals : setup.program.RevealOnly)
    (initial : State L setup.context) (openable : initial.BindingsOpenable) :
    Checkpoint setup leaks initial (setup.initialConfig initial)
      (ContextRefs.initial setup.context (outputLayout setup.program)) 0
      (ReactiveApplication.Execution.initial (application setup leaks)
        (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial))) := by
  refine {
    emptyRegistry := rfl
    openable := openable
    agrees := initial_agrees setup initial
    history := initial_history setup initial
    ordered := ?_
    invariant := EventGraphRuntime.State.initial_invariant _
    binding := EventGraphRuntime.State.initial_bindingInvariant _
    accepted := rfl
    candidates := rfl
    pending := ?_
    leaked := rfl
    inputs := ?_
    serials := MessageNetwork.SerialsBeforeNext.empty
    recall := (application setup leaks).initial_inputRecall _
    timely := ?_
    reveals := reveals
    covered := ContextRefs.initial_coversPrefix setup.program
    ledger := rfl
    receipts := rfl
    counters := rfl
    clock := rfl
    activated := ?_ }
  · exact EventOrder.Cut.empty_isPrefix _
  · intro event first strategic
    apply EventGraphRuntime.State.initial_withinDeadline _ (runtime setup) event _ strategic
      (runtime_deadline_pos setup event)
    have start := EventOrder.Cut.empty_isPrefix (graph setup).order
    have positive : 0 < (graph setup).order.eventCount := by omega
    have same : (⟨0, positive⟩ : (graph setup).EventId) = event := Fin.ext first.symm
    rw [← same]
    exact start.ready positive
  · exact (initial_calendar setup reveals (setup.eventInputs initial) _).2
  · simp only [ReactiveApplication.Execution.initial, MessageNetwork.empty,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  · simp only [ReactiveApplication.Execution.initial, MessageNetwork.empty,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true]

/-- At a checkpoint of some rank, the event of that rank is ready. -/
theorem PublicCheckpoint.ready {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} {Γ : SourceCtx Player L}
    {source : Config Player L Γ} {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {execution : (application setup leaks).Execution}
    (checkpoint : PublicCheckpoint setup leaks initial source refs rank execution)
    (event : (graph setup).EventId) (eventRank : event.val = rank) :
    execution.application.config.cut.Ready event := by
  have inside : rank < (graph setup).order.eventCount := eventRank ▸ event.isLt
  have same : (⟨rank, inside⟩ : (graph setup).EventId) = event := Fin.ext eventRank.symm
  rw [← same]
  exact checkpoint.ordered.ready inside

/-- At matched source ranks, the actual public metadata formulas make the
native before-view a function of the source view. This permits different
initial private states and does not identify the players' response recalls. -/
theorem PublicCheckpoint.observe_eq {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {leftInitial rightInitial : State L setup.context} {Γ : SourceCtx Player L}
    {left right : Config Player L Γ} {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {nativeLeft nativeRight : (application setup leaks).Execution}
    (leftCheckpoint : PublicCheckpoint setup leaks leftInitial left refs rank nativeLeft)
    (rightCheckpoint : PublicCheckpoint setup leaks rightInitial right refs rank nativeRight)
    (who : Player)
    (leaked : nativeLeft.network.leaked who = nativeRight.network.leaked who)
    (same : left.view who = right.view who) :
    nativeLeft.observe (application setup leaks) who =
      nativeRight.observe (application setup leaks) who := by
  have leftCandidates : nativeLeft.application.candidates =
      (EventGraphRuntime.State.initial (graph := graph setup)
        nativeLeft.application.config.inputs).candidates := by
    rw [leftCheckpoint.invariant.reachable.inputs_eq]
    exact leftCheckpoint.candidates
  have rightCandidates : nativeRight.application.candidates =
      (EventGraphRuntime.State.initial (graph := graph setup)
        nativeRight.application.config.inputs).candidates := by
    rw [rightCheckpoint.invariant.reachable.inputs_eq]
    exact rightCheckpoint.candidates
  exact source_checkpoint_observe_eq setup leaks refs rank leftCheckpoint.covered
    who left right nativeLeft
    nativeRight leftCheckpoint.invariant.reachable rightCheckpoint.invariant.reachable
    leftCheckpoint.ordered rightCheckpoint.ordered leftCheckpoint.agrees rightCheckpoint.agrees
    leftCheckpoint.history rightCheckpoint.history leftCandidates rightCandidates
    (EventGraphRuntime.State.initial (graph := graph setup)
      (setup.eventInputs leftInitial)).accepted
    leftCheckpoint.accepted rightCheckpoint.accepted leftCheckpoint.clock rightCheckpoint.clock
    leftCheckpoint.activated rightCheckpoint.activated leftCheckpoint.ledger rightCheckpoint.ledger
    leaked
    leftCheckpoint.receipts rightCheckpoint.receipts same

/-- Empty leakage discharges the auxiliary observation premise of the
shared public checkpoint theorem. -/
theorem Checkpoint.observe_eq {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {leftInitial rightInitial : State L setup.context} {Γ : SourceCtx Player L}
    {left right : Config Player L Γ} {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {nativeLeft nativeRight : (application setup leaks).Execution}
    (leftCheckpoint : Checkpoint setup leaks leftInitial left refs rank nativeLeft)
    (rightCheckpoint : Checkpoint setup leaks rightInitial right refs rank nativeRight)
    (who : Player)
    (same : left.view who = right.view who) :
    nativeLeft.observe (application setup leaks) who =
      nativeRight.observe (application setup leaks) who :=
  leftCheckpoint.toPublicCheckpoint.observe_eq rightCheckpoint.toPublicCheckpoint who
    (by rw [leftCheckpoint.leaked, rightCheckpoint.leaked]) same

end Vegas
