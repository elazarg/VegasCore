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

end Vegas
