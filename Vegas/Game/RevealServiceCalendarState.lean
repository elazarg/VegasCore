/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceObservation
import Vegas.Pending.RevealTranscript
import Vegas.Pending.EventSequentialTiming

/-! # Public calendar metadata at revelation checkpoints

Every source rank contributes its fixed number of ticks. The next event's
activation time is the preceding event's completion time: before those ticks
for a successful opening and after them for withholding. The public result
therefore determines the exact activation table, including with repeated owners.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Clock at the start of source rank `rank` in the existing service calendar. -/
def clockAt (rank : Nat) : Nat := (Finset.range rank).sum (fun prior => prior + 1)

theorem clockAt_succ (rank : Nat) : clockAt (rank + 1) = clockAt rank + (rank + 1) := by
  simp only [clockAt, Finset.sum_range_succ]

/-- The activation time is determined by the preceding public publication. -/
def checkpointEntryTime (accepted : AcceptedHandles (graph setup))
    (view : (graph setup).PublicObservation) : Nat :=
  match view.completionOrder.getLast? with
  | none => 0
  | some prior =>
      if (publicationPacket? accepted view.store prior).isSome
      then clockAt prior.val else clockAt (prior.val + 1)

/-- Sequential dependencies leave only the current rank active. At settlement
rank there is no event with that index, so the whole table is empty. -/
def checkpointActivations (accepted : AcceptedHandles (graph setup))
    (view : (graph setup).PublicObservation) (rank : Nat) :
    (graph setup).EventId → Option Nat := fun event =>
  if event.val = rank then some (checkpointEntryTime setup accepted view) else none

theorem ready_iff_rank (config : (graph setup).Config) (rank : Nat)
    (ordered : config.cut.IsPrefix rank) (event : (graph setup).EventId) :
    config.cut.Ready event ↔ event.val = rank := by
  constructor
  · intro ready
    have lower : rank ≤ event.val := by
      by_contra earlier
      exact ready.1 ((ordered.2 event).mpr (by omega))
    have inside : rank < (graph setup).order.eventCount := by omega
    exact congrArg Fin.val (setup.eventGraph.sequentialize_ready_unique config.cut ready
      (ordered.ready inside))
  · intro same
    have inside : rank < (graph setup).order.eventCount := by omega
    have equal : event = ⟨rank, inside⟩ := Fin.ext same
    subst event
    exact ordered.ready inside

theorem complete_activations (reveals : setup.program.RevealOnly)
    {inputs : (graph setup).Inputs} (state : EventGraphRuntime.State (graph setup))
    (invariant : state.Invariant inputs) (event : (graph setup).EventId)
    (ready : state.config.cut.Ready event) (action : (graph setup).Action event)
    (value : ((graph setup).outputLayout event).Value) :
    (state.complete event ready action value).activatedAt = fun query =>
      if query.val = event.val + 1 then some state.clock else none := by
  funext query
  by_cases successor : query.val = event.val + 1
  · rw [ite_eq_left successor]
    obtain ⟨owner, owned⟩ := source_owner setup reveals query
    exact (EventGraphRuntime.State.complete_successor_activatedAt state invariant event query ready
      successor (by simp [owned]) action value).2
  · rw [ite_eq_right successor]
    have ordered : state.config.cut.IsPrefix event.val :=
      ⟨Nat.le_of_lt event.isLt, fun prior =>
        setup.eventGraph.sequentialize_mem_completed_iff_lt_of_ready state.config.cut ready⟩
    have nextPrefix := ordered.complete_at event ready rfl
    have absent : ¬ (state.config.complete event ready action value).cut.Ready query := by
      rw [ready_iff_rank setup _ (event.val + 1) nextPrefix query]
      exact successor
    change EventGraphRuntime.State.refreshActivated _ state.clock state.activatedAt query = none
    simp only [EventGraphRuntime.State.refreshActivated, dite_eq_right absent]

theorem checkpointEntryTime_complete (accepted : AcceptedHandles (graph setup))
    (config : (graph setup).Config) (event : (graph setup).EventId)
    (ready : config.cut.Ready event) (action : (graph setup).Action event)
    (value : ((graph setup).outputLayout event).Value) :
    checkpointEntryTime setup accepted
        ((graph setup).publicObserve (config.complete event ready action value)) =
      if (publicationPacket? accepted (config.complete event ready action value).store event).isSome
      then clockAt event.val else clockAt (event.val + 1) := by
  unfold checkpointEntryTime
  simp only [EventGraph.publicObserve, EventGraph.Config.complete_history, List.map_append,
    List.map_singleton, List.getLast?_append, List.getLast?_singleton, Option.some_or,
    publicationPacket?_publicStore]

theorem initial_calendar (reveals : setup.program.RevealOnly)
    (inputs : (graph setup).Inputs) (accepted : AcceptedHandles (graph setup)) :
    (EventGraphRuntime.State.initial inputs).clock = clockAt 0 ∧
      (EventGraphRuntime.State.initial inputs).activatedAt =
        checkpointActivations setup accepted
          ((graph setup).publicObserve (EventGraph.Config.initial inputs)) 0 := by
  constructor
  · rfl
  · funext event
    have ordered : (EventGraph.Config.initial (graph := graph setup) inputs).cut.IsPrefix 0 :=
      Vegas.EventOrder.Cut.empty_isPrefix _
    unfold checkpointActivations
    by_cases zero : event.val = 0
    · rw [ite_eq_left zero]
      have ready := (ready_iff_rank setup _ 0 ordered event).mpr zero
      obtain ⟨owner, owned⟩ := source_owner setup reveals event
      change EventGraphRuntime.State.refreshActivated _ 0 (fun _ => none) event = _
      rw [EventGraphRuntime.State.refreshActivated, dite_eq_left ready, owned]
      rfl
    · rw [ite_eq_right zero]
      have absent := mt (ready_iff_rank setup _ 0 ordered event).mp zero
      change EventGraphRuntime.State.refreshActivated _ 0 (fun _ => none) event = none
      rw [EventGraphRuntime.State.refreshActivated, dite_eq_right absent]

/-- The exact two actual application endpoints of a service block have the
public clock and activation formulas. Packet presence is a public-result fact,
discharged by the successful/failed resolve equations in `RevealTranscript`. -/
theorem settlement_calendar (reveals : setup.program.RevealOnly)
    {inputs : (graph setup).Inputs} (state : EventGraphRuntime.State (graph setup))
    (invariant : state.Invariant inputs) (event : (graph setup).EventId)
    (ready : state.config.cut.Ready event) (action : (graph setup).Action event)
    (value : ((graph setup).outputLayout event).Value) (disclose : Bool)
    (accepted : AcceptedHandles (graph setup)) (clock : state.clock = clockAt event.val)
    (published : (publicationPacket? accepted
      (state.config.complete event ready action value).store event).isSome = disclose) :
    let next := if disclose then
      { state.complete event ready action value with clock := state.clock + (event.val + 1) }
      else ({ state with clock := state.clock + (event.val + 1) } :
        EventGraphRuntime.State (graph setup)).complete event ready action value
    next.clock = clockAt (event.val + 1) ∧
      next.activatedAt = checkpointActivations setup accepted
        ((graph setup).publicObserve next.config) (event.val + 1) := by
  have clockNext : state.clock + (event.val + 1) = clockAt (event.val + 1) := by
    rw [clockAt_succ, clock]
  have entry := checkpointEntryTime_complete setup accepted state.config event ready action value
  rw [published] at entry
  cases disclose with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at entry ⊢
      refine ⟨clockNext, ?_⟩
      rw [complete_activations setup reveals _ (invariant.add_clock (event.val + 1))]
      funext query
      change (if query.val = event.val + 1 then some (state.clock + (event.val + 1)) else none) =
        if query.val = event.val + 1 then some (checkpointEntryTime setup accepted
          ((graph setup).publicObserve (state.config.complete event ready action value))) else none
      rw [entry, clockNext]
  | true =>
      simp only [↓reduceIte] at entry ⊢
      refine ⟨clockNext, ?_⟩
      rw [complete_activations setup reveals state invariant]
      funext query
      change (if query.val = event.val + 1 then some state.clock else none) =
        if query.val = event.val + 1 then some (checkpointEntryTime setup accepted
          ((graph setup).publicObserve (state.config.complete event ready action value))) else none
      rw [entry, clock]

/-- The operational checkpoint equations make the whole native before-view a
function of the source view. Own response recall is separate and may retain
different published replay choices; no hidden initial inputs are identified. -/
theorem source_checkpoint_observe_eq
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} (refs : ContextRefs (graphLayout setup.program) Γ)
    (rank : Nat) (covered : refs.CoversPrefix setup.program rank) (who : Player)
    (left right : Config Player L Γ)
    (nativeLeft nativeRight : (application setup leaks).Execution)
    {leftInputs rightInputs : (graph setup).Inputs}
    (leftReachable : nativeLeft.application.config.Reachable leftInputs)
    (rightReachable : nativeRight.application.config.Reachable rightInputs)
    (leftPrefix : nativeLeft.application.config.cut.IsPrefix rank)
    (rightPrefix : nativeRight.application.config.cut.IsPrefix rank)
    (leftStore : refs.Agrees left.state nativeLeft.application.config.store)
    (rightStore : refs.Agrees right.state nativeRight.application.config.store)
    (leftHistory : decodeHistory setup.program
      (nativeLeft.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = left.history)
    (rightHistory : decodeHistory setup.program
      (nativeRight.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = right.history)
    (leftCandidates : nativeLeft.application.candidates =
      (EventGraphRuntime.State.initial nativeLeft.application.config.inputs).candidates)
    (rightCandidates : nativeRight.application.candidates =
      (EventGraphRuntime.State.initial nativeRight.application.config.inputs).candidates)
    (accepted : AcceptedHandles (graph setup))
    (leftAccepted : nativeLeft.application.accepted = accepted)
    (rightAccepted : nativeRight.application.accepted = accepted)
    (leftClock : nativeLeft.application.clock = clockAt rank)
    (rightClock : nativeRight.application.clock = clockAt rank)
    (leftActivated : nativeLeft.application.activatedAt = checkpointActivations setup accepted
      ((graph setup).publicObserve nativeLeft.application.config) rank)
    (rightActivated : nativeRight.application.activatedAt = checkpointActivations setup accepted
      ((graph setup).publicObserve nativeRight.application.config) rank)
    (granted : Option (graph setup).EventId)
    (leftGrant : nativeLeft.application.serviceGrant = granted)
    (rightGrant : nativeRight.application.serviceGrant = granted)
    (leftLedger : nativeLeft.network.ledger = publicationLedger accepted
      ((graph setup).publicObserve nativeLeft.application.config))
    (rightLedger : nativeRight.network.ledger = publicationLedger accepted
      ((graph setup).publicObserve nativeRight.application.config))
    (leaked : nativeLeft.network.leaked who = nativeRight.network.leaked who)
    (leftReceipts : nativeLeft.receipts = publicationReceipts accepted
      ((graph setup).publicObserve nativeLeft.application.config))
    (rightReceipts : nativeRight.receipts = publicationReceipts accepted
      ((graph setup).publicObserve nativeRight.application.config))
    (same : left.view who = right.view who) :
    nativeLeft.observe (application setup leaks) who =
      nativeRight.observe (application setup leaks) who := by
  have observation := checkpoint_playerObservation_eq setup refs rank covered who left right
    nativeLeft.application.config nativeRight.application.config leftReachable rightReachable
    leftPrefix rightPrefix leftStore rightStore leftHistory rightHistory same
  have publicObservation := EventGraph.publicObserve_eq_of_playerObserve_eq who
    nativeLeft.application.config nativeRight.application.config observation
  apply checkpoint_observe_eq setup leaks who nativeLeft nativeRight observation
    leftCandidates rightCandidates
  · exact leftAccepted.trans rightAccepted.symm
  · exact leftClock.trans rightClock.symm
  · rw [leftActivated, rightActivated, publicObservation]
  · exact leftGrant.trans rightGrant.symm
  · rw [leftLedger, rightLedger, publicObservation]
  · exact leaked
  · rw [leftReceipts, rightReceipts, publicObservation]

/-- Both actual settlement branches leave the next event within its deadline.
This is uniform in the action and result; the successful branch completes before
the ticks, and the withholding branch completes afterward. -/
theorem settlement_successor_timely {inputs : (graph setup).Inputs}
    (state : EventGraphRuntime.State (graph setup)) (invariant : state.Invariant inputs)
    (event next : (graph setup).EventId) (ready : state.config.cut.Ready event)
    (successor : next.val = event.val + 1)
    (strategic : ((graph setup).actor? next).isSome = true)
    (action : (graph setup).Action event) (value : ((graph setup).outputLayout event).Value)
    (disclose : Bool) :
    let after := if disclose then
      { state.complete event ready action value with clock := state.clock + (event.val + 1) }
      else ({ state with clock := state.clock + (event.val + 1) } :
        EventGraphRuntime.State (graph setup)).complete event ready action value
    after.WithinDeadline (runtime setup) next := by
  cases disclose with
  | false =>
      exact EventGraphRuntime.State.ticks_complete_successor_within (runtime setup) state invariant
        event next ready successor strategic action value (event.val + 1)
        (runtime_deadline_pos setup next)
  | true =>
      apply EventGraphRuntime.State.complete_successor_within_after_ticks (runtime setup) state
        invariant event next ready successor strategic action value (event.val + 1)
      change event.val + 1 < next.val + 1
      omega

end Vegas.SourceProgram.RevealService
