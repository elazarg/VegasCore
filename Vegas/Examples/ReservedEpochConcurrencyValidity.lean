/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.ReservedEpochConcurrency
import Vegas.Pending.PhaseBindingAcceptance
import Vegas.Pending.PhaseNativeInvariant
import Interaction.ReactiveRawRoundTrace

/-! # Native admissibility of two concurrently pending commitments -/

noncomputable section

namespace Vegas.Examples.ReservedEpochConcurrency

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability
open CommitTimingInformation

def fixtureInputs (bit : Bool) : PMF graph.Inputs := PMF.pure (encodeInputs (sourceInitial bit))

def fixtureInitial (bit : Bool) : PMF app.State :=
  (fixtureInputs bit).map (PhaseRuntimeState.initial CommitTimingInformation.plan)

theorem concurrent_raw_trace (reverse bit : Bool) :
    Nonempty ((app.protocol (fixtureInitial bit) 4 selectedScheduler).Trace
      (some ⟨0, none, afterBoth reverse bit⟩)) := by
  apply app.raw_trace_roundsFrom (fixtureInitial bit) 4 selectedScheduler players 4 (by decide)
  change afterBoth reverse bit ∈ ((fixtureInitial bit).bind fun state =>
    app.runRounds selectedScheduler players 4
      (ReactiveApplication.Execution.initial app state)).support
  simpa only [fixtureInitial, fixtureInputs, PMF.pure_map, PMF.pure_bind,
    initialExecution, CommitTimingInformation.initialState] using
    concurrent_prefix_supported reverse bit

private theorem offer_preserves_request (execution : app.Execution) (actor owner : Player)
    (requested : execution.application.SeedRequest owner (originalCoordinate owner)) :
    (offer execution actor).application.SeedRequest owner (originalCoordinate owner) :=
  respond_request runtime leaks _ actor (response actor) owner _ requested

theorem pending_binding_request (reverse bit : Bool) (owner : Player) :
    (afterBoth reverse bit).application.SeedRequest owner (originalCoordinate owner) :=
  offer_preserves_request _ _ _
    (offer_preserves_request _ _ _ (initial_binding_request bit owner))

theorem pending_clock (reverse bit : Bool) :
    (afterBoth reverse bit).application.current.native.clock = 0 := by
  have publicEq (execution : app.Execution) (owner : Player) :
      (offer execution owner).application.publicView = execution.application.publicView := by
    exact PhaseCount.submit_publicView execution.application owner _
  have both := (publicEq (afterFirst reverse bit) (second reverse)).trans
    (publicEq (beforeOffers bit) (first reverse))
  have clock := congrArg (fun view : PhasePublicView graph => view.native.clock) both
  change (afterBoth reverse bit).application.current.native.clock =
    (initialState bit).current.native.clock at clock
  exact clock.trans (initialState_clock bit)

theorem pending_inputs (reverse bit : Bool) :
    (afterBoth reverse bit).network.inputs = (afterBoth reverse bit).network.pending := rfl

theorem owner_message_pending (reverse bit : Bool) (owner : Player) :
    commitmentMessage owner ∈ (afterBoth reverse bit).network.pending := by
  rw [canonical_pending]
  fin_cases owner <;> cases reverse <;> simp [first, second]

theorem pending_binding_timely (reverse bit : Bool) (owner : Player) :
    (afterBoth reverse bit).application.current.native.WithinDeadline runtime
      (bindingEvent owner) := by
  obtain ⟨trace⟩ := concurrent_raw_trace reverse bit
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks CommitTimingInformation.plan
    (fixtureInputs bit) 4 selectedScheduler trace
  have request := pending_binding_request reverse bit owner
  have active := (valid.active.activated_iff (bindingEvent owner)).mpr
    ⟨request.2.2.1, by rw [bindingEvent_actor]; rfl⟩
  obtain ⟨entered, stamp⟩ := Option.isSome_iff_exists.mp active
  rw [State.WithinDeadline, stamp, pending_clock]
  norm_num [runtime, CommitTimingInformation.runtime]

/-- Each concurrently pending packet can be accepted immediately by the actual
phase handler. The proof uses its genuine initialized trace, not a supplied
native acceptance or a stipulated scheduler response table. -/
theorem pending_binding_admissible (reverse bit : Bool) (owner : Player) :
    ∃ next, app.handle (afterBoth reverse bit).application
      (commitmentMessage owner) = some next := by
  obtain ⟨trace⟩ := concurrent_raw_trace reverse bit
  have signed := phaseSignedBindings_history runtime leaks CommitTimingInformation.plan
    (fixtureInputs bit) 4 selectedScheduler trace
  have binding := phaseBindingRecord_history runtime leaks CommitTimingInformation.plan
    (fixtureInputs bit) 4 selectedScheduler trace
  have recalled := app.history_inputRecall (fixtureInitial bit) 4 selectedScheduler trace
  have unique := app.uniqueIds_history selectedScheduler (fixtureInitial bit) 4 _ trace
  have clean (message : Message Player (CommitAttemptPacket graph))
      (input : message ∈ (afterBoth reverse bit).network.inputs) (_ : message.sender = owner) :
      PhaseCount.permits (afterBoth reverse bit).network.inputs message = true := by
    rw [pending_inputs] at input ⊢
    exact pending_permitted reverse bit message input
  have input : commitmentMessage owner ∈ (afterBoth reverse bit).network.inputs := by
    rw [pending_inputs]
    exact owner_message_pending reverse bit owner
  obtain ⟨_native, next, _handled, _completed, _accepted, _normalized, accepted⟩ :=
    PhaseCount.binding_accepted runtime leaks (afterBoth reverse bit) recalled owner clean
      signed unique binding.active.toAssociationInvariant (commitmentMessage owner) input rfl
      (bindingEvent owner) (owner, .prepared 0) rfl (pending_binding_request reverse bit owner)
      (pending_binding_timely reverse bit owner)
  exact ⟨next, accepted⟩

theorem correlated_order_and_epochs :
    (tape false).owner 0 0 = alice ∧ (tape true).owner 0 0 = bob ∧
      (tape false).processes 1 = true ∧ (tape true).processes 1 = false := by
  rw [tape_owner_first, tape_owner_first]
  decide

end Vegas.Examples.ReservedEpochConcurrency
