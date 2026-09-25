/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationNativeDeviation
import Vegas.Pending.ReactiveAuthorization

/-! # Readiness restrictions do not remove candidate certificates

The selective-association fixture discloses its certificate on a commitment
call. That event is already dependency-ready, within its deadline, and would
accept the packet immediately. The service grant is merely a cursor; it is
not a precondition of the call handler. No opening call is needed before the
later accepted association. Bob may remain silent in the intervening response.

These results certify operational capabilities of the existing runtime. They
do not transfer the sequential-equilibrium separation to a game with restricted
menus: deleting actions changes the rationality premises of that theorem.
-/

noncomputable section

namespace VegasTests.ReactiveReadinessRestrictions

open GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime
open SelectiveAssociation ReactiveAssociationEvidence

def certifiedEnvelope (bit : Bool) : Message Player (WitnessedPacket nativeGraph) :=
  ⟨(alice, 0), ⟨.commitment aliceBinding candidate, some (opening bit)⟩⟩

def associationEnvelope : Message Player (WitnessedPacket nativeGraph) :=
  ⟨(alice, 1), ⟨.commitment aliceBinding candidate, none⟩⟩

def PendingEventsReady (execution : nativeApp.Execution) : Prop :=
  ∀ message ∈ execution.network.pending, ∃ event,
    message.payload.call.event? nativeGraph = some event ∧
      execution.application.config.cut.Ready event

def PendingCallsSucceed (execution : nativeApp.Execution) : Prop :=
  ∀ message ∈ execution.network.pending,
    (nativeApp.handle execution.application message).isSome = true

def OnlyCommitmentCalls (execution : nativeApp.Execution) : Prop :=
  ∀ message ∈ execution.network.pending, ∃ event handle,
    message.payload.call = .commitment event handle

/-- All three players' initial binding events are concurrent dependencies.
An early Bob binding is not premature merely because his grant comes later. -/
theorem initial_bindings_ready :
    nativeInitial.config.cut.Ready aliceBinding ∧
      nativeInitial.config.cut.Ready bobBinding ∧
      nativeInitial.config.cut.Ready carolBinding := by
  decide

theorem first_pending (bit : Bool) :
    (first bit).network.pending = [certifiedEnvelope bit] := by
  cases bit <;> rfl

theorem offered_pending (bit : Bool) :
    (offeredAfter bit ⟨none⟩).network.pending =
      [certifiedEnvelope bit, associationEnvelope] := by
  cases bit <;> rfl

theorem first_event_ready (bit : Bool) :
    (first bit).application.config.cut.Ready aliceBinding := by
  cases bit <;> decide

/-- The certificate-carrying call can succeed immediately after submission,
even though the service has not yet issued Alice's binding grant. -/
theorem first_call_succeeds (bit : Bool) (serial : Nat) :
    (handle nativeRuntime (first bit).application
      ⟨(alice, serial), .commitment aliceBinding candidate⟩).isSome = true := by
  have unused : (first bit).application.HandleUnused candidate := by
    intro field
    cases field with
    | inl input => exact Fin.elim0 input
    | inr event =>
        change (none : Option (Handle nativeGraph)) ≠ some candidate
        simp
  rw [handle_commitment_eq nativeRuntime (first bit).application (alice, serial)
    aliceBinding candidate alice .bool rfl rfl rfl (first_event_ready bit)
    (by change 0 < 1; decide) rfl rfl rfl unused]
  rfl

theorem offered_application (bit : Bool) :
    (offeredAfter bit ⟨none⟩).application =
      { (first bit).application with serviceGrant := some aliceBinding } := by
  cases bit <;> rfl

theorem offered_call_succeeds (bit : Bool) (serial : Nat) :
    (handle nativeRuntime (offeredAfter bit ⟨none⟩).application
      ⟨(alice, serial), .commitment aliceBinding candidate⟩).isSome = true := by
  rw [offered_application, handle_serviceGrant_update]
  simpa using first_call_succeeds bit serial

theorem first_pending_ready_and_successful (bit : Bool) :
    PendingEventsReady (first bit) ∧ PendingCallsSucceed (first bit) ∧
      OnlyCommitmentCalls (first bit) ∧ (first bit).application.serviceGrant = none := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · intro message member
    rw [first_pending] at member
    rcases List.mem_singleton.mp member with rfl
    exact ⟨aliceBinding, rfl, first_event_ready bit⟩
  · intro message member
    rw [first_pending] at member
    rcases List.mem_singleton.mp member with rfl
    exact first_call_succeeds bit 0
  · intro message member
    rw [first_pending] at member
    rcases List.mem_singleton.mp member with rfl
    exact ⟨aliceBinding, candidate, rfl⟩

/-- Both competing packets remain ready and successful before one is selected.
They differ in certificate attachment, not in the addressed event. -/
theorem offered_pending_ready_and_successful (bit : Bool) :
    PendingEventsReady (offeredAfter bit ⟨none⟩) ∧
      PendingCallsSucceed (offeredAfter bit ⟨none⟩) ∧
      OnlyCommitmentCalls (offeredAfter bit ⟨none⟩) := by
  have ready : (offeredAfter bit ⟨none⟩).application.config.cut.Ready aliceBinding := by
    rw [offered_application]
    exact first_event_ready bit
  refine ⟨?_, ?_, ?_⟩
  · intro message member
    rw [offered_pending] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨aliceBinding, rfl, ready⟩
  · intro message member
    rw [offered_pending] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact offered_call_succeeds bit 0
    · exact offered_call_succeeds bit 1
  · intro message member
    rw [offered_pending] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨aliceBinding, candidate, rfl⟩

/-- Dependency authorization admits this original certificate envelope;
authorization does not inspect or strip its certificate. -/
theorem certified_submission_authorized (bit : Bool) :
    (first bit).AuthorizedAtSubmission nativeApp
      (nativeRuntime.submissionDependencyCondition nativeLeaks) (certifiedEnvelope bit) := by
  have ready : activatedInitial.application.publicView.EventReady aliceBinding := by
    rw [State.publicView_eventReady]
    exact initial_bindings_ready.1
  have permitted := nativeRuntime.ready_submission_authorized nativeLeaks
    activatedInitial alice
    ⟨⟨.commitment aliceBinding candidate, some ⟨.bool, bit⟩⟩, .owned (opening bit)⟩
    aliceBinding rfl ready rfl
  convert permitted using 1 <;> cases bit <;> rfl

def silentPlayers : Player → nativeApp.Policy := fun _ _ _ => FinDist.pure ⟨none⟩

/-- This is the actual first five service rounds. Bob sends nothing; the
certificate is learned passively, before Alice's certificate-free inclusion. -/
theorem silent_bob_prefix :
    nativeApp.runRounds nativeScheduler (nativeAliceProfile silentPlayers) 5 nativeRoot =
      (FinDist.uniformOfFintype (α := Bool)).map (fun bit => includedAfter bit ⟨none⟩) := by
  have bridge := native_prefix_rounds (nativeAliceProfile silentPlayers)
    (nativePlan.take 5) (nativePlan.drop 5) (by simp)
  change nativeApp.runRounds nativeScheduler (nativeAliceProfile silentPlayers) 5 nativeRoot = _
    at bridge
  rw [bridge]
  change nativeRuntime.runInteractionPlan nativeLeaks (nativeAliceProfile silentPlayers)
    nativeNetwork [.player alice, .player bob, .grant aliceBinding, .player alice,
      .includeLatest aliceBinding alice] initial = _
  rw [runInteractionPlan, native_alice_first_round, FinDist.bind_map]
  rw [FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro bit _
  rw [runInteractionPlan, native_alice_bob_round]
  simp only [silentPlayers, FinDist.map_pure, FinDist.pure_bind]
  change nativeRuntime.runInteractionPlan nativeLeaks (nativeAliceProfile silentPlayers)
    nativeNetwork ([.grant aliceBinding, .player alice] ++
      [.includeLatest aliceBinding alice]) (reacted bit ⟨none⟩) = _
  rw [runInteractionPlan_append, native_alice_offer_rounds, FinDist.pure_bind,
    runInteractionPlan, native_alice_include_round, FinDist.pure_bind]
  rfl

/-- Selective, subsequently associated evidence survives the absence of every
premature opening call, and even immediate acceptability of every offered call.
This is an operational witness, not an equilibrium transfer theorem. -/
theorem disclosure_with_ready_commitment_calls (bit : Bool) :
    PendingEventsReady (first bit) ∧ PendingCallsSucceed (first bit) ∧
      OnlyCommitmentCalls (first bit) ∧
      PendingEventsReady (offeredAfter bit ⟨none⟩) ∧
      PendingCallsSucceed (offeredAfter bit ⟨none⟩) ∧
      OnlyCommitmentCalls (offeredAfter bit ⟨none⟩) ∧
      opening bit ∈ (nativeRuntime.packetEvidence nativeLeaks).observe
        ((observed bit).observe nativeApp bob) ∧
      nativeRuntime.bindingEvidenceObserved nativeLeaks
        ((includedAfter bit ⟨none⟩).observe nativeApp bob) (named bit) ∧
      (includedAfter false ⟨none⟩).observe nativeApp carol =
        (includedAfter true ⟨none⟩).observe nativeApp carol := by
  have firstReady := first_pending_ready_and_successful bit
  have offeredReady := offered_pending_ready_and_successful bit
  exact ⟨firstReady.1, firstReady.2.1, firstReady.2.2.1,
    offeredReady.1, offeredReady.2.1, offeredReady.2.2,
    (proof_before_association bit).1, (association_after_arbitrary_response bit ⟨none⟩).2,
    congrArg Prod.snd (carol_input_after_arbitrary_responses ⟨none⟩ ⟨none⟩)⟩

theorem included_binding_completed (bit : Bool) :
    aliceBinding ∈ (includedAfter bit ⟨none⟩).application.config.cut.completed := by
  have accepts : (nativeApp.handle (offeredAfter bit ⟨none⟩).application
      associationEnvelope).isSome = true := offered_call_succeeds bit 1
  obtain ⟨next, accepted⟩ := Option.isSome_iff_exists.mp accepts
  have lookup : (offeredAfter bit ⟨none⟩).network.lookup (alice, 1) =
      some associationEnvelope := by
    cases bit <;> rfl
  have nextState : (includedAfter bit ⟨none⟩).application = next := by
    unfold includedAfter ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [lookup]
    change (nativeApp.handle _ associationEnvelope).getD _ = next
    rw [accepted]
    rfl
  rw [nextState]
  obtain ⟨event, address, ready, action, reached⟩ :=
    nativeRuntime.handle_config_mem_step (offeredAfter bit ⟨none⟩).application next
      ⟨associationEnvelope.id, associationEnvelope.payload.call⟩ accepted
  have same : aliceBinding = event := Option.some.inj address
  subst event
  rw [(offeredAfter bit ⟨none⟩).application.config.step_cut aliceBinding ready action next.config
    reached]
  exact Finset.mem_insert_self _ _

/-- Inclusion of a winner leaves its losing competitor in the ordinary pool.
Readiness checked at submission is therefore not a persistent pool invariant. -/
theorem accepted_winner_leaves_unready_competitor (bit : Bool) :
    certifiedEnvelope bit ∈ (includedAfter bit ⟨none⟩).network.pending ∧
      ¬ PendingEventsReady (includedAfter bit ⟨none⟩) ∧
      nativeApp.handle (includedAfter bit ⟨none⟩).application (certifiedEnvelope bit) = none := by
  have pending : certifiedEnvelope bit ∈ (includedAfter bit ⟨none⟩).network.pending := by
    cases bit <;> exact List.mem_singleton_self _
  have notReady : ¬ (includedAfter bit ⟨none⟩).application.config.cut.Ready aliceBinding :=
    fun ready => ready.1 (included_binding_completed bit)
  refine ⟨pending, ?_, ?_⟩
  · intro allReady
    obtain ⟨event, address, ready⟩ := allReady _ pending
    have same : aliceBinding = event := Option.some.inj address
    apply notReady
    simpa only [← same] using ready
  · change handle nativeRuntime (includedAfter bit ⟨none⟩).application
      ⟨(alice, 0), .commitment aliceBinding candidate⟩ = none
    simp only [handle]
    split
    · exact (notReady ‹_›).elim
    · rfl

/-- A clock step may leave dependencies ready while making the same call
inadmissible. Dependency readiness and successful execution are distinct. -/
theorem readiness_survives_deadline_but_acceptance_does_not (bit : Bool) :
    let aged : State nativeGraph := { (first bit).application with clock := 1 }
    environmentStep nativeRuntime (first bit).application .advanceClock = FinDist.pure aged ∧
      aged.config.cut.Ready aliceBinding ∧
      handle nativeRuntime aged ⟨(alice, 0), .commitment aliceBinding candidate⟩ = none := by
  dsimp only
  refine ⟨?_, first_event_ready bit, ?_⟩
  · cases bit <;> rfl
  · have late : ¬ ({ (first bit).application with clock := 1 } : State nativeGraph).WithinDeadline
        nativeRuntime aliceBinding := by
      change ¬ 1 - 0 < 1
      decide
    simp only [handle]
    split <;> rfl

/-- Changing the pool does not erase a player's prior inputs or observations.
The scheduler does see the pool, so this equality makes no claim about future
execution or equilibrium. -/
theorem pending_replacement_preserves_player_input (execution : nativeApp.Execution)
    (pending : List (Message Player (WitnessedPacket nativeGraph))) (who : Player) :
    let replaced : nativeApp.Execution :=
      { execution with network := { execution.network with pending := pending } }
    (replaced.recall who, replaced.observe nativeApp who) =
      (execution.recall who, execution.observe nativeApp who) := rfl

/-- Clearing stale competitors after the accepted association satisfies the
pool predicates and retains Bob's certified knowledge and Carol's identical
inputs. This is a cleanup state calculation, not a new runtime transition. -/
theorem empty_pool_cleanup_preserves_asymmetry (bit : Bool) :
    let cleaned (value : Bool) : nativeApp.Execution :=
      { includedAfter value ⟨none⟩ with
        network := { (includedAfter value ⟨none⟩).network with pending := [] } }
    PendingEventsReady (cleaned bit) ∧ PendingCallsSucceed (cleaned bit) ∧
      nativeRuntime.bindingEvidenceObserved nativeLeaks
        ((cleaned bit).observe nativeApp bob) (named bit) ∧
      ((cleaned false).recall carol, (cleaned false).observe nativeApp carol) =
        ((cleaned true).recall carol, (cleaned true).observe nativeApp carol) := by
  refine ⟨?_, ?_, (association_after_arbitrary_response bit ⟨none⟩).2,
    carol_input_after_arbitrary_responses ⟨none⟩ ⟨none⟩⟩
  · intro _ member
    exact (List.not_mem_nil member).elim
  · intro _ member
    exact (List.not_mem_nil member).elim

end VegasTests.ReactiveReadinessRestrictions
