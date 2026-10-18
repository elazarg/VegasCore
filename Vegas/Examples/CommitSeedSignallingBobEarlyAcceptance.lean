/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingInitialPollRequests
import Vegas.Examples.CommitSeedSignallingEarlySnapshot
import Vegas.Examples.CommitSeedSignallingTimingIncentives
import Vegas.Pending.PhaseCountedSurvivor
import Vegas.Pending.PhaseBindingAcceptedReceipt
import Interaction.ReactiveTrafficIdentity

/-! # Actual admission of Bob's arbitrary counted early declaration -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

theorem bob_request_before_helper (players : Player → app.Policy)
    (seed : Seeds) (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (family seed) players 5 initialExecution).support) :
    execution.application.SeedRequest bob (originalCoordinate bob) := by
  rw [app.runRounds_succ_eq_bind_round, PMF.support_bind] at reached
  obtain ⟨before, prior, moved⟩ := Set.mem_iUnion₂.mp reached
  have requested := original_request_before_first_poll players seed 4 le_rfl before prior bob
  have original : before.application.attempt = originalAttempt := requested.1.symm
  have length := app.runRounds_environmentRecall_length (family seed) players 4 initialExecution
    before prior
  have count : before.environmentRecall.length = 4 := by
    simpa only [initialExecution, ReactiveApplication.Execution.initial, List.length_nil,
      Nat.zero_add] using length
  obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
  have chosen : command = pollCommand alice (seedBits seed alice) false
      (before.observeEnvironment app) := by
    rw [family_first_late_command seed alice _ _ original count] at selected
    exact (PMF.mem_support_pure_iff _ _).mp selected
  obtain ⟨observed, environmentMoved, resumed⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have sameApplication : observed.application = before.application := by
    rw [chosen] at environmentMoved
    unfold pollCommand at environmentMoved
    split at environmentMoved
    · unfold activateReady at environmentMoved
      split at environmentMoved
      · rw [completeActivation_law] at environmentMoved
        cases (PMF.mem_support_pure_iff _ _).mp environmentMoved
        rfl
      · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at environmentMoved
        cases (PMF.mem_support_pure_iff _ _).mp environmentMoved
        rfl
    · simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at environmentMoved
      cases (PMF.mem_support_pure_iff _ _).mp environmentMoved
      rfl
  have observedRequest : observed.application.SeedRequest bob (originalCoordinate bob) := by
    rwa [sameApplication]
  cases actor : command.actor? app with
  | none =>
      change execution ∈ (app.resume players (command.actor? app) observed).support at resumed
      rw [actor] at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      exact observedRequest
  | some who =>
      change execution ∈ (app.resume players (command.actor? app) observed).support at resumed
      rw [actor] at resumed
      obtain ⟨action, _chosen, rfl⟩ := PMF.support_map .. ▸ resumed
      exact respond_request runtime leaks observed who action bob _ observedRequest

section Counted

variable (profile : ∀ who, countedModel.BehavioralPolicy who)

local notation "players" => countedMenu.decodeProfile initial horizon scheduler profile

private theorem first_two_early_rounds (seed : Seeds) (material : app.Submission)
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobEarly : players bob [] ((bobFirst ⟨none⟩).observe app bob) =
      PMF.pure ⟨some material⟩) :
    app.runRounds (family seed) players 2 initialExecution =
      PMF.pure (afterFirstTwo ⟨none⟩ ⟨some material⟩) := by
  rw [first_two_rounds, aliceWait, PMF.pure_bind, bobEarly, PMF.pure_map]

/-- The original helper turn accepts every supported counted initial Bob
transmission. Its preparation and evidence are retained without a success
condition, and Alice's late response remains arbitrary. -/
theorem bob_early_binding_accepted_six (seed : Seeds) (material : app.Submission)
    (aliceWait : players alice [] (aliceFirst.observe app alice) = PMF.pure ⟨none⟩)
    (bobEarly : players bob [] ((bobFirst ⟨none⟩).observe app bob) =
      PMF.pure ⟨some material⟩)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players 6 initialExecution).support) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob final := by
  classical
  have offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions bob
      ((bobFirst ⟨none⟩).recall bob) ((bobFirst ⟨none⟩).observe app bob) := by
    apply countedMenu.decode_embedPolicy_covered initial horizon scheduler bob (profile bob)
    change (⟨some material⟩ : app.Action) ∈
      (players bob [] ((bobFirst ⟨none⟩).observe app bob)).support
    rw [bobEarly]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨serial, preparation, evidence, declared, _bounded, _fresh⟩ :=
    bobQuiet_counted_binding_shape material offered
  rw [app.runRounds_succ_eq_bind_round, PMF.support_bind] at reached
  obtain ⟨execution, beforeReached, future⟩ := Set.mem_iUnion₂.mp reached
  have request := bob_request_before_helper players seed execution beforeReached
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have length := app.runRounds_environmentRecall_length (family seed) players 5 initialExecution
    execution beforeReached
  have position : execution.environmentRecall.length = 5 := by
    simpa only [initialExecution, ReactiveApplication.Execution.initial, List.length_nil,
      Nat.zero_add] using length
  obtain ⟨trace⟩ := counted_profile_trace profile seed 5 (by decide) execution beforeReached
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  let first := bobFirst ⟨none⟩
  let action : app.Action := ⟨some material⟩
  let entry := originalResponseEntry first bob action
  let message : Message Player (CommitAttemptPacket graph) :=
    ⟨(bob, first.network.nextSerial bob),
      app.packet (app.submit first.application bob material) bob
        (first.network.known bob) material⟩
  have emitted : entry.emitted = some message := rfl
  have sender : message.sender = bob := rfl
  have attempt : message.payload.attempt = originalAttempt := by
    change ((first.application.submit bob material).emit bob
      (first.network.known bob) material).attempt = originalAttempt
    rw [PhaseCount.emit_after_submit]
    exact initialState_attempt
  have called : message.payload.packet.call = .commitment bobBinding (bob, .prepared serial) := by
    change ((first.application.submit bob material).emit bob
      (first.network.known bob) material).packet.call = _
    rw [phase_emit_call, declared]
  have past : execution ∈ (app.runRounds (family seed) players 3
      (afterFirstTwo ⟨none⟩ ⟨some material⟩)).support := by
    rw [show 5 = 2 + 3 by rfl, app.runRounds_add,
      first_two_early_rounds profile seed material aliceWait bobEarly, PMF.pure_bind]
        at beforeReached
    exact beforeReached
  have retained : entry ∈ execution.recall bob := by
    let property : app.Execution → Prop := fun next => entry ∈ next.recall bob
    have invariant : app.ServiceInvariant (family seed) property := {
      respond := fun next actor response present =>
        (app.respond_recall_mono next actor bob response) present
      environment := fun next after command present _selected moved => by
        change entry ∈ after.recall bob
        rw [app.environmentStep_recall next after command moved]
        exact present }
    apply invariant.runRounds players 3 (afterFirstTwo ⟨none⟩ ⟨some material⟩) execution _ past
    change entry ∈ (first.respond app bob action).recall bob
    rw [respond_originalResponseEntry]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have entryOriginal : entry.beforeView.application.2.attempt = originalAttempt :=
    initialState_attempt
  have entryZero : entry.beforeView.application.1.publicView.clock = 0 := initialState_clock
  have snapshotLength :
      3 ≤ (⟨59, none, execution⟩ : app.Control).execution.environmentRecall.length := by
    change 3 ≤ execution.environmentRecall.length
    omega
  obtain ⟨snapshot, snapshotEq, snapshotInput⟩ := raw_clock_zero_packet_in_snapshot seed
    ⟨59, none, execution⟩ raw bob entry retained message emitted entryOriginal entryZero
      snapshotLength
  let predicate := fun packet : Message Player (CommitAttemptPacket graph) =>
    decide (packet.sender = bob ∧ packet.payload.attempt = originalAttempt)
  have findEarly : snapshot.beforeView.network.inputs.find? predicate = some message := by
    cases selected : snapshot.beforeView.network.inputs.find? predicate with
    | none =>
        have absent := List.find?_eq_none.mp selected message snapshotInput
        exact (absent (by simp only [predicate, sender, attempt, and_self, decide_true])).elim
    | some packet =>
        have packetInput := List.mem_of_find?_eq_some selected
        have picked := List.find?_some selected
        have stamp : packet.sender = bob ∧ packet.payload.attempt = originalAttempt := by
          exact of_decide_eq_true picked
        have unique := first_snapshot_unique_owner players seed 2 execution beforeReached
          snapshot snapshotEq bob packet message packetInput snapshotInput stamp.1 sender
        exact congrArg some unique
  have input : message ∈ execution.network.inputs := by
    have remembered := app.history_inputRecall initial horizon (family seed) raw bob
    have output : message ∈ app.outputs (execution.recall bob) :=
      List.mem_filterMap.mpr ⟨entry, retained, emitted⟩
    rw [← remembered] at output
    exact (List.mem_filter.mp output).1
  have clock := original_clock_index seed ⟨59, none, execution⟩ raw original
  rw [position] at clock
  have clockTwo : execution.application.current.native.clock = 2 := clock
  have timer := original_timer (family seed) ⟨59, none, execution⟩ raw original bobBinding
    (Or.inr rfl) request.2.2.1.1
  have timely : execution.application.current.native.WithinDeadline runtime bobBinding := by
    rw [State.WithinDeadline, timer, clockTwo]
    decide
  have packetRequest : execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, bobBinding⟩ := by
    have different : bob ≠ alice := by decide
    simpa only [sender, attempt, originalCoordinate, bindingEvent, different, ite_false]
      using request
  have named : message.payload.packet.call.event? graph = some bobBinding := by
    rw [called]
    rfl
  have pending := PhaseCount.survivor_pending runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup .concurrentReveals)
    (compiledRuntimePhasePlan_maximal program .concurrentReveals)
    (setup.initialLaw.map encodeInputs) horizon (family seed) ⟨59, none, execution⟩ trace message
      input bobBinding named packetRequest timely
  have found : execution.network.lookup message.id = some message := by
    cases selected : execution.network.lookup message.id with
    | none =>
        have absent := List.find?_eq_none.mp selected message pending
        exact (absent (by simp only [decide_true])).elim
    | some packet =>
        have packetPending := List.mem_of_find?_eq_some selected
        have packetInput := (app.retained_envelopes_mem_inputs execution
          (app.history_provenance initial horizon (family seed) raw)
          (app.history_inputRecall initial horizon (family seed) raw)).pending packet packetPending
        have picked := List.find?_some selected
        have identified : packet.id = message.id := of_decide_eq_true picked
        have same := app.input_identifier_injective_history initial horizon (family seed)
          ⟨59, none, execution⟩ raw packet message packetInput input identified
        exact congrArg some same
  have available : (execution.observeEnvironment app).network.pending.any
      (fun packet => packet.id = message.id) = true :=
    List.any_eq_true.mpr ⟨message, pending, by simp only [decide_true]⟩
  have command : family seed execution.environmentRecall (execution.observeEnvironment app) =
      PMF.pure (.include message.id) := by
    rw [family_apply, choose_original seed _ _ original, position]
    change PMF.pure (earlyCommand bob _ _) = _
    unfold earlyCommand
    rw [snapshotEq]
    change PMF.pure (match snapshot.beforeView.network.inputs.find? predicate with
      | none => ReactiveApplication.Command.wait
      | some packet => pendingCommand packet.id (execution.observeEnvironment app)) = _
    rw [findEarly]
    simp only [pendingCommand, available, ite_true]
  obtain ⟨native, next, nativeHandled, _completed, accepted, _normalized, phaseHandled⟩ :=
    PhaseCount.binding_accepted_of_history runtime leaks bounds plan
      (setup.initialLaw.map encodeInputs) horizon (family seed) trace message input bobBinding
        (bob, .prepared serial) called packetRequest timely
  obtain ⟨actualNative, actualHandled, _actualNormalized, receipt⟩ :=
    phase_inclusion_snapshot_bindingAccepted runtime leaks plan (setup.initialLaw.map encodeInputs)
      horizon (family seed) raw message.id message found next phaseHandled
  have sameNative : actualNative = native :=
    Option.some.inj (actualHandled.symm.trans nativeHandled)
  subst actualNative
  have trueReceipt : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      (execution.includePending app message.id) := by
    have actual := receipt bobBinding (bob, .prepared serial) (by rw [original]; decide) accepted
    have different : bob ≠ alice := by decide
    simpa only [original, originalCoordinate, bindingEvent, different, ite_false] using actual
  rw [ReactiveApplication.round, command, PMF.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind] at future
  let included : app.Execution :=
    {execution.includePending app message.id with environmentRecall :=
      execution.environmentRecall ++
        [⟨execution.observeEnvironment app, .include message.id⟩]}
  change final ∈ (PMF.pure included).support at future
  have finalEq := (PMF.mem_support_pure_iff _ _).mp future
  subst final
  exact trueReceipt

end Counted

end Vegas.Examples.CommitSeedSignalling
