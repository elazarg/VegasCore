/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperPacketPermission
import Vegas.Examples.CommitSeedSignallingBobEarlyAcceptance
import Vegas.Pending.PhaseBindingService
import Vegas.Pending.PhaseBindingAcceptedReceipt

/-! # Actual accepting inclusion of the pending original helper -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- Before Bob's late block, the permitted visible initial envelope is all
of his actual signed traffic. Alice's raw traffic is unrestricted. -/
theorem helper_bob_own_permitted (seed : Seeds) (current : app.Control)
    (mixed : rawProtocol.Trace (some current))
    (fixed : (rawMenu.protocol initial horizon (family seed)).Trace (some current))
    (request : current.execution.application.SeedRequest alice (originalCoordinate alice))
    (early : current.execution.environmentRecall.length ≤ 12)
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ current.execution.network.inputs)
    (identified : message.id = (bob, 0)) (permitted : PhaseCount.permits [] message = true) :
    OwnPermitted bob current.execution := by
  have raw := rawMenu.toRawTrace initial horizon scheduler mixed
  refine ⟨PhaseCount.countRecall_history runtime leaks raw, ?_⟩
  intro other otherInput otherSender
  obtain ⟨entry, recorded, emitted, original, clock⟩ := bob_packet_before_late_origin seed current
    fixed request early other otherInput otherSender
  obtain ⟨first, _viewed, _allowed, materialized, _aliceRecorded⟩ :=
    bob_original_record_materialization current mixed entry recorded original clock
  rw [materialized] at emitted
  obtain ⟨material, _transmitted, packetEq⟩ := Option.map_eq_some_iff.mp emitted
  have otherId : other.id = (bob, 0) := by
    rw [← packetEq]
    rfl
  have same := app.input_identifier_injective_history initial horizon scheduler current raw
    other message otherInput input (otherId.trans identified.symm)
  rw [same]
  have verdict : PhaseCount.permits current.execution.network.inputs message =
      PhaseCount.permits [] message := by
    apply PhaseCount.permits_congr
    intro earlier
    constructor
    · intro prior
      have lower := prior.2.2
      rw [identified] at lower
      exact (Nat.not_lt_zero _ lower).elim
    · intro prior
      exact (List.not_mem_nil prior.1).elim
  exact verdict.trans permitted

/-- Slot five accepts the actual pending Bob envelope after Alice's real
count-admitted query-four response. No current accepting receipt, proper Bob
preparation, or globally counted foreign history is assumed. -/
theorem helper_pending_binding_accepted_next (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (mixed : rawProtocol.Trace (some ⟨remaining, some alice, execution⟩))
    (fixed : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (bit : seedBits seed alice = false)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ execution.network.inputs) (sender : message.sender = bob)
    (identified : message.id = (bob, 0)) (permitted : PhaseCount.permits [] message = true)
    (action : app.Action)
    (offered : action ∈ countedMenu.actions alice (execution.recall alice)
      (execution.observe app alice))
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.round (family seed) players
      (execution.respond app alice action)).support) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob final := by
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have count := original_first_late_input_index seed ⟨remaining, some alice, execution⟩ fixed
    alice rfl original clock
  change execution.environmentRecall.length = 4 + if seedBits seed alice then 3 else 1 at count
  rw [bit] at count
  simp only [Bool.false_eq_true, ite_false] at count
  have early : execution.environmentRecall.length ≤ 12 := by omega
  obtain ⟨entry, recorded, emitted, entryOriginal, entryClock⟩ :=
    bob_packet_before_late_origin seed ⟨remaining, some alice, execution⟩ fixed request
      early message input sender
  obtain ⟨_first, _viewed, _rawAllowed, materialized, _aliceRecorded⟩ :=
    bob_original_record_materialization ⟨remaining, some alice, execution⟩ mixed entry recorded
      entryOriginal entryClock
  have actualMaterial := emitted
  rw [materialized] at actualMaterial
  obtain ⟨material, transmitted, _packetEq⟩ := Option.map_eq_some_iff.mp actualMaterial
  obtain ⟨bobView, serial, preparation, evidence, shape, _bounded, _fresh⟩ :=
    bob_helper_record_binding_shape ⟨remaining, some alice, execution⟩ mixed quiet entry recorded
      entryOriginal entryClock material transmitted message emitted permitted
  have localPacket : PhaseCount.localEnvelope runtime leaks bob []
      ((bobFirst ⟨none⟩).observe app bob) material = message := by
    obtain ⟨first, view, _allowed, exactPacket, _retained⟩ :=
      bob_original_record_materialization ⟨remaining, some alice, execution⟩ mixed entry recorded
        entryOriginal entryClock
    rw [transmitted, Option.map_some] at exactPacket
    have samePacket := Option.some.inj (exactPacket.symm.trans emitted)
    have views : (bobFirst first).observe app bob = (bobFirst ⟨none⟩).observe app bob :=
      view.symm.trans bobView
    rw [views] at samePacket
    exact samePacket
  have called : message.payload.packet.call = .commitment bobBinding (bob, .prepared serial) := by
    rw [← localPacket]
    change (PhaseCount.maskPacket _ _).call = _
    rw [PhaseCount.maskPacket_call, shape]
  have addressed : message.payload.attempt = originalAttempt := by
    rw [← localPacket]
    exact initialState_attempt
  have own := helper_bob_own_permitted seed ⟨remaining, some alice, execution⟩ mixed fixed request
    early message input identified permitted
  let after := execution.respond app alice action
  have afterOwn : OwnPermitted bob after :=
    ownPermitted_respond bob alice execution action own (fun impossible =>
      ((by decide : alice ≠ bob) impossible).elim)
  have rawAllowed := PhaseCount.onePacketMenu_in_raw runtime leaks bounds alice _ _ offered
  obtain ⟨afterFixed⟩ := rawMenu.trace_respond initial horizon (family seed) remaining execution
    alice action fixed rawAllowed
  have afterRaw := rawMenu.toRawTrace initial horizon (family seed) afterFixed
  have afterCount : after.environmentRecall.length = 5 := by
    rw [ReactiveApplication.respond_environmentRecall]
    exact count
  have initialized := (rawMenu.roundSupported_uniform initial horizon (family seed) afterFixed).2
  change after ∈ (app.roundsFrom initial (family seed) rawMenu.uniformResponses
    after.environmentRecall.length).support at initialized
  rw [afterCount] at initialized
  have prior : after ∈ (app.runRounds (family seed) rawMenu.uniformResponses 5
      initialExecution).support := by
    simpa only [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind,
      initialExecution] using initialized
  have bobRequest := bob_request_before_helper rawMenu.uniformResponses seed after prior
  have afterOriginal : after.application.attempt = originalAttempt := bobRequest.1.symm
  have afterClock : after.application.current.native.clock = 2 := by
    have valid := raw_native_valid (family seed) ⟨remaining, some alice, execution⟩
      (rawMenu.toRawTrace initial horizon (family seed) fixed)
    exact (PhaseSeedCalendar.respond_clock runtime leaks execution valid alice action).trans clock
  have output : message ∈ app.outputs (execution.recall bob) := by
    rw [← own.1.1 bob]
    exact List.mem_filter.mpr ⟨input, by simp only [sender, decide_true]⟩
  have afterInput : message ∈ after.network.inputs := by
    have afterOutput : message ∈ app.outputs (after.recall bob) := by
      rw [app.respond_recall_other execution alice bob (by decide) action]
      exact output
    rw [← afterOwn.1.1 bob] at afterOutput
    exact (List.mem_filter.mp afterOutput).1
  have timer := original_timer (family seed) ⟨remaining, none, after⟩ afterRaw afterOriginal
    bobBinding (Or.inr rfl) bobRequest.2.2.1.1
  have timely : after.application.current.native.WithinDeadline runtime bobBinding := by
    rw [State.WithinDeadline, timer, afterClock]
    decide
  have packetRequest : after.application.SeedRequest message.sender
      ⟨message.payload.attempt, bobBinding⟩ := by
    have different : bob ≠ alice := by decide
    simpa only [sender, addressed, originalCoordinate, bindingEvent, different, ite_false]
      using bobRequest
  have signed := phaseSignedBindings_history runtime leaks plan (setup.initialLaw.map encodeInputs)
    horizon (family seed) afterRaw
  have binding := phaseBindingRecord_history runtime leaks plan (setup.initialLaw.map encodeInputs)
    horizon (family seed) afterRaw
  obtain ⟨native, next, nativeHandled, _completed, accepted, _normalized, handled⟩ :=
    PhaseCount.binding_accepted runtime leaks after afterOwn.1.1 bob afterOwn.2 signed
      (app.uniqueIds_history (family seed) initial horizon ⟨remaining, none, after⟩ afterRaw)
      binding.active.toAssociationInvariant message afterInput sender bobBinding
        (bob, .prepared serial) called packetRequest timely
  obtain ⟨snapshot, snapshotEq, snapshotInput⟩ := raw_clock_zero_packet_in_snapshot seed
    ⟨remaining, none, after⟩ afterRaw bob entry
      (app.respond_recall_mono execution alice bob action recorded) message emitted entryOriginal
        entryClock (by change 3 ≤ after.environmentRecall.length; omega)
  let predicate := fun packet : Message Player (CommitAttemptPacket graph) =>
    decide (packet.sender = bob ∧ packet.payload.attempt = originalAttempt)
  have selected : snapshot.beforeView.network.inputs.find? predicate = some message := by
    cases found : snapshot.beforeView.network.inputs.find? predicate with
    | none =>
        have absent := List.find?_eq_none.mp found message snapshotInput
        exact (absent (by simp only [predicate, sender, addressed, and_self, decide_true])).elim
    | some packet =>
        have pickedBool := List.find?_some found
        have picked : packet.sender = bob ∧ packet.payload.attempt = originalAttempt := by
          change decide (packet.sender = bob ∧ packet.payload.attempt = originalAttempt) = true
            at pickedBool
          exact of_decide_eq_true pickedBool
        have unique := first_snapshot_unique_owner rawMenu.uniformResponses seed 2 after prior
          snapshot snapshotEq bob packet message (List.mem_of_find?_eq_some found) snapshotInput
            picked.1 sender
        exact congrArg some unique
  have receiptsEmpty := original_receipts_before_helper seed ⟨remaining, none, after⟩ afterRaw
    afterOriginal (by change after.environmentRecall.length ≤ 5; exact Nat.le_of_eq afterCount)
  have retained := app.pendingOrPublished_history (family seed) initial horizon afterRaw
  have pending : message ∈ after.network.pending := by
    rcases retained.inputs message afterInput with present | published
    · exact present
    · have identifiers := app.receipt_identifiers_history initial horizon (family seed)
        ⟨remaining, none, after⟩ afterRaw
      have receiptId : message.id ∈ after.receipts.map Prod.fst := by
        rw [identifiers]
        exact List.mem_map.mpr ⟨message, published, rfl⟩
      rw [receiptsEmpty] at receiptId
      exact (List.not_mem_nil receiptId).elim
  have found : after.network.lookup message.id = some message := by
    cases lookup : after.network.lookup message.id with
    | none =>
        exact ((List.find?_eq_none.mp lookup message pending) (by simp only [decide_true])).elim
    | some packet =>
        have packetInput := (app.retained_envelopes_mem_inputs after
          (app.history_provenance initial horizon (family seed) afterRaw)
          (app.history_inputRecall initial horizon (family seed) afterRaw)).pending packet
            (List.mem_of_find?_eq_some lookup)
        have picked := List.find?_some lookup
        have sameId : packet.id = message.id := by
          change decide (packet.id = message.id) = true at picked
          exact of_decide_eq_true picked
        exact congrArg some (app.input_identifier_injective_history initial horizon (family seed)
          ⟨remaining, none, after⟩ afterRaw packet message packetInput afterInput sameId)
  have available : (after.observeEnvironment app).network.pending.any
      (fun packet => packet.id = message.id) = true :=
    List.any_eq_true.mpr ⟨message, pending, by simp only [decide_true]⟩
  have command : family seed after.environmentRecall (after.observeEnvironment app) =
      PMF.pure (.include message.id) := by
    rw [family_apply, choose_original seed _ _ afterOriginal, afterCount]
    change PMF.pure (earlyCommand bob _ _) = _
    unfold earlyCommand
    rw [snapshotEq]
    change PMF.pure (match snapshot.beforeView.network.inputs.find? predicate with
      | none => ReactiveApplication.Command.wait
      | some packet => pendingCommand packet.id (after.observeEnvironment app)) = _
    rw [selected]
    simp only [pendingCommand, available, ite_true]
  obtain ⟨actualNative, actualHandled, _normalized, receipt⟩ :=
    phase_inclusion_snapshot_bindingAccepted runtime leaks plan (setup.initialLaw.map encodeInputs)
      horizon (family seed) afterRaw message.id message found next handled
  have sameNative : actualNative = native := Option.some.inj
    (actualHandled.symm.trans nativeHandled)
  subst actualNative
  have trueReceipt : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      (after.includePending app message.id) := by
    have actual := receipt bobBinding (bob, .prepared serial) (by rw [afterOriginal]; decide)
      accepted
    change PhaseService.BindingAccepted runtime leaks ⟨after.application.attempt, bobBinding⟩ bob
      (after.includePending app message.id) at actual
    rw [afterOriginal] at actual
    change PhaseService.BindingAccepted runtime leaks ⟨originalAttempt, bobBinding⟩ bob
      (after.includePending app message.id)
    exact actual
  rw [ReactiveApplication.round, command, PMF.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind] at reached
  let included : app.Execution :=
    {after.includePending app message.id with environmentRecall := after.environmentRecall ++
      [⟨after.observeEnvironment app, .include message.id⟩]}
  change final ∈ (PMF.pure included).support at reached
  have finalEq := (PMF.mem_support_pure_iff _ _).mp reached
  subst final
  exact trueReceipt

end Vegas.Examples.CommitSeedSignalling
