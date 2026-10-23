/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochPublicationEmission

/-! # The actual old publication emission and receipt word -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs

local notation "cycles" => ReservedEpoch.completionCycles runtime

/-- The original old UNSENT opening has exactly its first-offer emission bit.
Late SENDs remain in the literal proposal archive independently of receipt. -/
theorem phaseProposalUnflagged_stopped_unsent_opening_emission_word
    (ordered : (graph).RevealRelaxedOrdered)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (remaining closedRemaining count : Nat) (owner : Player)
    (before closed : (app).Execution)
    (trace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.horizon («graph» := graph) cycles)
      (ReservedEpoch.family runtime leaks
        (ReservedEpoch.submissionBudget (Player := Player) cycles) tape)).Trace
          (some ⟨remaining, none, before⟩))
    (closedTrace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.horizon («graph» := graph) cycles)
      (ReservedEpoch.family runtime leaks
        (ReservedEpoch.submissionBudget (Player := Player) cycles) tape)).Trace
          (some ⟨closedRemaining, none, closed⟩))
    (kept : TracePrefix trace closedTrace)
    (retired : closed.application.attempt ≠ before.application.attempt)
    (event : (graph).EventId) (payload : L.Ty)
    (binding : FieldRef (graph).layout (.binding owner payload))
    (checks : List (GuardCheck (graph).layout payload))
    (outputEq : (graph).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph).layout) outputEq) ((graph).nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (value : L.Val payload)
    (stored : binding.get? before.application.current.native.config.store = some (.success value))
    (bounded : (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (request : before.application.SeedRequest owner ⟨before.application.attempt, event⟩)
    (entered : Nat) (stamp : before.application.current.native.activatedAt event = some entered)
    (unsent : ∀ message ∈ (app).outputs (before.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨before.application.attempt, event⟩)
    (positive : 0 < runtime.deadline event)
    (path : closed ∈ ((app).runRounds (ReservedEpoch.family runtime leaks
      (ReservedEpoch.submissionBudget (Player := Player) cycles) tape)
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) count
          before).support) :
    (∃ message ∈ closed.network.inputs, message.sender = owner ∧
      PhaseProposal.packetProposal? message.payload =
        some (⟨before.application.attempt, event⟩, (⟨payload, value⟩ : Raw L))) ↔
      ReservedEpoch.openingFrontierEmission runtime leaks tape before owner event := by
  classical
  let initial := (inputs).map (PhaseRuntimeState.initial plan)
  let horizon := ReservedEpoch.executionHorizon runtime
  let budget := ReservedEpoch.packetCapacity runtime
  let scheduler := ReservedEpoch.family runtime leaks budget tape
  let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
  have closedBudget := (app).raw_trace_horizon initial horizon scheduler
    ((menu).toRawTrace initial horizon scheduler closedTrace)
  have startBudget := (app).raw_trace_horizon initial horizon scheduler
    ((menu).toRawTrace initial horizon scheduler trace)
  have elapsed := (app).runRounds_environmentRecall_length scheduler players count before closed
    path
  have lengths : count + closedRemaining = remaining := by
    change before.environmentRecall.length + remaining = horizon at startBudget
    change closed.environmentRecall.length + closedRemaining = horizon at closedBudget
    omega
  rcases phaseProposalUnflagged_stopped_unsent_opening setup mode runtime leaks bounds plan ordered
    values cycles tape remaining closedRemaining count owner before closed trace closedTrace kept
      retired event payload binding checks outputEq codeEq node value stored bounded request entered
        stamp unsent positive path with
    ⟨cursor, lower, upper, expiredNow, dueNow, quiet, _open, _failed,
      used, tail, due, expired, split, dueCursor, initialPath, expiry, resolved, future⟩ |
    ⟨used, tail, activeRemaining, offered, active, response, material, candidate, split,
      initialPath, activation, moved, _chosen, _sent, call, _accepted, _archive, sameAttempt,
      _activeStamp, _recalled, quiet, expiryOpen, _activeTrace, input, _receipt⟩
  · have noEmission := ReservedEpoch.openingFrontierEmission_false_of_due runtime leaks tape before
      owner event entered cursor stamp unsent lower expiredNow dueNow quiet
    refine iff_of_false ?_ noEmission
    rintro ⟨message, input, sender, proposed⟩
    have selected : ReservedEpoch.command runtime leaks budget tape due.environmentRecall.length
        (due.observeEnvironment app) = .application (.expire event) := by
      rw [dueCursor]
      exact expiredNow _
    have noPacket := ReservedEpoch.old_due_counted_packet_absent runtime leaks cycles tape bounds
      plan ordered inputs players (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks
        bounds plan values) remaining closedRemaining used tail before due expired closed trace
          (by omega) owner ⟨before.application.attempt, event⟩ unsent (by
            intro earlier lower upper view
            have elapsed := (app).runRounds_environmentRecall_length scheduler players used before
              due initialPath
            exact quiet earlier lower (by omega) view) initialPath selected expiry resolved future
    obtain ⟨address, candidate, call⟩ := PhaseProposal.opening_of_packetProposal message.payload
      ⟨before.application.attempt, event⟩ (⟨payload, value⟩ : Raw L) proposed
    exact noPacket message input sender (by simp only [PhaseCount.event?, call, Payload.event?,
      address, Option.map_some])
  · let message : Message Player (CommitAttemptPacket graph) :=
      ⟨(owner, active.network.nextSerial owner),
        (app).packet ((app).submit active.application owner material) owner
          (active.network.known owner) material⟩
    have emitted : message.payload.packet.call = .opening event candidate ⟨payload, value⟩ := by
      change (PhaseRuntimeState.emit (active.application.submit owner material) owner
        (active.network.known owner) material).packet.call = _
      rw [phase_emit_call, call]
    have addressed : message.payload.attempt = active.application.attempt := rfl
    have existsPacket : ∃ message ∈ closed.network.inputs, message.sender = owner ∧
        PhaseProposal.packetProposal? message.payload =
          some (⟨before.application.attempt, event⟩, (⟨payload, value⟩ : Raw L)) := by
      exact ⟨message, input, rfl, by
        simp only [PhaseProposal.packetProposal?, emitted, addressed, sameAttempt]⟩
    have frontier : ReservedEpoch.openingFrontierEmission runtime leaks tape before owner event :=
        by
      apply Or.inr
      refine ⟨entered, stamp, offered.environmentRecall.length, ?_, ?_, ?_, ?_, ?_⟩
      · have := (app).runRounds_environmentRecall_length scheduler players used before offered
          initialPath
        omega
      · have first := (app).runRounds_environmentRecall_length scheduler players used before offered
          initialPath
        change closed.environmentRecall.length + closedRemaining = horizon at closedBudget
        omega
      · intro view
        have acting : (ReservedEpoch.command runtime leaks budget tape
            offered.environmentRecall.length (offered.observeEnvironment app)).actor? app =
            some owner := by
          change (ReservedEpoch.command runtime leaks
            (ReservedEpoch.submissionBudget (Player := Player) cycles) tape
              offered.environmentRecall.length (offered.observeEnvironment app)).actor? app = _
          rw [activation]
          rfl
        exact (ReservedEpoch.command_actor_view_independent runtime leaks budget tape
          offered.environmentRecall.length view (offered.observeEnvironment app)).trans acting
      · intro earlier lower upper view
        have := (app).runRounds_environmentRecall_length scheduler players used before offered
          initialPath
        exact quiet earlier lower (by omega) view
      · intro earlier lower upper view selected
        have := (app).runRounds_environmentRecall_length scheduler players used before offered
          initialPath
        exact expiryOpen earlier lower (by omega) view selected
    exact iff_of_true existsPacket frontier

/-- The full old ready receipt bit includes UNSENT, genuinely pending, and
permanently FALSE-receipted opening episodes at the original phase exit. -/
theorem phaseProposalUnflagged_stopped_old_opening_receipt_word
    (ordered : (graph).RevealRelaxedOrdered)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (remaining closedRemaining count : Nat) (owner : Player)
    (before closed : (app).Execution)
    (trace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.horizon («graph» := graph) cycles)
      (ReservedEpoch.family runtime leaks
        (ReservedEpoch.submissionBudget (Player := Player) cycles) tape)).Trace
          (some ⟨remaining, none, before⟩))
    (closedTrace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.horizon («graph» := graph) cycles)
      (ReservedEpoch.family runtime leaks
        (ReservedEpoch.submissionBudget (Player := Player) cycles) tape)).Trace
          (some ⟨closedRemaining, none, closed⟩))
    (kept : TracePrefix trace closedTrace)
    (retired : closed.application.attempt ≠ before.application.attempt)
    (event : (graph).EventId) (payload : L.Ty)
    (binding : FieldRef (graph).layout (.binding owner payload))
    (checks : List (GuardCheck (graph).layout payload))
    (outputEq : (graph).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph).layout) outputEq) ((graph).nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (value : L.Val payload)
    (stored : binding.get? before.application.current.native.config.store = some (.success value))
    (bounded : (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (request : before.application.SeedRequest owner ⟨before.application.attempt, event⟩)
    (entered : Nat) (stamp : before.application.current.native.activatedAt event = some entered)
    (positive : 0 < runtime.deadline event)
    (afterProcessing : ReservedEpoch.packetCapacity runtime ≤
      before.environmentRecall.length %
        ReservedEpoch.cycleWidth («graph» := graph) (ReservedEpoch.packetCapacity runtime))
    (path : closed ∈ ((app).runRounds (ReservedEpoch.family runtime leaks
      (ReservedEpoch.submissionBudget (Player := Player) cycles) tape)
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) count
          before).support) :
    PhaseService.BindingAccepted runtime leaks ⟨before.application.attempt, event⟩ owner closed ↔
      ReservedEpoch.openingFrontierReceipt runtime leaks tape before owner event := by
  classical
  let initial := (inputs).map (PhaseRuntimeState.initial plan)
  let horizon := ReservedEpoch.executionHorizon runtime
  let budget := ReservedEpoch.packetCapacity runtime
  let width := ReservedEpoch.cycleWidth («graph» := graph) budget
  let scheduler := ReservedEpoch.family runtime leaks budget tape
  let qualified := ∃ epoch, tape.nextProcessingEpoch (before.environmentRecall.length / width + 1) =
    some epoch ∧ epoch < cycles ∧ epoch - entered < runtime.deadline event
  have rawStart := (menu).toRawTrace initial horizon scheduler trace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  rcases ReservedEpoch.opening_frontier_sent_status runtime leaks bounds plan inputs horizon
    scheduler ⟨remaining, none, before⟩ trace owner event payload binding checks outputEq codeEq
      node
      request with unsent |
    ⟨message, candidate, oldValue, input, sender, address, call, status, _stored, _associated,
      _fixed⟩
  · have actual := phaseProposalUnflagged_stopped_unsent_opening_receipt_word setup mode runtime
      leaks bounds plan ordered values cycles tape remaining closedRemaining count owner before
        closed trace closedTrace kept retired event payload binding checks outputEq codeEq node
          value stored bounded request entered stamp unsent positive path
    have bit : ReservedEpoch.openingFrontierReceipt runtime leaks tape before owner event ↔
        ReservedEpoch.UnsentQualification runtime leaks budget cycles tape
          before.environmentRecall.length entered owner event := by
      unfold ReservedEpoch.openingFrontierReceipt
      constructor
      · rintro ⟨otherEntered, otherStamp, qualification⟩
        have equal : otherEntered = entered := Option.some.inj (otherStamp.symm.trans stamp)
        subst otherEntered
        simpa only [ite_eq_left unsent] using qualification
      · intro qualification
        exact ⟨entered, stamp, by simpa only [ite_eq_left unsent] using qualification⟩
    exact actual.trans bit.symm
  · have output : message ∈ (app).outputs (before.recall owner) := by
      rw [← (app).history_inputRecall initial horizon scheduler rawStart owner]
      exact List.mem_filter.mpr ⟨input, by simp only [sender, decide_true]⟩
    have sent : ¬ ∀ packet ∈ (app).outputs (before.recall owner),
        PhaseCount.event? packet.payload ≠ some ⟨before.application.attempt, event⟩ := by
      intro unsent
      exact unsent message output (by
        simp only [PhaseCount.event?, call, Payload.event?, address, Option.map_some])
    have shape : ReservedEpoch.openingFrontierReceipt runtime leaks tape before owner event ↔
        ∃ packet ∈ before.network.pending, ∃ otherCandidate otherValue,
          packet.sender = owner ∧
          packet.payload.packet.call = .opening event otherCandidate otherValue ∧
          packet.payload.attempt = before.application.attempt ∧ qualified := by
      unfold ReservedEpoch.openingFrontierReceipt
      constructor
      · rintro ⟨otherEntered, otherStamp, qualification⟩
        have equal : otherEntered = entered := Option.some.inj (otherStamp.symm.trans stamp)
        subst otherEntered
        simpa only [ite_eq_right sent] using qualification
      · intro qualification
        exact ⟨entered, stamp, by simpa only [ite_eq_right sent] using qualification⟩
    have messageRequest : before.application.SeedRequest message.sender
        ⟨message.payload.attempt, event⟩ := by simpa only [sender, address] using request
    rcases status with pending | rejected
    · have actual := phaseProposalUnflagged_stopped_pending_opening_receipt_word setup mode runtime
        leaks bounds plan ordered values cycles tape remaining closedRemaining count before closed
          trace closedTrace kept retired event owner payload binding checks outputEq codeEq node
            message pending candidate ⟨payload, oldValue⟩ call messageRequest entered stamp
              afterProcessing path
      have bit : ReservedEpoch.openingFrontierReceipt runtime leaks tape before owner event ↔
          qualified := by
        rw [shape]
        constructor
        · rintro ⟨_packet, _pending, _candidate, _value, _sender, _call, _address, qualification⟩
          exact qualification
        · intro qualification
          exact ⟨message, pending, candidate, ⟨payload, oldValue⟩, sender, call, address,
            qualification⟩
      simpa only [sender, address] using actual.trans bit.symm
    · have failed := stopped_rejected_opening_not_accepted setup mode runtime leaks bounds
        initial horizon scheduler ⟨remaining, none, before⟩ ⟨closedRemaining, none, closed⟩ trace
          closedTrace kept message input event candidate ⟨payload, oldValue⟩ call rejected
      have noBit : ¬ ReservedEpoch.openingFrontierReceipt runtime leaks tape before owner event :=
          by
        intro bit
        obtain ⟨other, pending, otherCandidate, otherValue, otherSender, otherCall, otherAddress,
          _qualification⟩ := shape.mp bit
        have otherInput := ((app).retained_envelopes_mem_inputs before
          ((app).history_provenance initial horizon scheduler rawStart)
          ((app).history_inputRecall initial horizon scheduler rawStart)).pending other pending
        have first := (PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)
        have second := (PhaseCount.permits_eq_true_iff _ _).mp (clean.2 other otherInput)
        have equal : message = other := PhaseCount.Permits.eq_of_same_event first second input
          otherInput (fun first firstInput second secondInput ids =>
            (app).input_identifier_injective_history initial horizon scheduler
              ⟨remaining, none, before⟩ rawStart first second firstInput secondInput ids)
          (sender.trans otherSender.symm) (by
            simp only [PhaseCount.event?, call, otherCall, Payload.event?, Option.map_some,
              address, otherAddress])
        subst other
        exact (app).pending_identifier_not_receipted initial horizon scheduler
          ⟨remaining, none, before⟩ rawStart message pending false rejected
      exact iff_of_false (by simpa only [sender, address] using failed) noBit

end Vegas
