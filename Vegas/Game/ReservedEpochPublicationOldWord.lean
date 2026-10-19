/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochPublicationEpisode
import Vegas.Pending.PhaseReadyPacketStatus
import Vegas.Pending.PhaseBindingOpeningRead

/-! # Actual old ready opening episodes and their finite stopped word -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The full old sent status is literal: an initially ready publication is
UNSENT, actually pending with its locked truthful opening, or permanently
FALSE-receipted. TRUE receipt and semantic guard success are distinct. -/
theorem opening_frontier_sent_status (bounds : MessageBounds graph)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (current : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (request : current.execution.application.SeedRequest owner
      ⟨current.execution.application.attempt, event⟩) :
    (∀ message ∈ (app).outputs (current.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨current.execution.application.attempt, event⟩) ∨
    ∃ (message : Message Player (CommitAttemptPacket graph)) (candidate : Handle graph)
      (value : L.Val payload), message ∈ current.execution.network.inputs ∧
      message.sender = owner ∧ message.payload.attempt = current.execution.application.attempt ∧
      message.payload.packet.call = .opening event candidate ⟨payload, value⟩ ∧
      (message ∈ current.execution.network.pending ∨
        (message.id, false) ∈ current.execution.receipts) ∧
      binding.get? current.execution.application.current.native.config.store =
        some (.success value) ∧
      current.execution.application.current.native.accepted binding.field = some candidate ∧
      current.execution.application.current.native.candidates.lookup candidate =
        .openable ⟨payload, value⟩ := by
  classical
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  by_cases unsent : ∀ message ∈ (app).outputs (current.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨current.execution.application.attempt, event⟩
  · exact Or.inl unsent
  · obtain ⟨message, input, sender, address, named, status⟩ := phase_seedRequest_sent_status runtime
      leaks menu plan inputs horizon scheduler current trace owner _ request unsent
    have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
      initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
    have correct := ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message input)).2.1
    have opening : ∃ candidate raw,
        message.payload.packet.call = .opening event candidate raw := by
      cases call : message.payload.packet.call with
      | malformed raw => rw [call] at named; cases named
      | commitment other candidate =>
          have equal : other = event := Option.some.inj (by simpa only [call, Payload.event?]
            using named)
          subst other
          simp only [CountCallCorrect, PhaseCount.nativeMessage, call, bindingOwnedBy, outputEq,
            Bool.false_eq_true, false_and] at correct
      | opening other candidate raw =>
          have equal : other = event := Option.some.inj (by simpa only [call, Payload.event?]
            using named)
          subst other
          exact ⟨candidate, raw, rfl⟩
    obtain ⟨candidate, raw, call⟩ := opening
    have actualRequest : current.execution.application.SeedRequest message.sender
        ⟨message.payload.attempt, event⟩ := by simpa only [sender, address] using request
    obtain ⟨value, typed, stored, accepted, fixed⟩ :=
      PhaseBindingRepair.opening_binding_success runtime leaks bounds plan inputs horizon scheduler
        trace message input event candidate raw call actualRequest owner payload binding checks
          outputEq codeEq node
    subst raw
    exact Or.inr ⟨message, candidate, value, input, sender, address, call, status, stored, accepted,
      fixed⟩

end Vegas.EventGraphRuntime.ReservedEpoch

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

/-- The whole original old-UNSENT receipt bit is the literal first-offer
qualification. Late emissions remain in the existing race witness even when
this finite processing predicate is FALSE. -/
theorem phaseProposalUnflagged_stopped_unsent_opening_receipt_word
    (ordered : (graph).RevealRelaxedOrdered)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (cycles : Nat) (tape : ReservedEpoch.Tape Player length)
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
    (PhaseService.BindingAccepted runtime leaks ⟨before.application.attempt, event⟩ owner closed ↔
      ReservedEpoch.UnsentQualification runtime leaks
        (ReservedEpoch.submissionBudget (Player := Player) cycles) cycles tape
          before.environmentRecall.length entered owner event) := by
  let initial := (inputs).map (PhaseRuntimeState.initial plan)
  let horizon := ReservedEpoch.horizon («graph» := graph) cycles
  let budget := ReservedEpoch.submissionBudget (Player := Player) cycles
  let width := ReservedEpoch.cycleWidth («graph» := graph) budget
  let scheduler := ReservedEpoch.family runtime leaks budget tape
  rcases phaseProposalUnflagged_stopped_unsent_opening setup mode runtime leaks bounds plan ordered
    values cycles tape remaining closedRemaining count owner before closed trace closedTrace kept
      retired event payload binding checks outputEq codeEq node value stored bounded request entered
        stamp unsent positive path with
    ⟨cursor, lower, _upper, expired, due, quiet, _open, failed, _witness⟩ |
    ⟨used, tail, activeRemaining, offered, active, response, material, candidate, _lengths,
      initialPath, activation, moved, _chosen, _sent, call, _accepted, _archive, sameAttempt,
      _activeStamp, _recalled, quiet, expiryOpen, _activeTrace, input, receipt⟩
  · exact iff_of_false failed (ReservedEpoch.not_unsentQualification_of_due runtime leaks budget
      cycles tape before.environmentRecall.length entered cursor owner event
        (before.observeEnvironment app) lower expired due quiet)
  · let message : Message Player (CommitAttemptPacket graph) :=
      ⟨(owner, active.network.nextSerial owner),
        (app).packet ((app).submit active.application owner material) owner
          (active.network.known owner) material⟩
    have named : message.payload.packet.call = .opening event candidate ⟨payload, value⟩ := by
      change (PhaseRuntimeState.emit (active.application.submit owner material) owner
        (active.network.known owner) material).packet.call = _
      rw [phase_emit_call, call]
    have address : message.payload.attempt = before.application.attempt := sameAttempt
    have accepted := phase_counted_packet_receipt_iff runtime leaks bounds initial horizon scheduler
      ⟨closedRemaining, none, closed⟩ closedTrace message input owner
        ⟨before.application.attempt, event⟩ rfl address (by rw [named]; rfl)
    have counted := (app).runRounds_environmentRecall_length scheduler
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) used before
        offered initialPath
    have actor : (ReservedEpoch.command runtime leaks budget tape offered.environmentRecall.length
        (offered.observeEnvironment app)).actor? app = some owner := by rw [activation]; rfl
    have offeredAll : ∀ view, (ReservedEpoch.command runtime leaks budget tape
        offered.environmentRecall.length view).actor? app = some owner := fun view =>
      (ReservedEpoch.command_actor_view_independent runtime leaks budget tape
        offered.environmentRecall.length view (offered.observeEnvironment app)).trans actor
    have pureBit := ReservedEpoch.unsentQualification_iff_first_offer runtime leaks budget cycles
      tape before.environmentRecall.length entered offered.environmentRecall.length owner event
        (offered.observeEnvironment app) (by omega) offeredAll
          (by intro earlier lower upper view; exact quiet earlier lower (by omega) view)
          (by
            intro earlier lower upper view selected
            exact expiryOpen earlier lower (by omega) view selected)
    have activeLength := congrArg List.length ((app).environmentStep_environmentRecall offered
      active (.activate owner) moved)
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at activeLength
    have window := ReservedEpoch.command_activation_window runtime leaks budget tape
      offered.environmentRecall.length (offered.observeEnvironment app) owner actor
    change budget ≤ offered.environmentRecall.length % width ∧
      offered.environmentRecall.length % width < budget + Fintype.card Player at window
    have notLast : offered.environmentRecall.length % width ≠
        budget + Fintype.card Player + (graph).order.eventCount + 1 := by omega
    have cycle := ReservedEpoch.cycle_succ («graph» := graph) budget
      offered.environmentRecall.length
    change (offered.environmentRecall.length + 1) / width =
      offered.environmentRecall.length / width +
        if offered.environmentRecall.length % width =
          budget + Fintype.card Player + (graph).order.eventCount + 1 then 1 else 0 at cycle
    simp only [notLast, ↓reduceIte, Nat.add_zero] at cycle
    have sameCycle : active.environmentRecall.length / width =
        offered.environmentRecall.length / width := by rw [activeLength]; exact cycle
    change ((message.id, true) ∈ closed.receipts ↔
      ∃ epoch, tape.nextProcessingEpoch (active.environmentRecall.length / width + 1) =
        some epoch ∧ epoch < cycles ∧ epoch - entered < runtime.deadline event) at receipt
    rw [sameCycle] at receipt
    exact accepted.trans (receipt.trans pureBit.symm)

/-- An old pending opening has exactly its finite next-processing receipt
bit at the original stopped exit. Counted native provenance supplies factual
candidate association; no semantic guard acceptance is assumed. -/
theorem phaseProposalUnflagged_stopped_pending_opening_receipt_word
    (ordered : (graph).RevealRelaxedOrdered)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (cycles : Nat) (tape : ReservedEpoch.Tape Player length)
    (remaining closedRemaining count : Nat) (before closed : (app).Execution)
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
    (event : (graph).EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef (graph).layout (.binding owner payload))
    (checks : List (GuardCheck (graph).layout payload))
    (outputEq : (graph).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph).layout) outputEq) ((graph).nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (message : Message Player (CommitAttemptPacket graph))
    (pending : message ∈ before.network.pending) (candidate : Handle graph) (raw : Raw L)
    (call : message.payload.packet.call = .opening event candidate raw)
    (request : before.application.SeedRequest message.sender ⟨message.payload.attempt, event⟩)
    (entered : Nat) (stamp : before.application.current.native.activatedAt event = some entered)
    (afterProcessing : ReservedEpoch.submissionBudget (Player := Player) cycles ≤
      before.environmentRecall.length % ReservedEpoch.cycleWidth («graph» := graph)
        (ReservedEpoch.submissionBudget (Player := Player) cycles))
    (path : closed ∈ ((app).runRounds (ReservedEpoch.family runtime leaks
      (ReservedEpoch.submissionBudget (Player := Player) cycles) tape)
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) count
          before).support) :
    PhaseService.BindingAccepted runtime leaks ⟨message.payload.attempt, event⟩ message.sender
        closed ↔
      ∃ epoch, tape.nextProcessingEpoch (before.environmentRecall.length /
          ReservedEpoch.cycleWidth («graph» := graph)
            (ReservedEpoch.submissionBudget (Player := Player) cycles) + 1) = some epoch ∧
        epoch < cycles ∧ epoch - entered < runtime.deadline event := by
  let initial := (inputs).map (PhaseRuntimeState.initial plan)
  let horizon := ReservedEpoch.horizon («graph» := graph) cycles
  let budget := ReservedEpoch.submissionBudget (Player := Player) cycles
  let width := ReservedEpoch.cycleWidth («graph» := graph) budget
  let scheduler := ReservedEpoch.family runtime leaks budget tape
  let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
  have rawStart := (menu).toRawTrace initial horizon scheduler trace
  have input := ((app).retained_envelopes_mem_inputs before
    ((app).history_provenance initial horizon scheduler rawStart)
    ((app).history_inputRecall initial horizon scheduler rawStart)).pending message pending
  obtain ⟨_value, _typed, _stored, associated, _catalogue⟩ :=
    PhaseBindingRepair.opening_binding_success runtime leaks bounds plan inputs horizon scheduler
      trace message input event candidate raw call request owner payload binding checks outputEq
        codeEq node
  have certificate : ReservedEpoch.ReadyCall before.application message.payload.packet.call event :=
    .opening owner payload binding checks outputEq codeEq node candidate raw call associated
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have ownClean : PhaseCount.OwnCountClean runtime leaks message.sender before :=
    ⟨clean.1, fun packet member _ => clean.2 packet member⟩
  have covered : ∀ past view action, action ∈ (players message.sender past view).support →
      action.transmission = none ∨
        PhaseCount.OnePacketResponse runtime leaks message.sender past view action := by
    intro past view action selected
    exact ((PhaseCount.mem_onePacketActions runtime leaks bounds message.sender past view action).mp
      (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values
        message.sender past view action selected)).2
  have cursor : before.environmentRecall.length = before.environmentRecall.length / width * width +
      before.environmentRecall.length % width := by
    simpa only [Nat.mul_comm] using
      (Nat.div_add_mod before.environmentRecall.length width).symm
  have clock := ReservedEpoch.clock_history runtime leaks budget tape plan inputs horizon
    ⟨remaining, none, before⟩ rawStart
  have receipt := ReservedEpoch.stopped_pending_receipt_iff_epoch runtime leaks cycles tape players
    (menu) plan ordered inputs remaining closedRemaining count (before.environmentRecall.length /
      width) (before.environmentRecall.length % width) before closed trace closedTrace kept retired
        path (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values)
          cursor afterProcessing clock message pending event certificate request entered stamp
            ownClean covered
  have endInput := ReservedEpoch.input_mem_prefix runtime leaks (menu) initial horizon scheduler
    ⟨remaining, none, before⟩ ⟨closedRemaining, none, closed⟩ trace closedTrace kept message input
  exact (phase_counted_packet_receipt_iff runtime leaks bounds initial horizon scheduler
    ⟨closedRemaining, none, closed⟩ closedTrace message endInput message.sender
      ⟨message.payload.attempt, event⟩ rfl rfl (by rw [call]; rfl)).trans receipt

/-- An old opening with its literal FALSE receipt remains FALSE at the
original exit. Counted physical identity excludes a second envelope for it. -/
theorem stopped_rejected_opening_not_accepted
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (start ending : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some start))
    (closed : ((menu).protocol initial horizon scheduler).Trace (some ending))
    (kept : TracePrefix trace closed)
    (message : Message Player (CommitAttemptPacket graph))
    (input : message ∈ start.execution.network.inputs) (event : (graph).EventId)
    (candidate : Handle graph) (raw : Raw L)
    (call : message.payload.packet.call = .opening event candidate raw)
    (rejected : (message.id, false) ∈ start.execution.receipts) :
    ¬ PhaseService.BindingAccepted runtime leaks ⟨message.payload.attempt, event⟩ message.sender
      ending.execution := by
  have endInput := ReservedEpoch.input_mem_prefix runtime leaks (menu) initial horizon scheduler
    start ending trace closed kept message input
  have retained := ((app).reaches_receipts_prefix initial horizon scheduler
    ((menu).reaches_raw initial horizon scheduler kept.reachesWithin) start ending rfl rfl).subset
      rejected
  exact phase_counted_rejected_packet runtime leaks bounds initial horizon scheduler ending closed
    message endInput message.sender ⟨message.payload.attempt, event⟩ rfl rfl (by rw [call]; rfl)
      retained

end Vegas
