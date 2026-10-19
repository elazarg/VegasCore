/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochUnsentOpening
import Vegas.Pending.ReservedEpochUnsentRequest
import Vegas.Game.ReservedEpochStoppedTapeWord
import Interaction.ReactivePolicyInvariant
import Vegas.Pending.PhaseOwnCount
import Vegas.Pending.PhaseSemanticProgress
import Vegas.Pending.PhaseProposalRetention

/-! # Truthful opening emissions and receipts at the original phase exit -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
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

/-- The actual old unsent callback fixes its finite qualification bit at
original attempt closure. The complete continuation extends the literal closed
history, and retirement rules out a later first accepting original receipt. -/
theorem phaseProposalUnflagged_stopped_opening_offer_receipt
    (ordered : (graph).RevealRelaxedOrdered)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (cycles : Nat) (tape : ReservedEpoch.Tape Player length)
    (remaining closedRemaining activeRemaining tail : Nat) (owner : Player)
    (before active closed : (app).Execution)
    (trace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.horizon («graph» := graph) cycles)
      (ReservedEpoch.family runtime leaks
        (ReservedEpoch.submissionBudget (Player := Player) cycles) tape)).Trace
          (some ⟨remaining, none, before⟩))
    (activeTrace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.horizon («graph» := graph) cycles)
      (ReservedEpoch.family runtime leaks
        (ReservedEpoch.submissionBudget (Player := Player) cycles) tape)).Trace
          (some ⟨activeRemaining, some owner, active⟩))
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
    (request : active.application.SeedRequest owner ⟨active.application.attempt, event⟩)
    (sameAttempt : active.application.attempt = before.application.attempt)
    (entered : Nat) (stamp : active.application.current.native.activatedAt event = some entered)
    (unsent : ∀ message ∈ (app).outputs (active.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨active.application.attempt, event⟩)
    (value : L.Val payload)
    (stored : binding.get? active.application.current.native.config.store = some (.success value))
    (bounded : (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (response : (app).Action)
    (supported : response ∈ (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan
      values owner (active.recall owner) (active.observe app owner)).support)
    (path : closed ∈ ((app).runRounds (ReservedEpoch.family runtime leaks
      (ReservedEpoch.submissionBudget (Player := Player) cycles) tape)
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) tail
          (active.respond app owner response)).support) :
    ∃ (material : WitnessedSubmission graph) (candidate : Handle graph),
      response.transmission = some material ∧
      material.call.packet = .opening event candidate ⟨payload, value⟩ ∧
      active.application.current.native.accepted binding.field = some candidate ∧
      PhaseProposal.archive (active.respond app owner response).network.inputs =
        PhaseProposal.archive active.network.inputs ∪
          {(⟨active.application.attempt, event⟩, (⟨payload, value⟩ : Raw L))} ∧
      let message : Message Player (CommitAttemptPacket graph) :=
        ⟨(owner, active.network.nextSerial owner),
          (app).packet ((app).submit active.application owner material) owner
            (active.network.known owner) material⟩
      message ∈ closed.network.inputs ∧
      ((message.id, true) ∈ closed.receipts ↔
        ∃ epoch, tape.nextProcessingEpoch (active.environmentRecall.length /
            ReservedEpoch.cycleWidth («graph» := graph)
              (ReservedEpoch.submissionBudget (Player := Player) cycles) + 1) = some epoch ∧
          epoch < cycles ∧ epoch - entered < runtime.deadline event) := by
  classical
  let initial := (inputs).map (PhaseRuntimeState.initial plan)
  let horizon := ReservedEpoch.horizon («graph» := graph) cycles
  let budget := ReservedEpoch.submissionBudget (Player := Player) cycles
  let scheduler := ReservedEpoch.family runtime leaks budget tape
  let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
  let after := active.respond app owner response
  obtain ⟨material, candidate, sent, call, accepted, archive, law⟩ :=
    phaseProposalUnflagged_unsent_opening_receipt setup mode runtime leaks bounds plan values
      cycles tape ordered inputs activeRemaining owner active activeTrace event payload binding
        checks outputEq codeEq node request entered stamp unsent value stored bounded response
          supported
  refine ⟨material, candidate, sent, call, accepted, archive, ?_⟩
  let message : Message Player (CommitAttemptPacket graph) :=
    ⟨(owner, active.network.nextSerial owner),
      (app).packet ((app).submit active.application owner material) owner
        (active.network.known owner) material⟩
  change message ∈ closed.network.inputs ∧ ((message.id, true) ∈ closed.receipts ↔ _)
  have rawActive := (menu).toRawTrace initial horizon scheduler activeTrace
  have rawClosed := (menu).toRawTrace initial horizon scheduler closedTrace
  have activeBudget := (app).raw_trace_horizon initial horizon scheduler rawActive
  have closedBudget := (app).raw_trace_horizon initial horizon scheduler rawClosed
  have elapsed := (app).runRounds_environmentRecall_length scheduler players tail after closed path
  have afterClock : after.environmentRecall.length = active.environmentRecall.length := rfl
  have remainingSum : tail + closedRemaining = activeRemaining := by
    change active.environmentRecall.length + activeRemaining = horizon at activeBudget
    change closed.environmentRecall.length + closedRemaining = horizon at closedBudget
    omega
  obtain ⟨final, finalTrace, future, extension⟩ :=
    ReservedEpoch.complete_rounds_extension runtime leaks (menu) initial horizon scheduler players
      (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values)
        closedRemaining closed closedTrace
  have whole : final ∈ ((app).runRounds scheduler players activeRemaining after).support := by
    rw [← remainingSum, (app).runRounds_add scheduler players tail closedRemaining,
      PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨closed, path, future⟩
  have responseEq : response = ⟨some material⟩ := by cases response; congr
  have emitted : message ∈ (app).outputs (after.recall owner) := by
    simp only [after, responseEq, ReactiveApplication.Execution.respond, ↓reduceIte,
      ReactiveApplication.outputs, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  let recallInvariant : (app).PolicyInvariant players
      (fun execution => after.recall owner <+: execution.recall owner) := {
    respond execution actor action prior _ :=
      prior.trans ((app).respond_recall_prefix execution actor owner action)
    environment execution next command prior moved := by
      rw [(app).environmentStep_recall execution next command moved]
      exact prior }
  have recalled := recallInvariant.runRounds scheduler tail after closed
    (List.prefix_refl _) path
  have closedOutput := (recalled.filterMap ReactiveApplication.PlayerEntry.emitted).subset emitted
  have inputRecall := (app).history_inputRecall initial horizon scheduler rawClosed
  change message ∈ (app).outputs (closed.recall owner) at closedOutput
  change closed.InputRecall app at inputRecall
  rw [← inputRecall owner] at closedOutput
  have closedInput : message ∈ closed.network.inputs := (List.mem_filter.mp closedOutput).1
  have finalInput := ReservedEpoch.input_mem_prefix runtime leaks (menu) initial horizon scheduler
    ⟨closedRemaining, none, closed⟩ ⟨0, none, final⟩ closedTrace finalTrace extension message
      closedInput
  have address : message.payload.attempt = before.application.attempt := sameAttempt
  have receipt := ReservedEpoch.retired_event_receipt_iff runtime leaks (menu) plan inputs
    horizon scheduler ⟨remaining, none, before⟩ ⟨closedRemaining, none, closed⟩ ⟨0, none, final⟩
      trace closedTrace finalTrace kept extension retired message finalInput address
  exact ⟨closedInput, receipt.symm.trans (law final whole)⟩


/-- The old UNSENT frontier is resolved using its actual first race, not
an assumed future callback. The due branch is permanently nonaccepting; the
offer branch retains the actual typed draw and exact finite bit at closure. -/
theorem phaseProposalUnflagged_stopped_unsent_opening
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
    (∃ cursor, before.environmentRecall.length ≤ cursor ∧
      cursor < closed.environmentRecall.length ∧
      (∀ view, ReservedEpoch.command runtime leaks
        (ReservedEpoch.submissionBudget (Player := Player) cycles) tape cursor view =
          .application (.expire event)) ∧
      runtime.deadline event ≤ cursor / ReservedEpoch.cycleWidth («graph» := graph)
        (ReservedEpoch.submissionBudget (Player := Player) cycles) - entered ∧
      (∀ earlier, before.environmentRecall.length ≤ earlier → earlier < cursor → ∀ view,
        (ReservedEpoch.command runtime leaks
          (ReservedEpoch.submissionBudget (Player := Player) cycles) tape earlier view).actor?
            app ≠ some owner) ∧
      (∀ earlier, before.environmentRecall.length ≤ earlier → earlier < cursor → ∀ view,
        ReservedEpoch.command runtime leaks
            (ReservedEpoch.submissionBudget (Player := Player) cycles) tape earlier view =
          .application (.expire event) →
          earlier / ReservedEpoch.cycleWidth («graph» := graph)
            (ReservedEpoch.submissionBudget (Player := Player) cycles) - entered <
              runtime.deadline event) ∧
      ¬ PhaseService.BindingAccepted runtime leaks ⟨before.application.attempt, event⟩ owner
        closed ∧
      ∃ used tail due expired,
        used + 1 + tail = count ∧
        due.environmentRecall.length = cursor ∧
        due ∈ ((app).runRounds (ReservedEpoch.family runtime leaks
          (ReservedEpoch.submissionBudget (Player := Player) cycles) tape)
          (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) used
            before).support ∧
        expired ∈ (due.environmentStep app (.application (.expire event))).support ∧
        (⟨before.application.attempt, event⟩ : CommitAttemptEvent graph).Resolved
          expired.application ∧
        closed ∈ ((app).runRounds (ReservedEpoch.family runtime leaks
          (ReservedEpoch.submissionBudget (Player := Player) cycles) tape)
          (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) tail
            expired).support) ∨
      ∃ (used tail activeRemaining : Nat) (offered active : (app).Execution)
        (response : (app).Action) (material : WitnessedSubmission graph)
        (candidate : Handle graph),
        used + 1 + tail = count ∧
        offered ∈ ((app).runRounds (ReservedEpoch.family runtime leaks
          (ReservedEpoch.submissionBudget (Player := Player) cycles) tape)
          (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) used
            before).support ∧
        ReservedEpoch.command runtime leaks
          (ReservedEpoch.submissionBudget (Player := Player) cycles) tape
          offered.environmentRecall.length (offered.observeEnvironment app) = .activate owner ∧
        active ∈ (offered.environmentStep app (.activate owner)).support ∧
        response ∈ (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
          owner (active.recall owner) (active.observe app owner)).support ∧
        response.transmission = some material ∧
        material.call.packet = .opening event candidate ⟨payload, value⟩ ∧
        active.application.current.native.accepted binding.field = some candidate ∧
        PhaseProposal.archive (active.respond app owner response).network.inputs =
          PhaseProposal.archive active.network.inputs ∪
            {(⟨active.application.attempt, event⟩, (⟨payload, value⟩ : Raw L))} ∧
        active.application.attempt = before.application.attempt ∧
        active.application.current.native.activatedAt event = some entered ∧
        active.recall owner = before.recall owner ∧
        (∀ earlier, before.environmentRecall.length ≤ earlier →
          earlier < before.environmentRecall.length + used → ∀ view,
          (ReservedEpoch.command runtime leaks
            (ReservedEpoch.submissionBudget (Player := Player) cycles) tape earlier view).actor?
              app ≠ some owner) ∧
        (∀ earlier, before.environmentRecall.length ≤ earlier →
          earlier < before.environmentRecall.length + used → ∀ view,
          ReservedEpoch.command runtime leaks
              (ReservedEpoch.submissionBudget (Player := Player) cycles) tape earlier view =
            .application (.expire event) →
            earlier / ReservedEpoch.cycleWidth («graph» := graph)
              (ReservedEpoch.submissionBudget (Player := Player) cycles) - entered <
                runtime.deadline event) ∧
        Nonempty (((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
          (ReservedEpoch.horizon («graph» := graph) cycles)
          (ReservedEpoch.family runtime leaks
            (ReservedEpoch.submissionBudget (Player := Player) cycles) tape)).Trace
              (some ⟨activeRemaining, some owner, active⟩)) ∧
        let message : Message Player (CommitAttemptPacket graph) :=
          ⟨(owner, active.network.nextSerial owner),
            (app).packet ((app).submit active.application owner material) owner
              (active.network.known owner) material⟩
        message ∈ closed.network.inputs ∧
        ((message.id, true) ∈ closed.receipts ↔
          ∃ epoch, tape.nextProcessingEpoch (active.environmentRecall.length /
              ReservedEpoch.cycleWidth («graph» := graph)
                (ReservedEpoch.submissionBudget (Player := Player) cycles) + 1) = some epoch ∧
            epoch < cycles ∧ epoch - entered < runtime.deadline event) := by
  let initial := (inputs).map (PhaseRuntimeState.initial plan)
  let horizon := ReservedEpoch.horizon («graph» := graph) cycles
  let budget := ReservedEpoch.submissionBudget (Player := Player) cycles
  let scheduler := ReservedEpoch.family runtime leaks budget tape
  let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
  have covered := phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have rawClosed := (menu).toRawTrace initial horizon scheduler closedTrace
  have startBudget := (app).raw_trace_horizon initial horizon scheduler raw
  have endBudget := (app).raw_trace_horizon initial horizon scheduler rawClosed
  have elapsed := (app).runRounds_environmentRecall_length scheduler players count before
    closed path
  have within : count ≤ remaining := by
    change before.environmentRecall.length + remaining = horizon at startBudget
    change closed.environmentRecall.length + closedRemaining = horizon at endBudget
    omega
  rcases ReservedEpoch.unsent_race_response_before_exit runtime leaks budget tape players plan
    ordered inputs horizon remaining count before closed raw within owner
      ⟨before.application.attempt, event⟩ request entered stamp unsent path positive retired with
    failed | ⟨used, tail, offered, active, response, lengths, initialPath, activation, moved,
      chosen, future, activeRequest, activeStamp, recalled, activeUnsent, quiet, expiryOpen⟩
  · exact Or.inl failed
  · have usedWithin : used + 1 ≤ remaining := by omega
    have remainingSplit : remaining - used + used = remaining := Nat.sub_add_cancel (by omega)
    obtain ⟨offeredTrace⟩ := (menu).trace_runRounds initial horizon scheduler players covered
      (remaining - used) used before offered (by simpa only [remainingSplit]
        using trace) initialPath
    have selected : (ReactiveApplication.Command.activate owner : (app).Command) ∈
        (scheduler offered.environmentRecall (offered.observeEnvironment app)).support :=
      (ReservedEpoch.family_support runtime leaks budget tape _ _ _).mpr activation.symm
    obtain ⟨activeTrace⟩ := (menu).trace_environment initial horizon scheduler
      (remaining - used - 1) offered active (.activate owner) (by
        simpa only [show remaining - used - 1 + 1 = remaining - used by omega]
          using offeredTrace) selected moved
    have sameAttempt : active.application.attempt = before.application.attempt :=
      activeRequest.1.symm
    have currentRequest : active.application.SeedRequest owner
        ⟨active.application.attempt, event⟩ := by
      simpa only [sameAttempt] using activeRequest
    have currentUnsent : ∀ message ∈ (app).outputs (active.recall owner),
        PhaseCount.event? message.payload ≠ some ⟨active.application.attempt, event⟩ := by
      simpa only [sameAttempt] using activeUnsent
    have applicationEq : active.application = offered.application := by
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨sample, _selected, rfl⟩ := PMF.support_map .. ▸ supported
      rfl
    have anchorOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
      scheduler (by
        intro state member
        obtain ⟨input, _member, rfl⟩ := PMF.support_map .. ▸ member
        exact PhaseRuntimeState.initial_ordered plan input) raw
    have sameOffered : before.application.attempt = offered.application.attempt :=
      sameAttempt.symm.trans (congrArg PhaseRuntimeState.attempt applicationEq)
    have immutable := (phase_runRounds_semantic_extension runtime leaks players scheduler used
      before offered anchorOrdered initialPath sameOffered).1
    have activeStored : binding.get? active.application.current.native.config.store =
        some (.success value) := by
      rw [applicationEq]
      exact binding.get?_preserved _ _ immutable _ stored
    obtain ⟨material, candidate, sent, call, accepted, archive, receipt⟩ :=
      phaseProposalUnflagged_stopped_opening_offer_receipt setup mode runtime leaks bounds plan
        ordered values cycles tape remaining closedRemaining (remaining - used - 1) tail owner
          before active closed trace activeTrace closedTrace kept retired event payload binding
            checks outputEq codeEq node currentRequest sameAttempt entered activeStamp currentUnsent
              value activeStored bounded response chosen future
    exact Or.inr ⟨used, tail, remaining - used - 1, offered, active, response, material, candidate,
      lengths, initialPath, activation, moved, chosen, sent, call, accepted, archive, sameAttempt,
        activeStamp, recalled, quiet, expiryOpen, ⟨activeTrace⟩, receipt⟩

end Vegas
