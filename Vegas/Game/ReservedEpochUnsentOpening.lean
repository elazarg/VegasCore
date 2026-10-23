/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalUnflaggedOpening
import Vegas.Pending.ReservedEpochReceiptTiming

/-! # Truthful emission and finite admission at an old unsent publication -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

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

/-- The next actual unflagged callback of an old unspent usable publication
emits its locked truthful value. Emission adds the proposal immediately,
including when the separate finite receipt test is false. Guard success and
first-ever response protection are not required for this old episode. -/
theorem phaseProposalUnflagged_unsent_opening_receipt
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (cycles : Nat) (tape : ReservedEpoch.Tape Player length)
    (ordered : (graph).RevealRelaxedOrdered) (inputs : PMF (graph).Inputs)
    (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.horizon («graph» := graph) cycles)
      (ReservedEpoch.family runtime leaks
        (ReservedEpoch.submissionBudget (Player := Player) cycles) tape)).Trace
        (some ⟨remaining, some owner, execution⟩))
    (event : (graph).EventId) (payload : L.Ty)
    (binding : FieldRef (graph).layout (.binding owner payload))
    (checks : List (GuardCheck (graph).layout payload))
    (outputEq : (graph).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph).layout) outputEq) ((graph).nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (entered : Nat) (stamp : execution.application.current.native.activatedAt event = some entered)
    (unsent : ∀ message ∈ (app).outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩)
    (value : L.Val payload)
    (stored : binding.get? execution.application.current.native.config.store =
      some (.success value))
    (bounded : (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (response : (app).Action)
    (supported : response ∈ (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan
      values owner (execution.recall owner) (execution.observe app owner)).support) :
    let after := execution.respond app owner response
    let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    ∃ (material : WitnessedSubmission graph) (candidate : Handle graph),
      response.transmission = some material ∧
      material.call.packet = .opening event candidate ⟨payload, value⟩ ∧
      execution.application.current.native.accepted binding.field = some candidate ∧
      PhaseProposal.archive after.network.inputs = PhaseProposal.archive execution.network.inputs ∪
        {(⟨execution.application.attempt, event⟩, (⟨payload, value⟩ : Raw L))} ∧
      let message : Message Player (app).Payload :=
        ⟨(owner, execution.network.nextSerial owner),
          (app).packet ((app).submit execution.application owner material) owner
            (execution.network.known owner) material⟩
      ∀ final ∈ ((app).runRounds (ReservedEpoch.family runtime leaks
          (ReservedEpoch.submissionBudget (Player := Player) cycles) tape)
          players remaining after).support,
        ((message.id, true) ∈ final.receipts ↔
          ∃ epoch, tape.nextProcessingEpoch (execution.environmentRecall.length /
              ReservedEpoch.cycleWidth («graph» := graph)
                (ReservedEpoch.submissionBudget (Player := Player) cycles) + 1) = some epoch ∧
            epoch < cycles ∧ epoch - entered < runtime.deadline event) := by
  classical
  intro after players
  let horizon := ReservedEpoch.horizon («graph» := graph) cycles
  let scheduler := ReservedEpoch.family runtime leaks
    (ReservedEpoch.submissionBudget (Player := Player) cycles) tape
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  obtain ⟨candidate, material, accepted, sent, call⟩ :=
    phaseProposalUnflaggedOpening_supported_truthful setup mode runtime leaks bounds plan values
      inputs horizon scheduler remaining owner execution trace event payload binding checks
        outputEq codeEq node request unsent value stored bounded response supported
  have responseEq : response = ⟨some material⟩ := by cases response; congr
  subst response
  have offered := phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values
    owner (execution.recall owner) (execution.observe app owner) ⟨some material⟩ supported
  let message : Message Player (app).Payload :=
    ⟨(owner, execution.network.nextSerial owner),
      (app).packet ((app).submit execution.application owner material) owner
        (execution.network.known owner) material⟩
  have proposed : PhaseProposal.packetProposal? message.payload =
      some (⟨execution.application.attempt, event⟩, (⟨payload, value⟩ : Raw L)) := by
    have named : message.payload.packet.call = .opening event candidate ⟨payload, value⟩ := by
      change (PhaseRuntimeState.emit (execution.application.submit owner material) owner
        (execution.network.known owner) material).packet.call = _
      rw [phase_emit_call, call]
    unfold PhaseProposal.packetProposal?
    rw [named]
    rfl
  have archive : PhaseProposal.archive after.network.inputs =
      PhaseProposal.archive execution.network.inputs ∪
        {(⟨execution.application.attempt, event⟩, (⟨payload, value⟩ : Raw L))} := by
    change PhaseProposal.archive (execution.network.inputs ++ [message]) = _
    rw [PhaseProposal.archive_append]
    simp only [PhaseProposal.archive, List.filterMap_cons, proposed, List.filterMap_nil,
      List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
  refine ⟨material, candidate, rfl, call, accepted, archive, ?_⟩
  intro _message final reached
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have ownClean : PhaseCount.OwnCountClean runtime leaks owner execution :=
    ⟨clean.1, fun packet member _ => clean.2 packet member⟩
  have permitted : PhaseCount.OnePacketResponse runtime leaks owner (execution.recall owner)
      (execution.observe app owner) ⟨some material⟩ := by
    rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp offered).2 with
      impossible | counted
    · cases impossible
    · exact counted
  have futureCovered : ∀ past view action, action ∈ (players owner past view).support →
      action.transmission = none ∨
        PhaseCount.OnePacketResponse runtime leaks owner past view action := by
    intro past view action chosen
    exact ((PhaseCount.mem_onePacketActions runtime leaks bounds owner past view action).mp
      (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values owner
        past view action chosen)).2
  exact ReservedEpoch.current_response_receipt_iff runtime leaks cycles tape players plan ordered
    inputs remaining owner execution raw event entered request stamp material
      (.opening owner payload binding checks outputEq codeEq node candidate ⟨payload, value⟩
        call accepted) ownClean permitted futureCovered final reached

end Vegas
