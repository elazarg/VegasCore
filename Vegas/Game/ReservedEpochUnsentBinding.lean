/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochUnsentRequest
import Vegas.Game.PhaseProposalUnflaggedBinding

/-! # The actual unflagged SEND at an old unsent binding episode -/

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

/-- An old unsent coordinate, including one with a remembered WAIT, SENDs an
ordinary typed value at its next actual eligible unflagged callback. Its
accepting bit is exactly the first next reserved epoch's original-deadline
test. No first-ever-response premise or semantic guard-success premise is used. -/
theorem phaseProposalUnflagged_unsent_binding_receipt
    (complete : leaks = MessageNetwork.completePendingObservation)
    (coveredValues : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (ordered : (graph).RevealRelaxedOrdered)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (cycles : Nat) (tape : ReservedEpoch.Tape Player length)
    (capacity : ReservedEpoch.horizon («graph» := graph) cycles ≤ bounds.candidateCount)
    (remaining : Nat) (owner : Player) (execution : (app).Execution)
    (trace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.horizon («graph» := graph) cycles)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.submissionBudget
        (Player := Player) cycles) tape)).Trace (some ⟨remaining, some owner, execution⟩))
    (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (entered : Nat) (stamp : execution.application.current.native.activatedAt event = some entered)
    (unsent : ∀ message ∈ (app).outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩)
    (response : (app).Action)
    (supported : response ∈ (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan
      values owner (execution.recall owner) (execution.observe app owner)).support) :
    let after := execution.respond app owner response
    let players := phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values
    ∃ (material : WitnessedSubmission graph) (value : L.Val payload) (serial : Nat),
      response.transmission = some material ∧
      PhaseProposal.bindingPreparation material = some (⟨payload, value⟩ : Raw L) ∧
      material.call.packet = .commitment event (owner, .prepared serial) ∧
      let message : Message Player (CommitAttemptPacket graph) :=
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
  intro after players
  let horizon := ReservedEpoch.horizon («graph» := graph) cycles
  let budget := ReservedEpoch.submissionBudget (Player := Player) cycles
  let scheduler := ReservedEpoch.family runtime leaks budget tape
  let initial := (inputs).map (PhaseRuntimeState.initial plan)
  obtain ⟨material, value, sent, prepared⟩ :=
    phaseProposalUnflaggedBinding_supported_usable setup mode runtime leaks bounds plan complete
      coveredValues maximal values fullValues horizon scheduler capacity remaining owner execution
        (by
          have nativeTrace := trace
          change ((menu).protocol
            ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
            horizon scheduler).Trace (some ⟨remaining, some owner, execution⟩) at nativeTrace
          rw [PMF.map_comp] at nativeTrace
          exact nativeTrace)
        event payload binding request unsent
          response supported
  have responseEq : response = ⟨some material⟩ := by cases response; congr
  subst response
  have offered := phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values
    owner (execution.recall owner) (execution.observe app owner) ⟨some material⟩ supported
  obtain ⟨serial, _preparation, _evidence, declared, _bounded, _fresh⟩ :=
    PhaseCount.onePacket_binding_shape runtime leaks bounds plan ordered inputs horizon scheduler
      remaining owner execution trace event payload binding request material offered
  have call : material.call.packet = .commitment event (owner, .prepared serial) :=
    congrArg (fun chosen : WitnessedSubmission graph => chosen.call.packet) declared
  refine ⟨material, value, serial, rfl, prepared, call, ?_⟩
  intro message final reached
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  have ownClean : PhaseCount.OwnCountClean runtime leaks owner execution :=
    ⟨clean.1, fun packet member _ => clean.2 packet member⟩
  have allowed := ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp offered).2
  have permitted : PhaseCount.OnePacketResponse runtime leaks owner (execution.recall owner)
      (execution.observe app owner) ⟨some material⟩ := by
    rcases allowed with impossible | counted
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
    inputs remaining owner execution raw event entered request stamp material (.binding _ call)
      ownClean permitted futureCovered final reached

end Vegas
