/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhasePreparedBinding
import Vegas.Pending.PhaseOwnCommitments

/-! # Actual first binding responses in the phased one-packet menu -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- Every fresh own binding at an unsent current ready coordinate is permitted
by the actual count rule. Retired first packets remain in the tested recall. -/
theorem phaseBindingResponse_permitted
    (execution : (phaseApplication runtime leaks).Execution)
    (recalled : CountRecall runtime leaks execution)
    (fixed : PhaseOwnCommitmentsFixed runtime leaks execution)
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (execution.recall who),
      event? message.payload ≠ some ⟨execution.application.attempt, event⟩)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (fresh : execution.application.current.native.candidates.lookup (who, .prepared serial) =
      .fresh) :
    OnePacketResponse runtime leaks who (execution.recall who)
      (execution.observe (phaseApplication runtime leaks) who)
      (phaseBindingResponse runtime leaks who event payload result serial) := by
  let app := phaseApplication runtime leaks
  let material : WitnessedSubmission graph := ⟨⟨.commitment event (who, .prepared serial),
    match result with
    | .failure => none
    | .success value => some ⟨payload, value⟩⟩, .none⟩
  refine ⟨material, rfl, ?_⟩
  have allowed : allows execution.application.publicView material.call.packet = true := by
    rw [allows_publicView]
    obtain ⟨phase, member, inside⟩ := request.2.1
    have head := Option.mem_def.mp member
    simp only [PhaseRuntimeState.allows, head, material, Payload.event?]
    exact decide_eq_true inside
  have unexcluded : excludedCall execution.application.publicView material.call.packet = false := by
    simp only [excludedCall, material, Payload.event?, request.2.2.2.1, Option.any_some]
    exact decide_eq_false request.2.2.2.2
  have token := execution.application.current.native.publicView_tokenFor_of_ready
    material.call.packet event (by rfl) request.2.2.1
  have envelope : localEnvelope runtime leaks who (execution.recall who)
      (execution.observe app who) material =
      ⟨(who, execution.network.nextSerial who), ⟨execution.application.attempt,
        ⟨.commitment event (who, .prepared serial), none, some ⟨event⟩⟩⟩⟩ := by
    rw [localEnvelope_eq_of_recall runtime leaks execution recalled.1 recalled.2.1 who material]
    change Message.mk _ ((execution.application.submit who material).emit who
      (execution.network.known who) material) = _
    rw [emit_after_submit]
    simp only [maskPacket, allowed, unexcluded, Bool.false_eq_true, ↓reduceIte,
      token, material, EvidenceRequest.resolve]
  rw [envelope, permits_eq_true_iff]
  refine ⟨WitnessedPacket.tokenValid_commitment _ _ _, ?_, ?_, trivial⟩
  · change CountCallCorrect _ (⟨(who, execution.network.nextSerial who),
      ⟨.commitment event (who, .prepared serial), none, some ⟨event⟩⟩⟩ :
        Message Player (WitnessedPacket graph))
    refine ⟨?_, rfl, rfl, ⟨serial, rfl⟩, ?_⟩
    · simp only [bindingOwnedBy, outputEq, Message.sender, decide_true]
    · intro other earlier named call
      obtain ⟨prior, member, rfl⟩ := List.mem_map.mp earlier.1
      exact fixed who prior member named (.prepared serial) call fresh
  · intro other earlier
    exact unsent other earlier.1

section FiniteMenu

variable [Fintype Player] (bounds : MessageBounds graph)

/-- A genuine unsent current binding admits every typed result in the actual
finite one-packet menu, with a derived globally fresh handle and exact result. -/
theorem exists_phaseBindingResponse_onePacket_of_history
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount)
    (control : (phaseApplication runtime leaks).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control)) (who : Player) (active : control.actor = some who)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    ∃ serial, serial < horizon ∧ ∀ result : PublicationResult (L.Val payload),
      phaseBindingResponse runtime leaks who event payload result serial ∈
        onePacketActions runtime leaks bounds who (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who) ∧
      let next := control.execution.respond (phaseApplication runtime leaks) who
        (phaseBindingResponse runtime leaks who event payload result serial)
      next.application.current.native.bindingResult (who, .prepared serial) payload = result := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have raw := menu.toRawTrace initial horizon scheduler trace
  obtain ⟨serial, bounded, selected⟩ := PhaseCandidates.reactiveFreshSlot_lt_horizon runtime leaks
    plan inputs horizon scheduler control raw who active
  have fresh := reactiveFreshSlot_spec _ serial selected
  have fixed := phaseOwnCommitmentsFixed_history runtime leaks initial horizon scheduler raw
  have recalled := countRecall_history runtime leaks raw
  refine ⟨serial, bounded, fun result => ⟨?_, ?_⟩⟩
  · rw [mem_onePacketActions]
    refine ⟨phaseBindingResponse_available runtime leaks bounds who _ _ event payload values
      result serial (bounded.trans_le capacity), Or.inr ?_⟩
    exact phaseBindingResponse_permitted runtime leaks control.execution recalled fixed who event
      payload outputEq request unsent result serial fresh
  · exact phaseBindingResponse_result runtime leaks control.execution who event payload result
      serial fresh

end FiniteMenu
end Vegas.EventGraphRuntime.PhaseCount
