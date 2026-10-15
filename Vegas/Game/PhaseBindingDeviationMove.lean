/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingMenuShape
import Vegas.Game.PhaseRecoveryBindingChoice
import Vegas.Game.PhaseRecoverySlotComponent

/-! # The exact auxiliary move of a permitted raw binding response -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

local notation "app" => phaseApplication runtime leaks

/-- Any permitted nonsilent binding response realizes a genuine nonmissing
auxiliary source move at its actual complete source information. Its exact
typed result is read from the physical postresponse catalogue; typed failure
does not imply physical omission or permanent exclusion. -/
theorem phase_binding_deviation_move_of_history
    (wellFormed : setup.WellFormed) (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat) (who : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (material : WitnessedSubmission (serviceGraph setup mode))
    (member : (⟨some material⟩ : (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds
      who (execution.recall who) (execution.observe app who)) :
    ∃ (view : SourceProgram.ProtocolView who setup.program) (serial : Nat)
      (preparation : Option (Raw L)) (evidence : EvidenceRequest (serviceGraph setup mode))
      (choice : setup.commitRecoveryModel.Choice who
        (setup.commitRecoveryClearInformation wellFormed who (some view))),
      phaseSourceView? setup mode runtime leaks who event (execution.observe app who) = some view ∧
      setup.commitRecoveryModel.IsDecisionInfo who
        (setup.commitRecoveryClearInformation wellFormed who (some view)) ∧
      material = ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩ ∧
      serial < bounds.candidateCount ∧
      execution.application.current.native.candidates.lookup (who, .prepared serial) = .fresh ∧
      phaseRecoveryBindingData setup mode event who payload binding choice.1 =
        phaseBindingResponseOutcome setup mode runtime leaks execution who payload ⟨some material⟩ ∧
      phaseRecoveryBindingData setup mode event who payload binding choice.1 =
        ((execution.respond app who ⟨some material⟩).application.current.native.bindingResult
          (who, .prepared serial) payload, false) ∧
      (execution.respond app who ⟨some material⟩).application.current.excluded = ∅ := by
  classical
  obtain ⟨serial, preparation, evidence, materialEq, bounded, fresh⟩ :=
    PhaseCount.onePacket_binding_shape runtime leaks bounds plan
      (serviceGraph_revealRelaxedOrdered setup mode) (setup.initialLaw.map encodeInputs) horizon
        scheduler remaining who execution trace event payload binding request material member
  let control : (app).Control := ⟨remaining, some who, execution⟩
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  have initialEq : (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan) =
      setup.initialLaw.map (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) := by
    simp only [PMF.map_comp, Function.comp_def]
  have actual : ((app).protocol (setup.initialLaw.map fun draw =>
      PhaseRuntimeState.initial plan (encodeInputs draw)) horizon scheduler).Trace
        (some control) := initialEq ▸ raw
  obtain ⟨_source, _sourceTrace, _excluded, _generation, _actor, decoded⟩ :=
    phase_ready_binding_sourceView setup mode runtime leaks plan maximal horizon scheduler actual
      who event payload binding request.2.2.1 clear
  have played := phase_ready_binding_information setup mode runtime leaks plan maximal horizon
    scheduler actual who event payload binding request.2.2.1 clear wellFormed
  rw [decoded] at played
  let result := (execution.respond app who ⟨some material⟩).application.current.native.bindingResult
    (who, .prepared serial) payload
  obtain ⟨choice, data⟩ := exists_phaseRecoveryBindingChoice setup mode runtime leaks wellFormed
    execution who event payload binding _ decoded request.2.2.2.1 result
  refine ⟨_, serial, preparation, evidence, choice, decoded, played, materialEq, bounded, fresh,
    ?_, data, ?_⟩
  · rw [data]
    subst material
    simp only [result, phaseBindingResponseOutcome, PhaseCandidates.responseCandidateSlot,
      Payload.preparedCommitment?, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
      Option.getD_some]
  · exact clear

end Vegas
