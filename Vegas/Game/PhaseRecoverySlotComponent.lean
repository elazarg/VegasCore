/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryBindingComponent
import Vegas.Pending.PhaseBindingSlotPolicy

/-! # Recovery binding choices with independent value-preserving fresh slots -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

/-- Silence is a physical omission. A transmitted unusable candidate retains
its failed typed result with the omission flag false. -/
def phaseBindingResponseOutcome (execution : (phaseApplication runtime leaks).Execution)
    (who : Player) (payload : L.Ty) (response : (phaseApplication runtime leaks).Action) :
    PublicationResult (L.Val payload) × Bool :=
  if response.transmission.isNone then (.failure, true) else
    let serial := (PhaseCandidates.responseCandidateSlot runtime leaks response).getD 0
    let next := execution.respond (phaseApplication runtime leaks) who response
    (next.application.current.native.bindingResult (who, .prepared serial) payload, false)

/-- The source choice is sampled without conditioning. Only its nonmissing
branch draws a fresh slot from the existing independent slot policy. -/
def phaseRecoverySlotPolicy (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload) :
    (phaseApplication runtime leaks).Policy := fun past view =>
  (assessment.strategy who (setup.commitRecoveryInformation wellFormed who
      (phaseSourceView? setup mode runtime leaks who event view))).bind fun choice =>
    let data := phaseRecoveryBindingData setup mode event who payload outputEq choice.1
    if data.2 then PMF.pure ⟨none⟩ else
      PhaseCount.phaseBindingSlotPolicy runtime leaks bounds who event payload
        (fun _ _ => PMF.pure data.1) past view

/-- Both the omission branch and every slot-tier response belong to the
actual authenticated finite menu at every input. -/
theorem phaseRecoverySlotPolicy_covered (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed
      assessment who event payload outputEq past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  rw [phaseRecoverySlotPolicy, PMF.mem_support_bind_iff] at supported
  obtain ⟨choice, _drawn, supported⟩ := supported
  dsimp only at supported
  split at supported
  · cases (PMF.mem_support_pure_iff _ _).mp supported
    exact PhaseCount.silence_onePacket runtime leaks bounds who past view
  · exact PhaseCount.phaseBindingSlotPolicy_covered runtime leaks bounds who event payload
      _ past view response supported

private theorem bindingSlotPolicy_outcome_law
    (execution : (phaseApplication runtime leaks).Execution) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (results : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF (PublicationResult (L.Val payload)))
    (nonempty : (PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
      (execution.recall who) (execution.observe (phaseApplication runtime leaks) who)).Nonempty) :
    (PhaseCount.phaseBindingSlotPolicy runtime leaks bounds who event payload results
        (execution.recall who) (execution.observe (phaseApplication runtime leaks) who)).map
      (phaseBindingResponseOutcome setup mode runtime leaks execution who payload) =
      (results (execution.recall who)
        (execution.observe (phaseApplication runtime leaks) who)).map (fun result =>
          (result, false)) := by
  classical
  have transmits (response : (phaseApplication runtime leaks).Action)
      (supported : response ∈ (PhaseCount.phaseBindingSlotPolicy runtime leaks bounds who event
        payload results (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who)).support) :
      response.transmission.isNone = false := by
    rw [PhaseCount.phaseBindingSlotPolicy, dite_eq_left nonempty,
      PMF.mem_support_bind_iff] at supported
    obtain ⟨serial, _selected, drawn⟩ := supported
    obtain ⟨result, _drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp drawn
    rfl
  calc
    _ = ((PhaseCount.phaseBindingSlotPolicy runtime leaks bounds who event payload results
        (execution.recall who) (execution.observe (phaseApplication runtime leaks) who)).map
      (fun response =>
        let serial := (PhaseCandidates.responseCandidateSlot runtime leaks response).getD 0
        let next := execution.respond (phaseApplication runtime leaks) who response
        next.application.current.native.bindingResult (who, .prepared serial) payload)).map
          (fun result => (result, false)) := by
      rw [PMF.map_comp]
      apply map_congr_on_support
      intro response supported
      simp only [phaseBindingResponseOutcome, transmits response supported, Bool.false_eq_true,
        ↓reduceIte, Function.comp_def]
    _ = _ := congrArg (fun law => law.map (fun result => (result, false)))
      (PhaseCount.phaseBindingSlotPolicy_result_law runtime leaks bounds execution who event
        payload results nonempty)

private theorem bindingSlotPolicy_move_outcome_law
    (execution : (phaseApplication runtime leaks).Execution) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (move : Option (CommitRecoveryMove Player L))
    (nonempty : (PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
      (execution.recall who) (execution.observe (phaseApplication runtime leaks) who)).Nonempty) :
    let data := phaseRecoveryBindingData setup mode event who payload outputEq move
    (if data.2 then PMF.pure (⟨none⟩ : (phaseApplication runtime leaks).Action) else
      PhaseCount.phaseBindingSlotPolicy runtime leaks bounds who event payload
        (fun _ _ => PMF.pure data.1) (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who)).map
      (phaseBindingResponseOutcome setup mode runtime leaks execution who payload) =
        PMF.pure data := by
  dsimp only
  cases missing : move.elim false (·.missing) with
  | true =>
      simp only [phaseRecoveryBindingData, missing, ↓reduceIte, PMF.pure_map]
      rfl
  | false =>
      have law := bindingSlotPolicy_outcome_law setup mode runtime leaks bounds execution
        who event payload (fun _ _ => PMF.pure
          (phaseRecoveryBindingData setup mode event who payload outputEq move).1) nonempty
      simpa only [phaseRecoveryBindingData, missing, Bool.false_eq_true, ↓reduceIte,
        PMF.pure_map] using law

/-- At an input with eligible slots, the declared typed result and omission
flag are jointly preserved in the actual post-response catalogue and traffic. -/
theorem phaseRecoverySlotPolicy_result_law (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (execution : (phaseApplication runtime leaks).Execution) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (nonempty : (PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
      (execution.recall who) (execution.observe (phaseApplication runtime leaks) who)).Nonempty) :
    (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment who event
      payload outputEq (execution.recall who)
        (execution.observe (phaseApplication runtime leaks) who)).map
      (phaseBindingResponseOutcome setup mode runtime leaks execution who payload) =
      (assessment.strategy who (setup.commitRecoveryInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (execution.observe (phaseApplication runtime leaks) who)))).map
        (fun choice => phaseRecoveryBindingData setup mode event who payload outputEq
          choice.1) := by
  let source := assessment.strategy who (setup.commitRecoveryInformation wellFormed who
    (phaseSourceView? setup mode runtime leaks who event
      (execution.observe (phaseApplication runtime leaks) who)))
  let data := fun choice : setup.commitRecoveryModel.Choice who
      (setup.commitRecoveryInformation wellFormed who (phaseSourceView? setup mode runtime leaks
        who event (execution.observe (phaseApplication runtime leaks) who))) =>
    phaseRecoveryBindingData setup mode event who payload outputEq choice.1
  rw [phaseRecoverySlotPolicy, PMF.map_bind]
  calc
    _ = source.bind (fun choice => PMF.pure (data choice)) := by
      apply bind_congr_on_support
      intro choice _supported
      exact bindingSlotPolicy_move_outcome_law setup mode runtime leaks bounds execution who
        event payload outputEq choice.1 nonempty
    _ = source.map data := PMF.bind_pure_comp _ _

/-- The omission law is preserved exactly, including its distinction from
transmitted failed typed results. -/
theorem phaseRecoverySlotPolicy_omission_law (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (execution : (phaseApplication runtime leaks).Execution) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (nonempty : (PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
      (execution.recall who) (execution.observe (phaseApplication runtime leaks) who)).Nonempty) :
    (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment who event
      payload outputEq (execution.recall who)
        (execution.observe (phaseApplication runtime leaks) who)).map
      (fun response => response.transmission.isNone) =
      (assessment.strategy who (setup.commitRecoveryInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (execution.observe (phaseApplication runtime leaks) who)))).map
        (fun choice => (phaseRecoveryBindingData setup mode event who payload outputEq
          choice.1).2) := by
  have law := congrArg (fun law : PMF (PublicationResult (L.Val payload) × Bool) =>
    law.map Prod.snd) (phaseRecoverySlotPolicy_result_law setup mode runtime leaks bounds
      wellFormed assessment execution who event payload outputEq nonempty)
  rw [PMF.map_comp, PMF.map_comp] at law
  have physical : (fun response => (phaseBindingResponseOutcome setup mode runtime leaks
      execution who payload response).2) = (fun response => response.transmission.isNone) := by
    funext response
    cases flag : response.transmission.isNone <;>
      simp only [phaseBindingResponseOutcome, flag, Bool.false_eq_true, ↓reduceIte]
  simpa only [Function.comp_def, physical] using law

/-- Every nonmissing source choice is represented at every eligible slot with
at least its original mass divided by the eligible-slot cardinality. -/
theorem phaseRecoverySlotPolicy_mass (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (choice : setup.commitRecoveryModel.Choice who
      (setup.commitRecoveryInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event view)))
    (serial : Nat)
    (eligible : serial ∈ PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
      past view)
    (notMissing : (phaseRecoveryBindingData setup mode event who payload outputEq choice.1).2 =
      false) :
    ((PhaseCount.phaseBindingSlots runtime leaks bounds who event payload past view).card :
        ENNReal)⁻¹ * (assessment.strategy who (setup.commitRecoveryInformation wellFormed who
          (phaseSourceView? setup mode runtime leaks who event view))) choice ≤
      phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment who event
        payload outputEq past view (phaseBindingResponse runtime leaks who event payload
          (phaseRecoveryBindingData setup mode event who payload outputEq choice.1).1 serial) := by
  classical
  let source := assessment.strategy who (setup.commitRecoveryInformation wellFormed who
    (phaseSourceView? setup mode runtime leaks who event view))
  let data := phaseRecoveryBindingData setup mode event who payload outputEq choice.1
  let response := phaseBindingResponse runtime leaks who event payload data.1 serial
  have lower := PhaseCount.phaseBindingSlotPolicy_mass runtime leaks bounds who event payload
    (fun _ _ => PMF.pure data.1) past view serial eligible data.1
  simp only [PMF.pure_apply_self, mul_one] at lower
  rw [phaseRecoverySlotPolicy, PMF.bind_apply]
  calc
    _ = source choice * ((PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
        past view).card : ENNReal)⁻¹ := mul_comm _ _
    _ ≤ source choice * PhaseCount.phaseBindingSlotPolicy runtime leaks bounds who event payload
        (fun _ _ => PMF.pure data.1) past view response := by
      simpa only [mul_comm] using mul_le_mul_left lower (source choice)
    _ ≤ _ := by
      have term := ENNReal.le_tsum (f := fun chosen => source chosen *
        (if (phaseRecoveryBindingData setup mode event who payload outputEq chosen.1).2 then
          PMF.pure (⟨none⟩ : (phaseApplication runtime leaks).Action) else
            PhaseCount.phaseBindingSlotPolicy runtime leaks bounds who event payload
              (fun _ _ => PMF.pure (phaseRecoveryBindingData setup mode event who payload
                outputEq chosen.1).1) past view) response) choice
      simpa only [notMissing, Bool.false_eq_true, ↓reduceIte, data, response, source] using term

/-- The lower bound uses the entire original mass of a typed result, even
when several auxiliary choices have the same result and omission data. -/
theorem phaseRecoverySlotPolicy_result_mass (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) (serial : Nat)
    (eligible : serial ∈ PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
      past view) (result : PublicationResult (L.Val payload)) :
    ((PhaseCount.phaseBindingSlots runtime leaks bounds who event payload past view).card :
        ENNReal)⁻¹ *
      ((assessment.strategy who (setup.commitRecoveryInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event view))).map
          (fun choice => phaseRecoveryBindingData setup mode event who payload outputEq
            choice.1)) (result, false) ≤
      phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment who event
        payload outputEq past view (phaseBindingResponse runtime leaks who event payload
          result serial) := by
  classical
  rw [PMF.map_apply, ← ENNReal.tsum_mul_left, phaseRecoverySlotPolicy, PMF.bind_apply]
  apply ENNReal.tsum_le_tsum
  intro choice
  dsimp only
  by_cases same : (result, false) =
      phaseRecoveryBindingData setup mode event who payload outputEq choice.1
  · have typed : (phaseRecoveryBindingData setup mode event who payload outputEq choice.1).1 =
        result := (congrArg Prod.fst same).symm
    have missing : (phaseRecoveryBindingData setup mode event who payload outputEq choice.1).2 =
        false := (congrArg Prod.snd same).symm
    rw [ite_eq_left same]
    have lower := PhaseCount.phaseBindingSlotPolicy_mass runtime leaks bounds who event payload
      (fun _ _ => PMF.pure result) past view serial eligible result
    simp only [PMF.pure_apply_self, mul_one] at lower
    simp only [missing, Bool.false_eq_true, ↓reduceIte, typed]
    simpa only [mul_comm] using mul_le_mul_left lower
      ((assessment.strategy who (setup.commitRecoveryInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event view))) choice)
  · simp only [ite_eq_right same, mul_zero, zero_le]

/-- A source omission retains its full mass on silence; it is not diluted by
the fresh-slot draw and cannot turn into a transmitted unusable commitment. -/
theorem phaseRecoverySlotPolicy_omission_mass (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (choice : setup.commitRecoveryModel.Choice who
      (setup.commitRecoveryInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event view)))
    (missing : (phaseRecoveryBindingData setup mode event who payload outputEq choice.1).2 = true) :
    (assessment.strategy who (setup.commitRecoveryInformation wellFormed who
      (phaseSourceView? setup mode runtime leaks who event view))) choice ≤
      phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment who event
        payload outputEq past view ⟨none⟩ := by
  classical
  rw [phaseRecoverySlotPolicy, PMF.bind_apply]
  simpa only [missing, ↓reduceIte, PMF.pure_apply_self, mul_one] using
    (ENNReal.le_tsum (f := fun chosen =>
      (assessment.strategy who (setup.commitRecoveryInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event view))) chosen *
      (if (phaseRecoveryBindingData setup mode event who payload outputEq chosen.1).2 then
        PMF.pure (⟨none⟩ : (phaseApplication runtime leaks).Action) else
          PhaseCount.phaseBindingSlotPolicy runtime leaks bounds who event payload
            (fun _ _ => PMF.pure (phaseRecoveryBindingData setup mode event who payload
              outputEq chosen.1).1) past view) ⟨none⟩) choice)

end Vegas
