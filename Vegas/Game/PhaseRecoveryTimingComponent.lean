/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoverySlotComponent
import Vegas.Game.OnePacketDelivery

/-! # Source binding draws before physical timing and serial selection -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

open Classical in
/-- An explicit bounded serial has one legality guard for all source results.
Waiting and an original missing move emit nothing. -/
def phaseBindingTimingResponse (who : Player) (event : (serviceGraph setup mode).EventId)
    (payload : L.Ty) (option : LateOption bounds.candidateCount)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (data : PublicationResult (L.Val payload) × Bool) :
    (phaseApplication runtime leaks).Action :=
  if data.2 then ⟨none⟩ else
    match option with
    | none => ⟨none⟩
    | some serial =>
        if serial.val ∈ PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
            past view then phaseBindingResponse runtime leaks who event payload data.1 serial.val
        else ⟨none⟩

theorem phaseBindingTimingResponse_covered (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (option : LateOption bounds.candidateCount)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (data : PublicationResult (L.Val payload) × Bool) :
    phaseBindingTimingResponse setup mode runtime leaks bounds who event payload option past view
      data ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  classical
  unfold phaseBindingTimingResponse
  split
  · exact PhaseCount.silence_onePacket runtime leaks bounds who past view
  · split
    · exact PhaseCount.silence_onePacket runtime leaks bounds who past view
    · split
      · rename_i serial eligible
        exact (Finset.mem_filter.mp eligible).2.2 data.1
      · exact PhaseCount.silence_onePacket runtime leaks bounds who past view

/-- The complete original auxiliary choice is sampled before the timing
encoder. The tag retains its result and its distinct missing flag even when
the physical option waits or its serial is unavailable. -/
def phaseRecoveryTimingTaggedLaw (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (option : LateOption bounds.candidateCount)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    PMF ((PublicationResult (L.Val payload) × Bool) × (phaseApplication runtime leaks).Action) :=
  (assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
    (phaseSourceView? setup mode runtime leaks who event view))).map fun choice =>
      let data := phaseRecoveryBindingData setup mode event who payload outputEq choice.1
      (data, phaseBindingTimingResponse setup mode runtime leaks bounds who event payload
        option past view data)

/-- Physical behavior is the response marginal of the unchanged source draw. -/
def phaseRecoveryTimingPolicy (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (option : LateOption bounds.candidateCount) : (phaseApplication runtime leaks).Policy :=
  fun past view => (phaseRecoveryTimingTaggedLaw setup mode runtime leaks bounds wellFormed
    assessment who event payload outputEq option past view).map Prod.snd

/-- Timing does not reweight the latent result or omission draw. -/
theorem phaseRecoveryTimingTaggedLaw_source (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (option : LateOption bounds.candidateCount)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    (phaseRecoveryTimingTaggedLaw setup mode runtime leaks bounds wellFormed assessment who
        event payload outputEq option past view).map Prod.fst =
      (assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event view))).map
          (fun choice => phaseRecoveryBindingData setup mode event who payload outputEq
            choice.1) := by
  rw [phaseRecoveryTimingTaggedLaw, PMF.map_comp]
  rfl

theorem phaseRecoveryTimingPolicy_covered (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (option : LateOption bounds.candidateCount)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed
      assessment who event payload outputEq option past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  rw [phaseRecoveryTimingPolicy, phaseRecoveryTimingTaggedLaw, PMF.map_comp] at supported
  obtain ⟨choice, _drawn, rfl⟩ := (PMF.mem_support_map_iff ..).mp supported
  exact phaseBindingTimingResponse_covered setup mode runtime leaks bounds who event payload
    option past view _

/-- Waiting does not turn an accepted typed failure into a sampled source
omission; it erases only the response marginal of the unchanged tagged law. -/
theorem phaseRecoveryTimingPolicy_wait (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed assessment who event
      payload outputEq none past view = PMF.pure ⟨none⟩ := by
  rw [phaseRecoveryTimingPolicy, phaseRecoveryTimingTaggedLaw, PMF.map_comp]
  have constant (data : PublicationResult (L.Val payload) × Bool) :
      phaseBindingTimingResponse setup mode runtime leaks bounds who event payload none past view
        data = ⟨none⟩ := by
    unfold phaseBindingTimingResponse
    split <;> rfl
  simp only [Function.comp_def, constant]
  exact PMF.map_const _ _

/-- At a legal serial, the encoder is the existing physical response to the
original auxiliary move, including both missing and accepted-failure branches. -/
theorem phaseRecoveryTimingPolicy_send (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (serial : Fin bounds.candidateCount)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (eligible : serial.val ∈ PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
      past view) :
    phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed assessment who event
        payload outputEq (some serial) past view =
      (assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event view))).map
          (phaseRecoveryBindingResponse setup mode runtime leaks who event payload outputEq
            serial.val ·.val) := by
  rw [phaseRecoveryTimingPolicy, phaseRecoveryTimingTaggedLaw, PMF.map_comp]
  apply map_congr_on_support
  intro choice _drawn
  simp only [Function.comp_def, phaseBindingTimingResponse, phaseRecoveryBindingResponse,
    eligible, ↓reduceIte]

/-- A legal send serial preserves the original result and missing flag in the
actual post-response catalogue and packet decision. -/
theorem phaseRecoveryTimingPolicy_result_law (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (execution : (phaseApplication runtime leaks).Execution) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (serial : Fin bounds.candidateCount)
    (eligible : serial.val ∈ PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
      (execution.recall who) (execution.observe (phaseApplication runtime leaks) who)) :
    (phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed assessment who event
        payload outputEq (some serial) (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who)).map
      (phaseBindingResponseOutcome setup mode runtime leaks execution who payload) =
      (assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (execution.observe (phaseApplication runtime leaks) who)))).map
            (fun choice => phaseRecoveryBindingData setup mode event who payload outputEq
              choice.1) := by
  classical
  have fresh := (Finset.mem_filter.mp eligible).2.1
  rw [phaseRecoveryTimingPolicy_send setup mode runtime leaks bounds wellFormed assessment who
    event payload outputEq serial _ _ eligible, PMF.map_comp]
  apply map_congr_on_support
  intro choice _drawn
  change phaseBindingResponseOutcome setup mode runtime leaks execution who payload
      (phaseRecoveryBindingResponse setup mode runtime leaks who event payload outputEq
        serial.val choice.1) =
    phaseRecoveryBindingData setup mode event who payload outputEq choice.1
  generalize choiceEq : choice.1 = move
  cases move with
  | none =>
      change (_, false) = (_, false)
      exact congrArg (fun result => (result, false))
        (phaseBindingResponse_result runtime leaks execution who event payload .failure serial.val
          fresh)
  | some move =>
      cases missing : move.missing with
      | true =>
          simp only [phaseRecoveryBindingResponse, phaseRecoveryBindingData, Option.elim_some,
            missing, ↓reduceIte, phaseBindingResponseOutcome]
          rfl
      | false =>
          simp only [phaseRecoveryBindingResponse, phaseRecoveryBindingData, Option.elim_some,
            missing, Bool.false_eq_true, ↓reduceIte, phaseBindingResponseOutcome]
          change (_, false) = (_, false)
          exact congrArg (fun result => (result, false))
            (phaseBindingResponse_result runtime leaks execution who event payload _ serial.val
              fresh)

end Vegas
