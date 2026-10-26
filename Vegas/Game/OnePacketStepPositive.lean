/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSlotLawForced
import Vegas.Game.OnePacketIrregularBound

/-! # Responses have positive step response

A transmission gives the slot tier a positive factor: one without a pending
event, the uniform slot mass at a pending binding, and one at a pending reveal
(`Vegas.slotTierFactor_pos_of_transmits`); silence has silence factor one. With
a tremble scale strictly between zero and one, the step response of every
response is therefore positive (`Vegas.stepResponse_pos_of_respond`), and so is
the operational mass of the certificate's steps at every response
(`Vegas.certificate_mass_pos`). Irregular responses are then bounded by their
response mass over the operational mass
(`Vegas.IrregularStepBound.ofResponseMass`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  (bounds : MessageBounds (graph setup))

omit [Fintype Player] in
/-- **A transmission has a positive slot-tier factor.** -/
theorem slotTierFactor_pos_of_transmits (before after : LateKey setup runtime leaks)
    (sent : after.lastEmitted ≠ none) : 0 < slotTierFactor (runtime :=
      runtime) bounds before after := by
  have slotsPos : (0 : ℝ) < (trembleSlots setup bounds).card := by
    exact_mod_cast (trembleSlots_nonempty setup bounds).card_pos
  unfold slotTierFactor
  split
  · norm_num
  · split
    · unfold pendingBindingSlotFactor
      cases emitted : after.lastEmitted with
      | none => exact absurd emitted sent
      | some _ => exact one_div_pos.mpr slotsPos
    · unfold transmitFactor silenceFactor
      simp [sent]

variable {bounds} {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}

omit [Fintype Player] in
/-- **Every response has positive step response** under a tremble scale strictly
between zero and one. -/
theorem stepResponse_pos_of_respond {slots : Nat}
    (keyLaw : Option (LateKey setup runtime leaks) → PMF (LateOption slots)) {scale : ℝ}
    (positive : 0 < scale) (lt_one : scale < 1) (control next : (application setup runtime
      leaks).Control)
    {actor : Player} (acting : control.actor = some actor)
    (response : (application setup runtime leaks).Action)
    (nextEq : next.execution = control.execution.respond (application setup runtime leaks) actor
      response) :
    0 < stepResponse (runtime := runtime) bounds keyLaw scale (operationalState setup runtime
      leaks (some control))
      (operationalState setup runtime leaks (some next)) := by
  set before := LateKey.ofView setup runtime leaks actor (control.execution.recall actor)
    (control.execution.observe (application setup runtime leaks) actor)
  set after := LateKey.ofView setup runtime leaks actor
    ((control.execution.respond (application setup runtime leaks) actor response).recall actor)
    ((control.execution.respond (application setup runtime leaks) actor response).observe
      (application setup runtime leaks) actor)
  have form : stepResponse (runtime := runtime) bounds keyLaw scale (operationalState setup
    runtime leaks (some control))
      (operationalState setup runtime leaks (some next)) =
      slotCombination scale (mainFactor (runtime := runtime) bounds (keyLaw (some before)) before
        after)
        (silenceFactor (runtime := runtime) after) (slotTierFactor (runtime := runtime) bounds
          before after) := by
    unfold stepResponse operationalState
    dsimp only
    rw [acting]
    dsimp only
    rw [nextEq]
    rfl
  rw [form]
  obtain ⟨mainNonneg, _⟩ := mainFactor_mem (runtime := runtime) bounds (keyLaw (some before))
    before after
  obtain ⟨silenceNonneg, _⟩ := silenceFactor_mem (runtime := runtime) after
  obtain ⟨slotNonneg, _⟩ := slotTierFactor_mem (runtime := runtime) bounds before after
  have cube : scale ^ 3 < 1 := pow_lt_one₀ positive.le lt_one (by norm_num)
  have square : scale ^ 2 < 1 := pow_lt_one₀ positive.le lt_one (by norm_num)
  have squarePos : 0 < scale ^ 2 := pow_pos positive 2
  unfold slotCombination
  by_cases sent : after.lastEmitted = none
  · have silenceOne : silenceFactor (runtime := runtime) after = 1 := by
      unfold silenceFactor
      simp [sent]
    rw [silenceOne]
    have inner : 0 < scale * 1 + (1 - scale) * mainFactor (runtime := runtime) bounds (keyLaw
      (some before)) before
        after := by nlinarith
    have outer : 0 < scale ^ 2 * slotTierFactor (runtime := runtime) bounds before after + (1 -
      scale ^ 2) *
        (scale * 1 + (1 - scale) * mainFactor (runtime := runtime) bounds (keyLaw (some before))
          before after) := by
      nlinarith
    exact mul_pos (by linarith) outer
  · have slotPos := slotTierFactor_pos_of_transmits (runtime := runtime) bounds before after sent
    have rest : 0 ≤ (1 - scale ^ 2) * (scale * silenceFactor (runtime := runtime) after + (1 -
      scale) *
        mainFactor (runtime := runtime) bounds (keyLaw (some before)) before after) := by
      apply mul_nonneg (by linarith)
      nlinarith
    exact mul_pos (by linarith) (by nlinarith [mul_pos squarePos slotPos])

variable [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

/-- **The certificate's operational mass is positive at every response** whose
step is irregular, so irregular responses are bounded by their response mass
over the operational mass. -/
theorem certificate_mass_pos (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (small : ∀ n, scale n ≤ 1 / 4) (floor : ℕ → ℝ) (floor_pos : ∀ n, 0 < floor n)
    [Finite (onePacketProtocol setup runtime leaks bounds horizon scheduler).History]
    (floored : ∀ n, floor n ≤ contentFloor setup runtime leaks bounds horizon scheduler (sequence
      n))
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p))
    (who : Player)
    (error_tendsto : Tendsto (fun n => slotError (scale n) (floor n)
      (trembleSlots setup bounds).card) atTop (nhds 0)) :
    ∀ n {before after : (application setup runtime leaks).ProtocolState}
      (_ : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace before) joint
        legal
      (_ : after ∈ ((onePacketProtocol setup runtime leaks bounds horizon scheduler).step before
        ⟨joint, legal⟩).support) (control next : (application setup runtime leaks).Control),
      before = some control → after = some next →
      ¬ RegularStep setup runtime leaks bounds horizon scheduler (sequence n) who before joint
        after →
      0 < responseMass setup runtime leaks bounds horizon scheduler
        (certificateProfile setup runtime leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one weights n) control joint →
      0 < (certificateOperationalSteps (runtime := runtime) wellFormed sequence scale scale_pos
        scale_le_one small
        floor floor_pos floored covers capacity weights who error_tendsto).mass n
          (operationalState setup runtime leaks before) (operationalState setup runtime leaks
            after) := by
  intro n before after prior joint legal realized control next initialized reached irregular _
  cases acting : control.actor with
  | none =>
      exfalso
      subst initialized reached
      exact irregular fun actor acted => by
        rw [acting] at acted
        cases acted
  | some actor =>
      obtain ⟨response, _, _, nextEq, _⟩ :=
        onePacket_response_step (runtime := runtime) prior joint legal realized control next
          initialized reached acting
      subst initialized reached
      change roundOrResponseMass (runtime := runtime) (scheduler := scheduler) _ (operationalState
        setup runtime leaks
        (some control)) (operationalState setup runtime leaks (some next)) > 0
      unfold roundOrResponseMass
      change 0 < if control.actor = none then _ else _
      rw [acting]
      simp only [reduceCtorEq, ↓reduceIte]
      exact stepResponse_pos_of_respond (runtime := runtime) _ (scale_pos n)
        (lt_of_le_of_lt (small n) (by norm_num)) control next acting response nextEq

end Vegas
