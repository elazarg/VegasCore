/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketResponseBound
import Vegas.Game.OnePacketSlotLawForced

/-! # Response likelihoods under directed binding repair

The one-packet certificate compares arbitrary actual response transitions with
the same operational endpoints. The comparison uses their slot laws, not an
invertible transformation of hidden values. It therefore applies to a directed
repair that replaces an unopenable binding with an intended binding.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}
  [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  [Finite (onePacketProtocol setup runtime leaks bounds horizon scheduler).History]

section Certificate

variable (wellFormed : setup.WellFormed)
  (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
  (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
  (small : ∀ n, scale n ≤ 1 / 4) (floor : ℕ → ℝ) (floor_pos : ∀ n, 0 < floor n)
  (floored : ∀ n, floor n ≤ contentFloor setup runtime leaks bounds horizon scheduler (sequence n))
  (covers : bounds.CoversOutputValues)
  (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
  {slots : Nat}
  (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p))

include wellFormed small floor_pos floored covers capacity

/-- A regular response dominates its source content times its operational slot
mass. Its full-menu tremble is at most the slot error times that same product. -/
theorem certificate_regularResponse_lower (who : Player) (n : ℕ)
    {control next : (application setup runtime leaks).Control}
    (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal (some control)
      joint)
    (realized : some next ∈ ((onePacketProtocol setup runtime leaks bounds horizon scheduler).step
      (some control) ⟨joint, legal⟩).support)
    {actor : Player} (acting : control.actor = some actor) (other : actor ≠ who)
    (regular : RegularStep setup runtime leaks bounds horizon scheduler (sequence n) who (some
      control)
      joint (some next)) :
    let content := contentFactor setup runtime leaks (sequence n) actor control.execution
      next.execution
      ((joint actor).getD ⟨none⟩)
    let response := stepResponse (runtime := runtime) bounds (keyWeights setup runtime leaks
      bounds horizon scheduler
      (weights n)) (scale n) (operationalState setup runtime leaks (some control))
      (operationalState setup runtime leaks (some next))
    content * response ≤ responseMass setup runtime leaks bounds horizon scheduler
        (certificateProfile setup runtime leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one weights n) control joint ∧
      scale n ^ 3 ≤ slotError (scale n) (floor n) (trembleSlots setup bounds).card *
        (content * response) := by
  obtain ⟨⟨forcedActor, forcedWho⟩, positive⟩ := regular actor acting other
  obtain ⟨main, alternative, slot, mainFactor', alternativeFactor, slotFactor, profileEq,
    mainMass, alternativeMass, slotMass, combination, cube⟩ :=
    certificate_slotLaw_forced (runtime := runtime) wellFormed sequence scale scale_pos
      scale_le_one small floor
      floor_pos floored covers capacity weights who n prior joint legal realized control next
      actor rfl rfl acting other forcedActor forcedWho positive
  refine ⟨?_, cube⟩
  have mass := stepProb_eq_responseMass (runtime := runtime) (certificateProfile setup runtime
    leaks bounds horizon scheduler
    sequence scale scale_pos scale_le_one weights n) prior joint legal realized control rfl acting
  rw [response_stepProb (runtime := runtime) _ prior joint legal realized control rfl acting,
    profileEq,
    slotTrembledChoice_apply_toReal , mainMass, alternativeMass, slotMass]
      at mass
  rw [← mass, ← combination]
  unfold slotCombination
  have uniform : 0 ≤ scale n ^ 3 * ((bounds.onePacketMenu runtime leaks).uniformPolicy
      (initialLaw setup) horizon scheduler actor _ (InformationModel.choicesOfLegal _ prior
        ⟨joint, legal⟩ actor)).toReal :=
    mul_nonneg (pow_nonneg (scale_pos n).le 3) ENNReal.toReal_nonneg
  nlinarith

/-- The likelihood of an arbitrary response is bounded by that of a regular
response with the same operational endpoints. Neither transition needs to be an
invertible image of the other. -/
theorem certificate_responseMass_le_of_operationally_equal (who : Player) (n : ℕ)
    {control next imageControl imageNext : (application setup runtime leaks).Control}
    (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal (some control)
      joint)
    (realized : some next ∈ ((onePacketProtocol setup runtime leaks bounds horizon scheduler).step
      (some control) ⟨joint, legal⟩).support)
    (imagePrior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace
      (some imageControl))
    (imageJoint : Player → Option (application setup runtime leaks).Action)
    (imageLegal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal
      (some imageControl) imageJoint)
    (imageRealized : some imageNext ∈ ((onePacketProtocol setup runtime leaks bounds horizon
      scheduler).step (some imageControl) ⟨imageJoint, imageLegal⟩).support)
    {actor : Player} (acting : control.actor = some actor)
    (imageActing : imageControl.actor = some actor) (other : actor ≠ who)
    (forcedActor : forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks)
      (initialLaw setup)
      horizon scheduler actor ((application setup runtime leaks).observe actor (some control)))
    (canonical : DisclosureCanonical setup runtime leaks bounds actor (control.execution.recall
      actor)
      (control.execution.observe (application setup runtime leaks) actor))
    (atTurn : ∀ response named, joint actor = some response →
      runtime.submittedEvent? leaks response = some named →
      control.execution.application.publicView.ownTurn? actor = some named)
    (beforeEq : operationalState setup runtime leaks (some imageControl) =
      operationalState setup runtime leaks (some control))
    (afterEq : operationalState setup runtime leaks (some imageNext) =
      operationalState setup runtime leaks (some next))
    (imageRegular : RegularStep setup runtime leaks bounds horizon scheduler (sequence n) who
      (some imageControl) imageJoint (some imageNext)) :
    responseMass setup runtime leaks bounds horizon scheduler
        (certificateProfile setup runtime leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one weights n) control joint ≤
      (1 / floor n + slotError (scale n) (floor n) (trembleSlots setup bounds).card) *
        responseMass setup runtime leaks bounds horizon scheduler
          (certificateProfile setup runtime leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one weights n) imageControl imageJoint := by
  obtain ⟨lower, imageCube⟩ := certificate_regularResponse_lower (runtime := runtime) wellFormed
    sequence scale
    scale_pos scale_le_one small floor floor_pos floored covers capacity weights who n imagePrior
    imageJoint imageLegal imageRealized imageActing other imageRegular
  rw [beforeEq, afterEq] at lower imageCube
  set content := contentFactor setup runtime leaks (sequence n) actor imageControl.execution
    imageNext.execution ((imageJoint actor).getD ⟨none⟩)
  set response := stepResponse (runtime := runtime) bounds (keyWeights setup runtime leaks bounds
    horizon scheduler
    (weights n)) (scale n) (operationalState setup runtime leaks (some control))
    (operationalState setup runtime leaks (some next))
  have historyBound := certificate_responseMass_le_response (runtime := runtime) sequence scale
    scale_pos scale_le_one
    small floor floor_pos floored covers capacity weights n prior joint legal realized control next
    actor rfl rfl acting forcedActor canonical atTurn
  have imagePositive := (imageRegular actor imageActing other).2
  have imageFloor : floor n ≤ content := (floored n).trans (contentFloor_le_of_step (runtime :=
    runtime) (sequence n)
    imagePrior imageJoint imageLegal imageRealized imageControl imageNext rfl rfl actor
    imagePositive)
  have responseNonneg : 0 ≤ response := stepResponse_nonneg (runtime := runtime) bounds _
    (scale_pos n).le
    (scale_le_one n) _ _
  have errorNonneg := slotError_nonneg (scale_pos n).le (floor_pos n)
    (trembleSlots setup bounds).card
  have inverse : 1 ≤ 1 / floor n * content := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (floor_pos n), one_mul]
    exact imageFloor
  have ratioNonneg : 0 ≤ 1 / floor n + slotError (scale n) (floor n)
      (trembleSlots setup bounds).card :=
    add_nonneg (div_nonneg zero_le_one (floor_pos n).le) errorNonneg
  calc _ ≤ response + scale n ^ 3 := historyBound
    _ ≤ (1 / floor n + slotError (scale n) (floor n) (trembleSlots setup bounds).card) *
        (content * response) := by
      have scaled : response ≤ 1 / floor n * (content * response) := by
        rw [← mul_assoc]
        nlinarith
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left lower ratioNonneg

/-- At an irregular response of another forced player, the corresponding
regular response dominates its likelihood by the vanishing slot error whenever
the operational endpoints agree. -/
theorem certificate_irregularResponseMass_le_of_operationally_equal (who : Player) (n : ℕ)
    {control next imageControl imageNext : (application setup runtime leaks).Control}
    (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal (some control)
      joint)
    (realized : some next ∈ ((onePacketProtocol setup runtime leaks bounds horizon scheduler).step
      (some control) ⟨joint, legal⟩).support)
    (imagePrior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace
      (some imageControl))
    (imageJoint : Player → Option (application setup runtime leaks).Action)
    (imageLegal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal
      (some imageControl) imageJoint)
    (imageRealized : some imageNext ∈ ((onePacketProtocol setup runtime leaks bounds horizon
      scheduler).step (some imageControl) ⟨imageJoint, imageLegal⟩).support)
    {actor : Player} (acting : control.actor = some actor)
    (imageActing : imageControl.actor = some actor) (other : actor ≠ who)
    (forcedWho : ForcedState setup runtime leaks who (some control))
    (forcedActor : forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks)
      (initialLaw setup)
      horizon scheduler actor ((application setup runtime leaks).observe actor (some control)))
    (irregular : ¬ RegularStep setup runtime leaks bounds horizon scheduler (sequence n) who
      (some control) joint (some next))
    (beforeEq : operationalState setup runtime leaks (some imageControl) =
      operationalState setup runtime leaks (some control))
    (afterEq : operationalState setup runtime leaks (some imageNext) =
      operationalState setup runtime leaks (some next))
    (imageRegular : RegularStep setup runtime leaks bounds horizon scheduler (sequence n) who
      (some imageControl) imageJoint (some imageNext)) :
    responseMass setup runtime leaks bounds horizon scheduler
        (certificateProfile setup runtime leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one weights n) control joint ≤
      slotError (scale n) (floor n) (trembleSlots setup bounds).card *
        responseMass setup runtime leaks bounds horizon scheduler
          (certificateProfile setup runtime leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one weights n) imageControl imageJoint := by
  have cube := certificate_responseMass_le_cube (runtime := runtime) sequence scale scale_pos
    scale_le_one weights
    covers capacity who n prior joint legal realized control next actor rfl rfl acting other
    forcedWho forcedActor irregular
  obtain ⟨lower, imageCube⟩ := certificate_regularResponse_lower (runtime := runtime) wellFormed
    sequence scale
    scale_pos scale_le_one small floor floor_pos floored covers capacity weights who n imagePrior
    imageJoint imageLegal imageRealized imageActing other imageRegular
  rw [beforeEq, afterEq] at lower imageCube
  exact cube.trans (imageCube.trans (mul_le_mul_of_nonneg_left lower
    (slotError_nonneg (scale_pos n).le (floor_pos n) _)))

end Certificate

end Vegas
