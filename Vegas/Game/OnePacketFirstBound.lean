/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketFirstIrregular
import Vegas.Game.OnePacketCounterpartBound
import Vegas.Game.OnePacketSlotLawForced

/-! # The first-irregular-step bound for the certificate

At a regular response with positive content, the certificate's slot-trembled
component gives the realized choice at least its content factor times the step
response, and the cube of the scale is at most the slot error times that
product (`Vegas.certificate_slotLaw_forced`). An irregular response from a forced
state has mass at most the cube of the scale
(`Vegas.certificate_responseMass_le_cube`). So the certificate's profiles meet
the first-step bound with the slot error as the ratio
(`Vegas.swapFirstBound_certificate`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

/-- **The certificate meets the first-step bound** with the slot error as the
ratio. -/
theorem swapFirstBound_certificate (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (small : ∀ n, scale n ≤ 1 / 4) (floor : ℕ → ℝ) (floor_pos : ∀ n, 0 < floor n)
    [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History]
    (floored : ∀ n, floor n ≤ contentFloor setup leaks bounds horizon scheduler (sequence n))
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (who : Player) (n : ℕ) :
    SwapFirstBound setup leaks bounds horizon scheduler sequence
      (certificateProfile setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one weights) n who
      (slotError (scale n) (floor n) (trembleSlots setup bounds).card) := by
  intro swap allowed before after prior joint legal realized _ imagePrior imageLegal
    imageRealized control next actor beforeEq afterEq acting other forcedWho forcedActor imageStep
    _ irregularStep
  have cube := certificate_responseMass_le_cube sequence scale scale_pos scale_le_one weights
    covers capacity who n prior joint legal realized control next actor beforeEq afterEq acting
    other forcedWho forcedActor irregularStep
  subst beforeEq afterEq
  have imageActing : (swap.control control).actor = some actor := acting
  obtain ⟨⟨imageForcedActor, imageForcedWho⟩, imagePositive⟩ := imageStep actor acting other
  obtain ⟨main, alternative, slot, mainFactor', alternativeFactor, slotFactor, profileEq,
    mainMass, alternativeMass, slotMass, combination, imageCube⟩ :=
    certificate_slotLaw_forced wellFormed sequence scale scale_pos scale_le_one small floor
      floor_pos floored covers capacity weights who n imagePrior (swap.joint joint) imageLegal
      imageRealized (swap.control control) (swap.control next) actor rfl rfl imageActing other
      imageForcedActor imageForcedWho imagePositive
  -- The image's response mass is at least its content times the step response.
  have imageMass := stepProb_eq_responseMass (certificateProfile setup leaks bounds horizon
    scheduler sequence scale scale_pos scale_le_one weights n) imagePrior (swap.joint joint)
    imageLegal imageRealized (swap.control control) rfl imageActing
  rw [response_stepProb _ imagePrior (swap.joint joint) imageLegal imageRealized
    (swap.control control) rfl imageActing, profileEq,
    slotTrembledChoice_apply_toReal, mainMass, alternativeMass, slotMass] at imageMass
  set content := contentFactor setup leaks (sequence n) actor (swap.control control).execution
    (swap.control next).execution ((swap.joint joint actor).getD ⟨none⟩)
  set response := stepResponse bounds (keyWeights setup leaks bounds horizon scheduler
    (weights n)) (scale n) (operationalState setup leaks (swap.protocolState (some control)))
    (operationalState setup leaks (swap.protocolState (some next)))
  have lower : content * response ≤ responseMass setup leaks bounds horizon scheduler
      (certificateProfile setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one weights n) (swap.control control) (swap.joint joint) := by
    rw [← imageMass, ← combination]
    unfold slotCombination
    have uniform : 0 ≤ scale n ^ 3 * ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy
        (initialLaw setup) horizon scheduler actor _ (InformationModel.choicesOfLegal _
          imagePrior ⟨swap.joint joint, imageLegal⟩ actor)).toReal :=
      mul_nonneg (pow_nonneg (scale_pos n).le 3) ENNReal.toReal_nonneg
    nlinarith
  calc responseMass setup leaks bounds horizon scheduler
        (certificateProfile setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one weights n) control joint ≤ scale n ^ 3 := cube
    _ ≤ slotError (scale n) (floor n) (trembleSlots setup bounds).card * (content * response) :=
        imageCube
    _ ≤ _ := mul_le_mul_of_nonneg_left lower (slotError_nonneg (scale_pos n).le (floor_pos n) _)

end Vegas
