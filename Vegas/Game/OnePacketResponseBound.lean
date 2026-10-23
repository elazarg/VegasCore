/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketFirstIrregular
import Vegas.Game.OnePacketCounterpartBound
import Vegas.Game.OnePacketSlotLawForced

/-! # The response bound for the certificate

At a response of a forced player `r` other than the observer, with a canonical
disclosure, the certificate's response mass is at most the step response plus
the cube of the scale, owing or not
(`Vegas.certificate_responseMass_le_response`):

* with positive content, the slot law at the response
  (`Vegas.certificate_slotLaw_at`) gives the content factor, at most one, times
  the step response, plus the uniform tremble;
* with content zero, a response naming the event of `r`'s turn commits at a
  binding (`Vegas.zeroContent_binding_of_turn`), where no tier gives it mass,
  so only the uniform tremble does.

Under a hidden swap whose image response is regular, the image has content at
least the floor, the same step response, since the swap keeps the operational
state, and a cube of the scale within the slot error. Its response's positive
content puts it at the image's turn, and the swap keeps the public view and the
event a packet names, so a zero-content response is at `r`'s turn too. Hence
the certificate meets the response bound with ratio the inverse floor plus the
slot error (`Vegas.swapResponseBound_certificate`).
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

/-- **The certificate's response mass is at most the step response plus the
cube of the scale** at a response of a forced player with a canonical disclosure
whose transmissions name the event of its turn. -/
theorem certificate_responseMass_le_response
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (small : ∀ n, scale n ≤ 1 / 4) (floor : ℕ → ℝ) (floor_pos : ∀ n, 0 < floor n)
    [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History]
    (floored : ∀ n, floor n ≤ contentFloor setup leaks bounds horizon scheduler (sequence n))
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (n : ℕ) {before after : (application setup leaks).ProtocolState}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before)
    (joint : Player → Option (application setup leaks).Action)
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal before joint)
    (realized : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
      ⟨joint, legal⟩).support) (control next : (application setup leaks).Control)
    (actor : Player) (initialized : before = some control) (reached : after = some next)
    (acting : control.actor = some actor)
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler actor ((application setup leaks).observe actor (some control)))
    (canonical : DisclosureCanonical setup leaks bounds actor (control.execution.recall actor)
      (control.execution.observe (application setup leaks) actor))
    (atTurn : ∀ response named, joint actor = some response →
      (runtime setup).submittedEvent? leaks response = some named →
      control.execution.application.publicView.ownTurn? actor = some named) :
    responseMass setup leaks bounds horizon scheduler
        (certificateProfile setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one weights n) control joint ≤
      stepResponse bounds (keyWeights setup leaks bounds horizon scheduler (weights n))
          (scale n) (operationalState setup leaks (some control))
          (operationalState setup leaks (some next)) +
        scale n ^ 3 := by
  obtain ⟨response, chosenJoint, member, nextEq, infoEq⟩ :=
    onePacket_response_step prior joint legal realized control next initialized reached acting
  subst initialized reached
  have played : (onePacketInformation setup leaks bounds horizon scheduler).infoOf actor prior ∈
      (onePacketModel setup leaks bounds (initialLaw setup) horizon
        scheduler).playedInformation actor :=
    (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).mem_playedInformation (history := ⟨_, prior⟩) legal.1
  have observed : (application setup leaks).observe actor (some control) =
      some (control.execution.recall actor,
        control.execution.observe (application setup leaks) actor) := by
    simp [ReactiveApplication.observe, acting]
  rw [observed] at forced
  have responseNonneg := stepResponse_nonneg bounds (keyWeights setup leaks bounds horizon
    scheduler (weights n)) (scale_pos n).le (scale_le_one n)
    (operationalState setup leaks (some control)) (operationalState setup leaks (some next))
  have cubeNonneg : 0 ≤ scale n ^ 3 := pow_nonneg (scale_pos n).le 3
  rcases (contentFactor_nonneg (setup := setup) (leaks := leaks) (sequence n) actor
    control.execution next.execution response).lt_or_eq with positive | zero
  · -- Positive content: the slot law at the response.
    have positiveJoint : 0 < contentFactor setup leaks (sequence n) actor control.execution
        next.execution ((joint actor).getD ⟨none⟩) := by
      rw [chosenJoint, Option.getD_some]
      exact positive
    have floorStep := contentFloor_le_of_step (sequence n) prior joint legal realized control next
      rfl rfl actor positiveJoint
    rw [chosenJoint, Option.getD_some] at floorStep
    obtain ⟨main, alternative, slot, mainFactor', alternativeFactor, slotFactor, profileEq,
      mainMass, alternativeMass, slotMass, combination, _⟩ :=
      certificate_slotLaw_at sequence scale scale_pos scale_le_one small floor floor_pos covers
        capacity weights n prior acting forced canonical response member nextEq positive
        (fun _ => (floored n).trans floorStep) _ infoEq played
        (InformationModel.choicesOfLegal _ prior ⟨joint, legal⟩ actor) chosenJoint
    have mass := stepProb_eq_responseMass (certificateProfile setup leaks bounds horizon
      scheduler sequence scale scale_pos scale_le_one weights n) prior joint legal realized
      control rfl acting
    rw [response_stepProb _ prior joint legal realized control rfl acting, profileEq,
      slotTrembledChoice_apply_toReal, mainMass, alternativeMass, slotMass] at mass
    rw [← mass, ← combination]
    set content := contentFactor setup leaks (sequence n) actor control.execution
      next.execution response
    have contentLe : content ≤ 1 := contentFactor_le_one _ _ _ _ _ _ _
    have uniformLe : ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy (initialLaw setup)
        horizon scheduler actor _ (InformationModel.choicesOfLegal _ prior ⟨joint, legal⟩
          actor)).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one
        (by rw [ENNReal.ofReal_one]; exact PMF.coe_le_one _ _)
    have combinationNonneg : 0 ≤ slotCombination (scale n) mainFactor' alternativeFactor
        slotFactor := by
      rw [combination]
      exact responseNonneg
    have contentNonneg : 0 ≤ content := positive.le
    unfold slotCombination at combinationNonneg ⊢
    nlinarith [mul_le_mul_of_nonneg_left uniformLe cubeNonneg,
      mul_le_mul_of_nonneg_right contentLe combinationNonneg]
  · -- Content zero: a commitment at a binding of the turn, given no tier mass.
    have zeroResponse : contentFactor setup leaks (sequence n) actor control.execution
        (control.execution.respond (application setup leaks) actor response) response = 0 := by
      rw [← nextEq]
      exact zero.symm
    have transmits : response.transmission ≠ none := by
      intro silent
      have silence : response = ⟨none⟩ := by
        rcases response with ⟨transmission⟩
        change transmission = none at silent
        rw [silent]
      rw [silence, contentFactor_silence] at zeroResponse
      exact one_ne_zero zeroResponse
    obtain ⟨remaining, controlActor, execution⟩ := control
    change controlActor = some actor at acting
    subst acting
    obtain ⟨event, payload, outputEq, codeEq, turn, node⟩ := zeroContent_binding_of_turn
      (sequence n) prior response member transmits zeroResponse
      (fun named submitted => atTurn response named chosenJoint submitted)
    have capacityOne : 1 ≤ bounds.candidateCount :=
      Nat.one_le_iff_ne_zero.mpr fun none => by
        have := capacity actor
        omega
    have site := onePacket_coveredPendingBinding (sequence n) covers capacityOne prior actor event
      turn node
    rw [infoEq] at played
    obtain ⟨main, mainForm, profileEq⟩ := certificateProfile_eq_slotTrembled sequence scale
      scale_pos scale_le_one weights n _ played forced
    refine (responseMass_le_of_slotTrembled _ ⟨remaining, some actor, execution⟩ rfl joint
      (scale_pos n).le (scale_le_one n) main _ _ profileEq fun choice chosen => ?_).trans
      (le_add_of_nonneg_left responseNonneg)
    rw [chosenJoint] at chosen
    obtain ⟨honestZero, slotZero, lateZero, silenceZero⟩ := tierMasses_of_zeroContent
      (sequence n) prior actor event site response transmits zeroResponse choice chosen
    refine ⟨?_, silenceZero, slotZero⟩
    rcases mainForm with rfl | ⟨late, rfl⟩
    · exact honestZero
    · rw [PMF.bind_apply]
      exact ENNReal.tsum_eq_zero.mpr fun option => by rw [lateZero option, mul_zero]

/-- **The certificate meets the response bound** with the inverse floor plus the
slot error as the ratio. -/
theorem swapResponseBound_certificate (wellFormed : setup.WellFormed)
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
    SwapResponseBound setup leaks bounds horizon scheduler sequence
      (certificateProfile setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one weights) n who
      (1 / floor n + slotError (scale n) (floor n) (trembleSlots setup bounds).card) := by
  intro swap allowed before after prior joint legal realized guardAfter imagePrior imageLegal
    imageRealized control next actor beforeEq afterEq acting other forcedActor canonical imageStep
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
    (operationalState setup leaks (swap.protocolState (some next))) with responseEq
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
  -- The swap keeps the operational states, so the history has the same step response.
  have guardBefore : SwapGuardState setup swap allowed (some control) :=
    swapGuard_of_transition swap (initialLaw setup) horizon scheduler control next joint realized
      guardAfter
  have sameResponse : response = stepResponse bounds (keyWeights setup leaks bounds horizon
      scheduler (weights n)) (scale n) (operationalState setup leaks (some control))
      (operationalState setup leaks (some next)) := by
    rw [responseEq, operationalState_swap swap _ guardBefore, operationalState_swap swap _
      guardAfter]
  -- The history's transmissions name the event of the actor's turn.
  have atTurn : ∀ response named, joint actor = some response →
      (runtime setup).submittedEvent? leaks response = some named →
      control.execution.application.publicView.ownTurn? actor = some named := by
    intro original named chosen submitted
    obtain ⟨imageResponse, imageChosen, imageMember, _, _⟩ := onePacket_response_step imagePrior
      (swap.joint joint) imageLegal imageRealized (swap.control control) (swap.control next) rfl
      rfl imageActing
    have imageEq : imageResponse = swap.action original := by
      have chosenImage := imageChosen
      simp only [HiddenSwap.joint, chosen, Option.map_some] at chosenImage
      exact (Option.some.inj chosenImage).symm
    cases sends : original.transmission with
    | none =>
        unfold EventGraphRuntime.submittedEvent? at submitted
        rw [sends] at submitted
        cases submitted
    | some material =>
        unfold EventGraphRuntime.submittedEvent? at submitted
        rw [sends] at submitted
        have imageSends : imageResponse.transmission = some (material.swap swap) := by
          rw [imageEq]
          simp [HiddenSwap.action, sends]
        have positiveImage : 0 < contentFactor setup leaks (sequence n) actor
            (swap.control control).execution (swap.control next).execution imageResponse := by
          have positiveJoint : 0 < contentFactor setup leaks (sequence n) actor
              (swap.control control).execution (swap.control next).execution
              ((swap.joint joint actor).getD ⟨none⟩) := imagePositive
          rw [imageChosen, Option.getD_some] at positiveJoint
          exact positiveJoint
        obtain ⟨event, turn, _, packetEvent⟩ := onePacket_content_pos (sequence n) imagePrior actor
          imageResponse imageMember (material.swap swap) imageSends _ positiveImage
        have namedEq : named = event := by
          rw [WitnessedSubmission.swap_call, Submission.swap_packet] at packetEvent
          exact Option.some.inj (submitted.symm.trans packetEvent)
        subst namedEq
        have samePublic : (swap.control control).execution.application.publicView =
            control.execution.application.publicView :=
          EventGraphRuntime.State.swap_publicView swap _
        rw [samePublic] at turn
        exact turn
  have historyBound := certificate_responseMass_le_response sequence scale scale_pos scale_le_one
    small floor floor_pos floored covers capacity weights n prior joint legal realized control next
    actor rfl rfl acting forcedActor canonical atTurn
  rw [← sameResponse] at historyBound
  -- The image's content is at least the floor.
  have imageFloor : floor n ≤ content := (floored n).trans (contentFloor_le_of_step (sequence n)
    imagePrior (swap.joint joint) imageLegal imageRealized (swap.control control)
    (swap.control next) rfl rfl actor imagePositive)
  have responseNonneg : 0 ≤ response := stepResponse_nonneg bounds _ (scale_pos n).le
    (scale_le_one n) _ _
  have errorNonneg := slotError_nonneg (scale_pos n).le (floor_pos n)
    (trembleSlots setup bounds).card
  have inverse : 1 ≤ 1 / floor n * content := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (floor_pos n), one_mul]
    exact imageFloor
  have ratioNonneg : 0 ≤ 1 / floor n + slotError (scale n) (floor n)
      (trembleSlots setup bounds).card :=
    add_nonneg (div_nonneg zero_le_one (floor_pos n).le) errorNonneg
  calc responseMass setup leaks bounds horizon scheduler
        (certificateProfile setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one weights n) control joint ≤ response + scale n ^ 3 := historyBound
    _ ≤ (1 / floor n + slotError (scale n) (floor n) (trembleSlots setup bounds).card) *
          (content * response) := by
        have scaled : response ≤ 1 / floor n * (content * response) := by
          rw [← mul_assoc]
          nlinarith
        nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left lower ratioNonneg

end Vegas
