/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketFirstIrregular

/-! # The certificate's response mass

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

end Vegas
