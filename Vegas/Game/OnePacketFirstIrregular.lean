/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketZeroContent
import Vegas.Game.OnePacketSlotLawDischarge
import Vegas.Game.OnePacketIrregularBound

/-! # Irregular responses from forced states are cube-small

At a response of a forced player other than the observer, from a state forced
for the observer, an irregular response has content factor zero, so it commits
at a binding of the player's turn (`Vegas.zeroContent_binding`) and no tier of
the certificate's slot-trembled component gives it mass
(`Vegas.tierMasses_of_zeroContent`). Only the uniform tremble does, so its
response mass is at most the cube of the scale
(`Vegas.certificate_responseMass_le_cube`).
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

/-- **Irregular responses from forced states are cube-small.** At a response of a
forced player other than `who` from a state forced for `who`, an irregular
response has response mass at most the cube of the scale under the
certificate's profile. -/
theorem certificate_responseMass_le_cube
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (who : Player) (n : ℕ) {before after : (application setup leaks).ProtocolState}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before)
    (joint : Player → Option (application setup leaks).Action)
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal before joint)
    (realized : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
      ⟨joint, legal⟩).support) (control next : (application setup leaks).Control)
    (actor : Player) (initialized : before = some control) (reached : after = some next)
    (acting : control.actor = some actor) (other : actor ≠ who)
    (forcedWho : ForcedState setup leaks who (some control))
    (forcedActor : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup)
      horizon scheduler actor ((application setup leaks).observe actor (some control)))
    (irregular : ¬ RegularStep setup leaks bounds horizon scheduler (sequence n) who before joint
      after) :
    responseMass setup leaks bounds horizon scheduler
        (certificateProfile setup leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one weights n) control joint ≤ scale n ^ 3 := by
  obtain ⟨response, chosenJoint, member, nextEq, infoEq⟩ :=
    onePacket_response_step prior joint legal realized control next initialized reached acting
  subst initialized reached
  -- The response has content factor zero.
  have zero : contentFactor setup leaks (sequence n) actor control.execution
      (control.execution.respond (application setup leaks) actor response) response = 0 := by
    rcases (contentFactor_nonneg (setup := setup) (leaks := leaks) (sequence n) actor
      control.execution (control.execution.respond (application setup leaks) actor response)
      response).lt_or_eq with positive | zero
    · exfalso
      apply irregular
      intro responder acted different
      rw [acting] at acted
      cases Option.some.inj acted
      refine ⟨⟨forcedActor, forcedWho⟩, ?_⟩
      rw [chosenJoint, Option.getD_some, nextEq]
      exact positive
    · exact zero.symm
  have transmits : response.transmission ≠ none := by
    intro silent
    have silence : response = ⟨none⟩ := by
      rcases response with ⟨transmission⟩
      change transmission = none at silent
      rw [silent]
    rw [silence, contentFactor_silence] at zero
    exact one_ne_zero zero
  -- The responder owes no failure.
  obtain ⟨point, decoded, forcedPoint⟩ := (forcedState_iff_decodedPoint control).mp forcedWho
  have notOwed : ∀ found, decodedPoint setup control.execution.application.config = some found →
      ¬ ProtocolState.OwesFailure actor setup.program found := by
    intro found foundDecoded
    rw [decoded, Option.some.injEq] at foundDecoded
    subst foundDecoded
    exact (forcedPoint.2 actor other).2
  obtain ⟨remaining, controlActor, execution⟩ := control
  change controlActor = some actor at acting
  subst acting
  obtain ⟨event, payload, outputEq, codeEq, turn, node⟩ := zeroContent_binding (sequence n) prior
    notOwed response member transmits zero
  have capacityOne : 1 ≤ bounds.candidateCount :=
    Nat.one_le_iff_ne_zero.mpr fun none => by
      have := capacity actor
      omega
  have site := onePacket_coveredPendingBinding (sequence n) covers capacityOne prior actor event
    turn node
  -- The certificate's component at the responder's information.
  have played : (onePacketInformation setup leaks bounds horizon scheduler).infoOf actor prior ∈
      (onePacketModel setup leaks bounds (initialLaw setup) horizon
        scheduler).playedInformation actor :=
    (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).mem_playedInformation (history := ⟨_, prior⟩) legal.1
  rw [infoEq] at played
  have observed : (application setup leaks).observe actor
      (some ⟨remaining, some actor, execution⟩) =
      some (execution.recall actor, execution.observe (application setup leaks) actor) := by
    simp [ReactiveApplication.observe]
  rw [observed] at forcedActor
  obtain ⟨main, mainForm, profileEq⟩ := certificateProfile_eq_slotTrembled sequence scale
    scale_pos scale_le_one weights n _ played forcedActor
  refine responseMass_le_of_slotTrembled _ ⟨remaining, some actor, execution⟩ rfl joint
    (scale_pos n).le (scale_le_one n) main _ _ profileEq fun choice chosen => ?_
  rw [chosenJoint] at chosen
  obtain ⟨honestZero, slotZero, lateZero, silenceZero⟩ := tierMasses_of_zeroContent (sequence n)
    prior actor event site response transmits zero choice chosen
  refine ⟨?_, silenceZero, slotZero⟩
  rcases mainForm with rfl | ⟨late, rfl⟩
  · exact honestZero
  · rw [PMF.bind_apply]
    exact ENNReal.tsum_eq_zero.mpr fun option => by rw [lateZero option, mul_zero]

end Vegas
