/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketEnvironmentSteps
import Vegas.Game.OnePacketSlotTrembles

/-! # Responses under slot-trembled components

The mass of a response step of the one-packet game is the responder's choice
mass (`Vegas.response_stepProb`). Under a slot-trembled component, a choice's
mass is the full-menu uniform tremble, at most the cube of the scale, plus a
combination of the main, alternative and slot-tier masses. When those three
masses at the realized choice are its content factor times factors `main`,
`alternative` and `slot`, the choice mass is the content factor times
`(1 - s³)(s² slot + (1 - s²)(s alternative + (1 - s) main))` up to at most `s³`
(`Vegas.slotTrembledChoice_near`).

**Component steps from slot-trembled components.** Suppose that at every
regular response of another player the responder plays a slot-trembled
component; that at the realized choice its main, alternative and slot-tier
laws give the content factor times factors whose combination is a function of
the operational states before and after the response; and that the cube of the
scale is at most the error times the content factor times that combination.
Then the operational steps of the factorization hold
(`Vegas.OperationalSteps.ofSlotComponents`). The choice-level factorization of
the three laws is where menu adequacy and the injectivity of the honest
realization enter: the slot tier draws the value by the as-if-honest law and
the slot uniformly and independently (`Vegas.slotPairs_apply`), and the main
and alternative laws send the as-if-honest response at the canonical slot. The
floor holds along a tremble sequence once the content factor is bounded below
by the intended step floor and the scale is negligible against it.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **The mass of a response step.** It is the responder's mass, at its
information, of the choice it made. -/
theorem response_stepProb
    (profile : ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    {before after : (application setup leaks).ProtocolState}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before)
    (joint : Player → Option (application setup leaks).Action)
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal before joint)
    (realized : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
      ⟨joint, legal⟩).support) (control : (application setup leaks).Control)
    (initialized : before = some control) {actor : Player} (acting : control.actor = some actor) :
    InformationModel.stepProb (onePacketInformation setup leaks bounds horizon scheduler)
        profile prior ⟨joint, legal⟩ after =
      (profile actor _ (InformationModel.choicesOfLegal
        (onePacketInformation setup leaks bounds horizon scheduler) prior ⟨joint, legal⟩
          actor)).toReal := by
  subst initialized
  have active : (application setup leaks).actor (some control) = some actor := acting
  rw [stepProb_of_actor profile prior joint legal active]
  change _ ∈ ((application setup leaks).transition (initialLaw setup) horizon scheduler
    (some control) joint).support at realized
  rw [transition_respond control acting joint] at realized ⊢
  rw [(PMF.mem_support_pure_iff _ _).mp realized, PMF.pure_apply_self, ENNReal.toReal_one,
    mul_one]

/-- The combination of main, alternative and slot-tier factors that a
slot-trembled component gives a choice outside its full-menu tremble. -/
def slotCombination (scale main alternative slot : ℝ) : ℝ :=
  (1 - scale ^ 3) * (scale ^ 2 * slot + (1 - scale ^ 2) * (scale * alternative +
    (1 - scale) * main))

omit [DecidableEq Player] [Fintype Player] in
theorem slotCombination_nonneg {scale main alternative slot : ℝ} (nonnegative : 0 ≤ scale)
    (le_one : scale ≤ 1) (mainNonneg : 0 ≤ main) (alternativeNonneg : 0 ≤ alternative)
    (slotNonneg : 0 ≤ slot) : 0 ≤ slotCombination scale main alternative slot := by
  unfold slotCombination
  have cube : scale ^ 3 ≤ 1 := pow_le_one₀ nonnegative le_one
  have square : scale ^ 2 ≤ 1 := pow_le_one₀ nonnegative le_one
  have : 0 ≤ 1 - scale := by linarith
  positivity

variable (setup leaks bounds) in
/-- **A slot-trembled choice near its content.** If the main, alternative and
slot-tier laws give a choice its content factor times given factors, the
component's mass of the choice is the content factor times their slot
combination, up to at most the cube of the scale. -/
theorem slotTrembledChoice_near (initial : PMF (application setup leaks).State)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler) {scale : ℝ}
    (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (who : Player)
    (info : (application setup leaks).Info)
    (main alternative slot :
      PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info))
    (choice : (onePacketModel setup leaks bounds initial horizon scheduler).Choice who info)
    {content mainFactor alternativeFactor slotFactor : ℝ}
    (mainMass : (main choice).toReal = content * mainFactor)
    (alternativeMass : (alternative choice).toReal = content * alternativeFactor)
    (slotMass : (slot choice).toReal = content * slotFactor) :
    |(slotTrembledChoice setup leaks bounds initial horizon scheduler scale nonnegative le_one
        who info main alternative slot choice).toReal -
      content * slotCombination scale mainFactor alternativeFactor slotFactor| ≤ scale ^ 3 := by
  rw [slotTrembledChoice_apply_toReal, mainMass, alternativeMass, slotMass]
  set uniform := ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy initial horizon
    scheduler who info choice).toReal
  have uniformNonneg : 0 ≤ uniform := ENNReal.toReal_nonneg
  have uniformLe : uniform ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one _ _)
  have cube : 0 ≤ scale ^ 3 := pow_nonneg nonnegative 3
  have difference : scale ^ 3 * uniform + (1 - scale ^ 3) * (scale ^ 2 * (content * slotFactor) +
      (1 - scale ^ 2) * (scale * (content * alternativeFactor) +
        (1 - scale) * (content * mainFactor))) -
      content * slotCombination scale mainFactor alternativeFactor slotFactor =
      scale ^ 3 * uniform := by
    unfold slotCombination
    ring
  rw [difference, abs_of_nonneg (mul_nonneg cube uniformNonneg)]
  exact mul_le_of_le_one_right cube uniformLe

/-- **Operational steps from slot-trembled components.** Suppose that at every
regular response of another player, the responder's policy at its information
is a slot-trembled component whose main, alternative and slot-tier laws give
the realized choice its content factor times nonnegative factors; that their
slot combination is the response mass of the operational states before and
after; and that the cube of the scale is at most the error times the content
factor times that mass. Then the operational steps hold. -/
def OperationalSteps.ofSlotComponents
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {profiles : ℕ → ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
    {who : Player}
    (response : ℕ → Option (OperationalState setup leaks) →
      Option (OperationalState setup leaks) → ℝ)
    (error : ℕ → ℝ) (response_nonneg : ∀ n before after, 0 ≤ response n before after)
    (error_nonneg : ∀ n, 0 ≤ error n) (error_tendsto : Filter.Tendsto error Filter.atTop (nhds 0))
    (slotLaw : ∀ n {before after}
      (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before) joint legal
      (_ : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
        ⟨joint, legal⟩).support) (control next : (application setup leaks).Control)
      (actor : Player), before = some control → after = some next →
      control.actor = some actor → actor ≠ who →
      forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
        scheduler actor ((application setup leaks).observe actor (some control)) →
      ForcedState setup leaks who (some control) →
      0 < contentFactor setup leaks (sequence n) actor control.execution next.execution
        ((joint actor).getD ⟨none⟩) →
      ∃ (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
        (main alternative slot : PMF ((onePacketInformation setup leaks bounds horizon
          scheduler).Choice actor
            ((onePacketInformation setup leaks bounds horizon scheduler).infoOf actor prior)))
        (mainFactor alternativeFactor slotFactor : ℝ),
        profiles n actor ((onePacketInformation setup leaks bounds horizon scheduler).infoOf
            actor prior) =
          slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler scale
            nonnegative le_one actor _ main alternative slot ∧
        (main (InformationModel.choicesOfLegal _ prior ⟨joint, legal⟩ actor)).toReal =
          contentFactor setup leaks (sequence n) actor control.execution next.execution
            ((joint actor).getD ⟨none⟩) * mainFactor ∧
        (alternative (InformationModel.choicesOfLegal _ prior ⟨joint, legal⟩ actor)).toReal =
          contentFactor setup leaks (sequence n) actor control.execution next.execution
            ((joint actor).getD ⟨none⟩) * alternativeFactor ∧
        (slot (InformationModel.choicesOfLegal _ prior ⟨joint, legal⟩ actor)).toReal =
          contentFactor setup leaks (sequence n) actor control.execution next.execution
            ((joint actor).getD ⟨none⟩) * slotFactor ∧
        slotCombination scale mainFactor alternativeFactor slotFactor =
          response n (operationalState setup leaks before) (operationalState setup leaks after) ∧
        scale ^ 3 ≤ error n * (contentFactor setup leaks (sequence n) actor control.execution
            next.execution ((joint actor).getD ⟨none⟩) *
          response n (operationalState setup leaks before) (operationalState setup leaks after))) :
    OperationalSteps setup leaks bounds horizon scheduler sequence profiles who :=
  OperationalSteps.ofComponents response error response_nonneg error_nonneg error_tendsto
    fun n before after prior joint legal realized control next actor initialized reached acting
      other forced observerForced positive => by
    obtain ⟨scale, nonnegative, le_one, main, alternative, slot, mainFactor, alternativeFactor,
      slotFactor, policyEq, mainMass, alternativeMass, slotMass, combination, floor⟩ :=
      slotLaw n prior joint legal realized control next actor initialized reached acting other
        forced observerForced positive
    rw [response_stepProb (profiles n) prior joint legal realized control initialized acting,
      ← combination]
    have near := slotTrembledChoice_near setup leaks bounds (initialLaw setup) horizon scheduler
      nonnegative le_one actor _ main alternative slot
      (InformationModel.choicesOfLegal _ prior ⟨joint, legal⟩ actor) mainMass alternativeMass
      slotMass
    rw [← policyEq] at near
    rw [combination] at near ⊢
    exact near.trans floor

end Vegas
