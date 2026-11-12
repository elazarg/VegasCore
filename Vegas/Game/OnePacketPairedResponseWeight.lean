module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketRepairResponseBound

@[expose] public section

/-! # Irregular source factors under paired response likelihood bounds

Operational factorization turns a bound on two actual response probabilities
into a bound on their source factors. The operational mass cancels because the
paired transitions have the same operational endpoints.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}
  {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
  {profiles : ℕ → ∀ player,
    (onePacketInformation setup timeouts leaks bounds horizon scheduler).BehavioralPolicy player}
  {who : Player} {steps : OperationalSteps setup timeouts leaks bounds horizon scheduler sequence
    profiles who}

/-- The irregular response factor is its actual response probability divided
by operational mass. A likelihood ratio against a paired regular response
therefore bounds it by that response's source factor and factorization error. -/
theorem irregularSourceFactor_le_of_paired_response
    (positive : ∀ n {before after : (application setup timeouts leaks).ProtocolState}
      (_ : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace before) joint
        legal
      (_ : after ∈ ((onePacketProtocol setup timeouts leaks bounds horizon scheduler).step before
        ⟨joint, legal⟩).support) (control next : (application setup timeouts leaks).Control),
      before = some control → after = some next →
      ¬ RegularStep setup timeouts leaks bounds horizon scheduler (sequence n) who before joint
        after →
      0 < responseMass setup timeouts leaks bounds horizon scheduler (profiles n) control joint →
      0 < steps.mass n (operationalState setup timeouts leaks before)
        (operationalState setup timeouts leaks after))
    (n : ℕ) {control next imageControl imageNext : (application setup timeouts leaks).Control}
    (imagePrior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace
      (some imageControl))
    (joint imageJoint : Player → Option (application setup timeouts leaks).Action)
    (imageLegal : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Legal
      (some imageControl) imageJoint)
    (imageRealized : some imageNext ∈ ((onePacketProtocol setup timeouts leaks bounds horizon
      scheduler).step (some imageControl) ⟨imageJoint, imageLegal⟩).support)
    {actor : Player} (acting : imageControl.actor = some actor) (other : actor ≠ who)
    (irregular : ¬ RegularStep setup timeouts leaks bounds horizon scheduler (sequence n) who
      (some control) joint (some next))
    (imageRegular : RegularStep setup timeouts leaks bounds horizon scheduler (sequence n) who
      (some imageControl) imageJoint (some imageNext))
    (beforeEq : operationalState setup timeouts leaks (some imageControl) =
      operationalState setup timeouts leaks (some control))
    (afterEq : operationalState setup timeouts leaks (some imageNext) =
      operationalState setup timeouts leaks (some next))
    {ratio : ℝ} (ratioNonneg : 0 ≤ ratio)
    (likelihood : responseMass setup timeouts leaks bounds horizon scheduler (profiles n) control
      joint ≤
      ratio * responseMass setup timeouts leaks bounds horizon scheduler (profiles n) imageControl
        imageJoint) :
    upperSourceFactor (timeouts := timeouts) (IrregularStepBound.ofResponseMass (timeouts :=
      timeouts)
      steps positive) n (some control) joint
        (some next) ≤ ratio * (1 + steps.error n) *
      transitionSourceFactor setup timeouts leaks (sequence n) who (some imageControl) imageJoint
        (some imageNext) := by
  obtain ⟨⟨forcedActor, forcedWho⟩, contentPositive⟩ := imageRegular actor acting other
  have component := steps.component n imagePrior imageJoint imageLegal
    imageRealized imageControl
    imageNext actor rfl rfl acting other forcedActor forcedWho contentPositive
  rw [stepProb_eq_responseMass (timeouts := timeouts) (profiles n) imagePrior imageJoint imageLegal
    imageRealized
    imageControl rfl acting, beforeEq, afterEq] at component
  let content := contentFactor setup timeouts leaks (sequence n) actor imageControl.execution
    imageNext.execution ((imageJoint actor).getD ⟨none⟩)
  let mass := steps.mass n (operationalState setup timeouts leaks (some
    control))
    (operationalState setup timeouts leaks (some next))
  have imageUpper : responseMass setup timeouts leaks bounds horizon scheduler (profiles n)
    imageControl
      imageJoint ≤ (1 + steps.error n) * (content * mass) := by
    have upper := (abs_le.mp component).2
    change _ ≤ (1 + steps.error n) * (content * mass)
    dsimp only [content, mass]
    linarith
  have imageFactor : transitionSourceFactor setup timeouts leaks (sequence n) who (some
    imageControl)
      imageJoint (some imageNext) = content := by
    simp only [transitionSourceFactor, acting, other, ↓reduceIte]
    rfl
  rw [imageFactor]
  unfold upperSourceFactor
  simp only [irregular, ↓reduceIte]
  change responseMass setup timeouts leaks bounds horizon scheduler (profiles n) control joint /
    mass ≤ _
  have massNonneg : 0 ≤ mass := steps.mass_nonneg _ _ _
  rcases massNonneg.lt_or_eq with massPositive | zero
  · rw [div_le_iff₀ massPositive]
    calc _ ≤ ratio * ((1 + steps.error n) * (content * mass)) :=
        likelihood.trans (mul_le_mul_of_nonneg_left imageUpper ratioNonneg)
      _ = _ := by ring
  · rw [← zero, div_zero]
    exact mul_nonneg (mul_nonneg ratioNonneg (by linarith [steps.error_nonneg n]))
      contentPositive.le

end Vegas
