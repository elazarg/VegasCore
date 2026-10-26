/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCounterpartDomination
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Source-weight comparison along paired actual histories

Directed repairs need not be state symmetries. Two actual histories with the
same number of steps can instead be compared through their paired prefixes.
A small factor at the first irregular step persists through the whole product.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}
  {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
  {profiles : ℕ → ∀ player,
    (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player}
  {who : Player} {steps : OperationalSteps setup runtime leaks bounds horizon scheduler sequence
    profiles who}

/-- Paired prefix bounds compare actual source weights without assuming an
invertible state map. A small factor is needed only at the first irregular
transition of the original history. -/
theorem upperSourceWeight_le_of_paired_steps
    (irregular : IrregularStepBound setup runtime leaks bounds horizon scheduler steps) (n : ℕ)
    {K small : ℝ} (one_le : 1 ≤ K) (smallNonneg : 0 ≤ small)
    {final imageFinal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).State}
    (top : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace final)
    (imageTop : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace imageFinal)
    (sameLength : top.length = imageTop.length)
    (every : ∀ {before after imageBefore imageAfter}
      (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace before) joint
      (legal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal before joint)
      (realized : after ∈ ((onePacketProtocol setup runtime leaks bounds horizon scheduler).step
        before
        ⟨joint, legal⟩).support)
      (imagePrior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace
        imageBefore)
      imageJoint
      (imageLegal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal
        imageBefore
        imageJoint)
      (imageRealized : imageAfter ∈ ((onePacketProtocol setup runtime leaks bounds horizon
        scheduler).step
        imageBefore ⟨imageJoint, imageLegal⟩).support),
      TracePrefix (prior.extend joint legal realized) top →
      TracePrefix (imagePrior.extend imageJoint imageLegal imageRealized) imageTop →
      prior.length = imagePrior.length →
      upperSourceFactor (runtime := runtime) irregular n before joint after ≤
        K * transitionSourceFactor setup runtime leaks (sequence n) who imageBefore imageJoint
          imageAfter)
    (first : ∀ {before after imageBefore imageAfter}
      (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace before) joint
      (legal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal before joint)
      (realized : after ∈ ((onePacketProtocol setup runtime leaks bounds horizon scheduler).step
        before
        ⟨joint, legal⟩).support)
      (imagePrior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace
        imageBefore)
      imageJoint
      (imageLegal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal
        imageBefore
        imageJoint)
      (imageRealized : imageAfter ∈ ((onePacketProtocol setup runtime leaks bounds horizon
        scheduler).step
        imageBefore ⟨imageJoint, imageLegal⟩).support),
      TracePrefix (prior.extend joint legal realized) top →
      TracePrefix (imagePrior.extend imageJoint imageLegal imageRealized) imageTop →
      prior.length = imagePrior.length →
      RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who prior →
      ¬ RegularStep setup runtime leaks bounds horizon scheduler (sequence n) who before joint
        after →
      upperSourceFactor (runtime := runtime) irregular n before joint after ≤
        small * transitionSourceFactor setup runtime leaks (sequence n) who imageBefore imageJoint
          imageAfter) :
    upperSourceWeight (runtime := runtime) irregular n top ≤
        K ^ top.length * othersSourceWeight setup runtime leaks bounds horizon scheduler (sequence
          n)
          who imageTop ∧
      (¬ RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who top →
        upperSourceWeight (runtime := runtime) irregular n top ≤ small * K ^ top.length *
          othersSourceWeight setup runtime leaks bounds horizon scheduler (sequence n) who
            imageTop) := by
  have carry : ∀ {state imageState}
      (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state)
      (image : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace imageState),
      TracePrefix trace top → TracePrefix image imageTop → trace.length = image.length →
      upperSourceWeight (runtime := runtime) irregular n trace ≤ K ^ trace.length *
          othersSourceWeight setup runtime leaks bounds horizon scheduler (sequence n) who image ∧
        (¬ RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who trace →
          upperSourceWeight (runtime := runtime) irregular n trace ≤ small * K ^ trace.length *
            othersSourceWeight setup runtime leaks bounds horizon scheduler (sequence n) who
              image) := by
    intro state imageState trace
    induction trace generalizing imageState with
    | start =>
        intro image isPrefix imagePrefix lengths
        cases image with
        | start => exact ⟨by simp [upperSourceWeight, othersSourceWeight, Trace.length],
            fun impossible => (impossible trivial).elim⟩
        | extend imagePrior _ _ _ =>
            change 0 = imagePrior.length + 1 at lengths
            omega
    | @extend before after prior joint legal realized ih =>
        intro image isPrefix imagePrefix lengths
        cases image with
        | start =>
            change prior.length + 1 = 0 at lengths
            omega
        | @extend imageBefore _ imagePrior imageJoint imageLegal imageRealized =>
            have priorLengths : prior.length = imagePrior.length := Nat.succ.inj lengths
            have priorPrefix : TracePrefix prior top :=
              (TracePrefix.extend .refl joint legal realized).trans isPrefix
            have priorImagePrefix : TracePrefix imagePrior imageTop :=
              (TracePrefix.extend .refl imageJoint imageLegal imageRealized).trans imagePrefix
            obtain ⟨priorBound, priorIrregular⟩ :=
              ih imagePrior priorPrefix priorImagePrefix priorLengths
            have priorNonneg := upperSourceWeight_nonneg (runtime := runtime) irregular n prior
            have factorNonneg := upperSourceFactor_nonneg (runtime := runtime) irregular n before
              joint after
            have imageNonneg := othersSourceWeight_nonneg (runtime := runtime) (sequence n) who
              imagePrior
            have stepNonneg := transitionSourceFactor_nonneg (runtime := runtime) (setup := setup)
              (leaks := leaks)
              (sequence n) who imageBefore imageJoint imageState
            have powerNonneg : 0 ≤ K ^ prior.length := pow_nonneg (by linarith) _
            have stepBound := every prior joint legal realized imagePrior imageJoint imageLegal
              imageRealized isPrefix imagePrefix priorLengths
            change upperSourceWeight (runtime := runtime) irregular n prior *
                  upperSourceFactor (runtime := runtime) irregular n before joint after ≤
                K ^ (prior.length + 1) * (othersSourceWeight setup runtime leaks bounds horizon
                  scheduler
                  (sequence n) who imagePrior * transitionSourceFactor setup runtime leaks
                    (sequence n)
                    who imageBefore imageJoint imageState) ∧
              (¬ (RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who prior ∧
                  RegularStep setup runtime leaks bounds horizon scheduler (sequence n) who before
                    joint
                    after) → upperSourceWeight (runtime := runtime) irregular n prior *
                  upperSourceFactor (runtime := runtime) irregular n before joint after ≤
                small * K ^ (prior.length + 1) *
                  (othersSourceWeight setup runtime leaks bounds horizon scheduler (sequence n) who
                    imagePrior * transitionSourceFactor setup runtime leaks (sequence n) who
                      imageBefore
                      imageJoint imageState))
            refine ⟨?_, fun irregularNow => ?_⟩
            · calc _ ≤ (K ^ prior.length * othersSourceWeight setup runtime leaks bounds horizon
                scheduler
                    (sequence n) who imagePrior) * (K * transitionSourceFactor setup runtime leaks
                      (sequence n) who imageBefore imageJoint imageState) :=
                  mul_le_mul priorBound stepBound factorNonneg
                    (mul_nonneg powerNonneg imageNonneg)
                _ = _ := by ring
            · by_cases regularPrior : RegularTrace setup runtime leaks bounds horizon scheduler
                  (sequence n) who prior
              · have irregularStep : ¬ RegularStep setup runtime leaks bounds horizon scheduler
                    (sequence n) who before joint after :=
                  fun regularStep => irregularNow ⟨regularPrior, regularStep⟩
                have firstBound := first prior joint legal realized imagePrior imageJoint
                  imageLegal imageRealized isPrefix imagePrefix priorLengths regularPrior
                  irregularStep
                have weakened := (mul_le_mul_of_nonneg_left one_le smallNonneg)
                have firstScaled : small * transitionSourceFactor setup runtime leaks (sequence n)
                  who
                    imageBefore imageJoint imageState ≤ small * K *
                      transitionSourceFactor setup runtime leaks (sequence n) who imageBefore
                        imageJoint
                        imageState := by
                  simpa only [mul_one] using mul_le_mul_of_nonneg_right weakened stepNonneg
                calc _ ≤ (K ^ prior.length * othersSourceWeight setup runtime leaks bounds horizon
                        scheduler (sequence n) who imagePrior) * (small * K *
                          transitionSourceFactor setup runtime leaks (sequence n) who imageBefore
                            imageJoint imageState) :=
                      mul_le_mul priorBound (firstBound.trans firstScaled) factorNonneg
                        (mul_nonneg powerNonneg imageNonneg)
                    _ = _ := by ring
              · calc _ ≤ (small * K ^ prior.length * othersSourceWeight setup runtime leaks bounds
                      horizon scheduler (sequence n) who imagePrior) *
                        (K * transitionSourceFactor setup runtime leaks (sequence n) who imageBefore
                          imageJoint imageState) :=
                    mul_le_mul (priorIrregular regularPrior) stepBound factorNonneg
                      (mul_nonneg (mul_nonneg smallNonneg powerNonneg) imageNonneg)
                  _ = _ := by ring
  exact carry top imageTop .refl .refl sameLength

end Vegas
