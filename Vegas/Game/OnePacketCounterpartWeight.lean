/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCounterpartDomination
import GameTheoryExtensions.Protocol.StateSymmetry
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Upper source weights along an image history

Map a native history of the one-packet game step by step under a state
symmetry. If every step's upper source factor is at most `K` times the source
factor of its image, and the first irregular step's is at most `small` times
it, then the upper source weight of the history is at most `K` to its length
times the source weight of the image, and at most `small` times that when the
history is irregular (`Vegas.upperSourceWeight_le_mapTrace`).
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
  {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
  {profiles : ℕ → ∀ player,
    (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
  {who : Player} {steps : OperationalSteps setup leaks bounds horizon scheduler sequence
    profiles who}

private theorem othersSourceWeight_cast_start
    (assessment : setup.intendedModel.BehavioralAssessment)
    {state : (onePacketProtocol setup leaks bounds horizon scheduler).State}
    (same : (onePacketProtocol setup leaks bounds horizon scheduler).init = state) :
    othersSourceWeight setup leaks bounds horizon scheduler assessment who
      (same ▸ Trace.start : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state) =
      1 := by
  subst same
  rfl

/-- **Upper source weights along an image history.** -/
theorem upperSourceWeight_le_mapTrace
    (irregular : IrregularStepBound setup leaks bounds horizon scheduler steps) (n : ℕ)
    (symmetry : (onePacketProtocol setup leaks bounds horizon scheduler).StateSymmetry)
    {K small : ℝ} (one_le : 1 ≤ K) (smallNonneg : 0 ≤ small)
    {final : (onePacketProtocol setup leaks bounds horizon scheduler).State}
    (top : (onePacketProtocol setup leaks bounds horizon scheduler).Trace final)
    (every : ∀ {before after} (_ : (onePacketProtocol setup leaks bounds horizon
        scheduler).Trace before) joint
      (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal before joint)
      (_ : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
        ⟨joint, legal⟩).support), symmetry.Guard after →
      RegularStep setup leaks bounds horizon scheduler (sequence n) who (symmetry.map before)
        (symmetry.act before joint) (symmetry.map after) →
      upperSourceFactor irregular n before joint after ≤
        K * transitionSourceFactor setup leaks (sequence n) who (symmetry.map before)
          (symmetry.act before joint) (symmetry.map after))
    (first : ∀ {before after} (prior : (onePacketProtocol setup leaks bounds horizon
        scheduler).Trace before) joint
      (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal before joint)
      (realized : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
        ⟨joint, legal⟩).support),
      TracePrefix (prior.extend joint legal realized) top → symmetry.Guard after →
      RegularStep setup leaks bounds horizon scheduler (sequence n) who (symmetry.map before)
        (symmetry.act before joint) (symmetry.map after) →
      RegularTrace setup leaks bounds horizon scheduler (sequence n) who prior →
      ¬ RegularStep setup leaks bounds horizon scheduler (sequence n) who before joint after →
      upperSourceFactor irregular n before joint after ≤
        small * transitionSourceFactor setup leaks (sequence n) who (symmetry.map before)
          (symmetry.act before joint) (symmetry.map after)) :
    ∀ {state} (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
      (guarded : symmetry.Guard state),
      TracePrefix trace top →
      RegularTrace setup leaks bounds horizon scheduler (sequence n) who
        (symmetry.mapTrace trace guarded) →
      upperSourceWeight irregular n trace ≤
          K ^ trace.length * othersSourceWeight setup leaks bounds horizon scheduler (sequence n)
            who (symmetry.mapTrace trace guarded) ∧
        (¬ RegularTrace setup leaks bounds horizon scheduler (sequence n) who trace →
          upperSourceWeight irregular n trace ≤
            small * K ^ trace.length * othersSourceWeight setup leaks bounds horizon scheduler
              (sequence n) who (symmetry.mapTrace trace guarded))
  | _, .start, _, _, _ => by
      refine ⟨?_, fun irregularStart => (irregularStart trivial).elim⟩
      change (1 : ℝ) ≤ 1 * othersSourceWeight setup leaks bounds horizon scheduler (sequence n)
        who (symmetry.map_init.symm ▸ Trace.start)
      rw [othersSourceWeight_cast_start, one_mul]
  | _, .extend (source := before) (target := after) prior joint legal realized, guarded,
      isPrefix, imageRegular => by
      have priorPrefix : TracePrefix prior top :=
        (TracePrefix.extend .refl joint legal realized).trans isPrefix
      have priorGuard := symmetry.guard_source legal realized guarded
      rw [StateSymmetry.mapTrace_extend] at imageRegular
      obtain ⟨priorImageRegular, imageStep⟩ := imageRegular
      obtain ⟨priorBound, priorIrregular⟩ :=
        upperSourceWeight_le_mapTrace irregular n symmetry one_le smallNonneg top every first prior
          priorGuard priorPrefix priorImageRegular
      rw [StateSymmetry.mapTrace_extend]
      change upperSourceWeight irregular n prior *
            upperSourceFactor irregular n before joint after ≤
          K ^ (prior.length + 1) * (othersSourceWeight setup leaks bounds horizon scheduler
            (sequence n) who (symmetry.mapTrace prior priorGuard) *
          transitionSourceFactor setup leaks (sequence n) who (symmetry.map before)
            (symmetry.act before joint) (symmetry.map after)) ∧
        (¬ (RegularTrace setup leaks bounds horizon scheduler (sequence n) who prior ∧
            RegularStep setup leaks bounds horizon scheduler (sequence n) who before joint
              after) →
          upperSourceWeight irregular n prior * upperSourceFactor irregular n before joint after ≤
            small * K ^ (prior.length + 1) * (othersSourceWeight setup leaks bounds horizon
              scheduler (sequence n) who (symmetry.mapTrace prior priorGuard) *
            transitionSourceFactor setup leaks (sequence n) who (symmetry.map before)
              (symmetry.act before joint) (symmetry.map after)))
      have priorNonneg := upperSourceWeight_nonneg irregular n prior
      have factorNonneg := upperSourceFactor_nonneg irregular n before joint after
      have imageNonneg := othersSourceWeight_nonneg (sequence n) who
        (symmetry.mapTrace prior priorGuard)
      have stepNonneg := transitionSourceFactor_nonneg (setup := setup) (leaks := leaks)
        (sequence n) who (symmetry.map before) (symmetry.act before joint) (symmetry.map after)
      have powerNonneg : 0 ≤ K ^ prior.length := pow_nonneg (by linarith) _
      have stepBound := every prior joint legal realized guarded imageStep
      refine ⟨?_, fun irregularNow => ?_⟩
      · calc upperSourceWeight irregular n prior * upperSourceFactor irregular n before joint after
            ≤ (K ^ prior.length * othersSourceWeight setup leaks bounds horizon scheduler
                (sequence n) who (symmetry.mapTrace prior priorGuard)) *
              (K * transitionSourceFactor setup leaks (sequence n) who (symmetry.map before)
                (symmetry.act before joint) (symmetry.map after)) :=
              mul_le_mul priorBound stepBound factorNonneg (mul_nonneg powerNonneg imageNonneg)
          _ = _ := by ring
      · by_cases regularPrior : RegularTrace setup leaks bounds horizon scheduler (sequence n)
            who prior
        · have irregularStep : ¬ RegularStep setup leaks bounds horizon scheduler (sequence n)
              who before joint after := fun regularStep => irregularNow ⟨regularPrior, regularStep⟩
          have firstBound := first prior joint legal realized isPrefix guarded imageStep
            regularPrior irregularStep
          calc upperSourceWeight irregular n prior *
                upperSourceFactor irregular n before joint after
              ≤ (K ^ prior.length * othersSourceWeight setup leaks bounds horizon scheduler
                  (sequence n) who (symmetry.mapTrace prior priorGuard)) *
                (small * transitionSourceFactor setup leaks (sequence n) who
                  (symmetry.map before) (symmetry.act before joint) (symmetry.map after)) :=
                mul_le_mul priorBound firstBound factorNonneg
                  (mul_nonneg powerNonneg imageNonneg)
            _ ≤ (K ^ prior.length * othersSourceWeight setup leaks bounds horizon scheduler
                  (sequence n) who (symmetry.mapTrace prior priorGuard)) *
                (small * K * transitionSourceFactor setup leaks (sequence n) who
                  (symmetry.map before) (symmetry.act before joint) (symmetry.map after)) := by
                apply mul_le_mul_of_nonneg_left _ (mul_nonneg powerNonneg imageNonneg)
                apply mul_le_mul_of_nonneg_right _ stepNonneg
                nlinarith
            _ = _ := by ring
        · have priorSmall := priorIrregular regularPrior
          calc upperSourceWeight irregular n prior *
                upperSourceFactor irregular n before joint after
              ≤ (small * K ^ prior.length * othersSourceWeight setup leaks bounds horizon
                  scheduler (sequence n) who (symmetry.mapTrace prior priorGuard)) *
                (K * transitionSourceFactor setup leaks (sequence n) who (symmetry.map before)
                  (symmetry.act before joint) (symmetry.map after)) :=
                mul_le_mul priorSmall stepBound factorNonneg
                  (mul_nonneg (mul_nonneg smallNonneg powerNonneg) imageNonneg)
            _ = _ := by ring

end Vegas
