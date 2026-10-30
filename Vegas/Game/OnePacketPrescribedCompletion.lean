/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketFirstActivationCompletion
import Vegas.Game.SourceDebtObservation
import Vegas.Game.OnePacketSourceTurn

/-! # Trembled expectations, behavioral steps and canonical transmissions

**Trembles move an expectation by the scale.** A slot-trembled mixture whose
main law has expectation target of a function bounded by bound has
expectation within six times the scale times bound of target
(`Vegas.abs_expect_slotTrembledChoice_sub_le`).

**The behavioral step at an actor's point** draws the actor's choice and steps
with it (`Vegas.SourceProgram.ProtocolState.behavioralStateStep_eq_bind_of_actor`),
so at a turn the source step of the as-if-honest law of an intended assessment
is the step of its intended effective opening
(`Vegas.asIfHonest_bind_step_eq_behavioralStateStep`).

**Canonical decisions at a binding transmit.** Along every history of the
one-packet game, the canonical decision of every encoded source action at a
binding of the player transmits (`Vegas.canonicalTransmitsAt_of_binding`).
-/

noncomputable section



namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
/-- A mixture of two values bounded by left and right is bounded by the
weight times left plus right. -/
private theorem abs_mix_le {weight first second left right : ℝ} (nonnegative : 0 ≤ weight)
    (le_one : weight ≤ 1) (firstBound : |first| ≤ left) (secondBound : |second| ≤ right) :
    |weight * first + (1 - weight) * second| ≤ weight * left + right := by
  have rest : 0 ≤ 1 - weight := by linarith
  have rightNonneg : 0 ≤ right := (abs_nonneg _).trans secondBound
  calc |weight * first + (1 - weight) * second|
      ≤ |weight * first| + |(1 - weight) * second| := abs_add_le _ _
    _ = weight * |first| + (1 - weight) * |second| := by
        rw [abs_mul, abs_mul, abs_of_nonneg nonnegative, abs_of_nonneg rest]
    _ ≤ weight * left + (1 - weight) * right := by
        gcongr
    _ ≤ weight * left + right := by nlinarith

/-- **Trembles move an expectation by the scale.** If the main law of a
slot-trembled mixture gives a function bounded by bound the expectation
target, with target bounded by bound, the mixture gives it an expectation
within six times the scale times bound of target. -/
theorem abs_expect_slotTrembledChoice_sub_le {scale : ℝ} (nonnegative : 0 ≤ scale)
    (le_one : scale ≤ 1) (who : Player) (info : (application setup runtime leaks).Info)
    (main alternative slot :
      PMF ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler).Choice
        who
        info))
    (value : (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).Choice who
      info → ℝ) {target bound : ℝ} (bounded : ∀ choice, |value choice| ≤ bound)
    (targetBounded : |target| ≤ bound) (mainEq : expect main value = target) :
    |expect (slotTrembledChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler
      scale
        nonnegative le_one who info main alternative slot) value - target| ≤
      6 * scale * bound := by
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans targetBounded
  have gap : ∀ law : PMF ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).Choice who info), |expect law value - target| ≤ 2 * bound := by
    intro law
    have inside := abs_le.mp (expect_abs_le_of_bounded (μ := law) boundNonneg bounded)
    have targetInside := abs_le.mp targetBounded
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  unfold slotTrembledChoice
  rw [expect_mix_of_finite, expect_mix_of_finite, expect_mix_of_finite, mainEq]
  have cube : scale ^ 3 ≤ scale := pow_le_of_le_one nonnegative le_one (by norm_num)
  have square : scale ^ 2 ≤ scale := pow_le_of_le_one nonnegative le_one (by norm_num)
  have innermost : |scale * (expect alternative value - target) +
      (1 - scale) * (target - target)| ≤ scale * (2 * bound) + 0 :=
    abs_mix_le nonnegative le_one (gap alternative) (by rw [sub_self, abs_zero])
  have middle := abs_mix_le (sq_nonneg scale) (pow_le_one₀ nonnegative le_one) (gap slot)
    innermost
  have outer := abs_mix_le (pow_nonneg nonnegative 3) (pow_le_one₀ nonnegative le_one)
    (gap ((bounds.onePacketMenu runtime leaks).uniformPolicy (initialLaw setup) horizon
      scheduler who info)) middle
  have regroup : scale ^ 3 * expect ((bounds.onePacketMenu runtime leaks).uniformPolicy
        (initialLaw setup) horizon scheduler who info) value +
      (1 - scale ^ 3) * (scale ^ 2 * expect slot value +
        (1 - scale ^ 2) * (scale * expect alternative value + (1 - scale) * target)) - target =
      scale ^ 3 * (expect ((bounds.onePacketMenu runtime leaks).uniformPolicy
        (initialLaw setup) horizon scheduler who info) value - target) +
      (1 - scale ^ 3) * (scale ^ 2 * (expect slot value - target) +
        (1 - scale ^ 2) * (scale * (expect alternative value - target) +
          (1 - scale) * (target - target))) := by ring
  rw [regroup]
  refine outer.trans ?_
  nlinarith [mul_le_mul_of_nonneg_right cube boundNonneg,
    mul_le_mul_of_nonneg_right square boundNonneg]

/-- **Canonical decisions at a binding transmit.** Along every history of the
one-packet game, at a binding of who, the canonical decision of every encoded
source action transmits. -/
theorem canonicalTransmitsAt_of_binding {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId) {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) :
    CanonicalTransmitsAt setup runtime leaks who (control.execution.recall who)
      (control.execution.observe (application setup runtime leaks) who) event := by
  intro action graphAction _ _ _
  obtain ⟨serial, selected⟩ := onePacket_canonicalFreshSlot_exists (runtime := runtime) trace who
  obtain ⟨choice, rfl⟩ : ∃ choice : PublicationResult (L.Val payload),
      graphAction = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :=
    ⟨cast (congrArg EventGraph.EventField.Action outputEq) graphAction, by simp⟩
  rw [runtime.canonicalServiceDecision_binding leaks who _ _ event payload outputEq
    codeEq node serial selected choice]
  exact Option.some_ne_none _

end Vegas
