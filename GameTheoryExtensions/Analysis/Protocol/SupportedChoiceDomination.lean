/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.RestrictionDomination
import GameTheoryExtensions.Math.Probability.TotalVariation

/-! # Initialized domination from actual supported choices

A choice lower bound is needed only at histories supported by the reference
profile. The same one-step joint law and finite run induction give point-mass
domination and total-variation loss, while the target remains arbitrary after
leaving that support. These unconditional bounds make no posterior estimate.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability GameTheory.Protocol.ExecutionProtocol

variable {Player : Type*} [Fintype Player] {E : ExecutionProtocol Player}
  (M : InformationModel E)

private theorem bind_supported_domination {α : Type*}
    (source target : PMF α) (sourceStep targetStep : α → PMF α)
    (initialFactor stepFactor : ℝ) (initialNonnegative : 0 ≤ initialFactor)
    (initialLower : ∀ value, initialFactor * (source value).toReal ≤ (target value).toReal)
    (stepLower : ∀ prior ∈ source.support, ∀ value,
      stepFactor * (sourceStep prior value).toReal ≤ (targetStep prior value).toReal)
    (value : α) :
    (initialFactor * stepFactor) * ((source.bind sourceStep) value).toReal ≤
      ((target.bind targetStep) value).toReal := by
  rw [toReal_bind_apply, toReal_bind_apply]
  calc
    _ = initialFactor * expect source
        (fun prior => stepFactor * (sourceStep prior value).toReal) := by
      rw [expect_const_mul]
      ring
    _ ≤ initialFactor * expect source (fun prior => (targetStep prior value).toReal) :=
      mul_le_mul_of_nonneg_left (expect_mono
        (fun prior supported => stepLower prior supported value)
        (payoffIntegrable_of_bounded _ _ (C := |stepFactor|) fun prior => by
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          exact mul_le_of_le_one_right (abs_nonneg _) (pmf_toReal_apply_le_one _ _))
        (payoffIntegrable_toReal_apply source targetStep value)) initialNonnegative
    _ ≤ expect target (fun prior => (targetStep prior value).toReal) :=
      mul_expect_le_of_prob_le source target initialFactor initialLower _
        (fun _ => ENNReal.toReal_nonneg) (payoffIntegrable_toReal_apply target targetStep value)

private theorem withinTV_of_domination {α : Type*} (source target : PMF α)
    (factor : ℝ) (small : factor ≤ 1)
    (lower : ∀ value, factor * (source value).toReal ≤ (target value).toReal) :
    PMF.WithinTV (1 - factor) source target := by
  intro event
  have first := probOf_domination source target factor lower event
  have second := probOf_domination_excess source target factor lower event
  have atMostOne : (source.toOuterMeasure event).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using outerMeasure_le_one source event)
  have missing : (1 - factor) * (source.toOuterMeasure event).toReal ≤ 1 - factor :=
    mul_le_of_le_one_right (sub_nonneg.mpr small) atMostOne
  have scaled : factor * (source.toOuterMeasure event).toReal ≤
      (source.toOuterMeasure event).toReal :=
    mul_le_of_le_one_left ENNReal.toReal_nonneg small
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem runBehavioral_step_domination_of_choices
    (source target : ∀ who, M.BehavioralPolicy who)
    (factor : ℝ) (nonnegative : 0 ≤ factor)
    (history : E.History)
    (lower : ∀ who choice,
      factor * ((source who (M.infoOf who history.trace)) choice).toReal ≤
          ((target who (M.infoOf who history.trace)) choice).toReal)
    (next : E.History) :
    factor ^ Fintype.card Player *
        ((M.runBehavioralFrom source 1 history) next).toReal ≤
      ((M.runBehavioralFrom target 1 history) next).toReal := by
  rw [M.runBehavioralFrom_one_localStep, M.runBehavioralFrom_one_localStep]
  apply prob_bind_ge_mul _ _ _ _ (M.localStep history) next
  intro choices
  have lower := prob_pi_ge_prod_mul
    (fun who => source who (M.infoOf who history.trace))
    (fun who => target who (M.infoOf who history.trace))
    (fun _ => factor) (fun _ => nonnegative) lower choices
  simpa only [Finset.prod_const, Finset.card_univ] using lower

/-- Choice domination is required only at actual initialized source
histories. The target may use arbitrary policies after leaving that support. -/
theorem runBehavioral_domination_of_supported_choices
    (source target : ∀ who, M.BehavioralPolicy who)
    (factor : ℝ) (nonnegative : 0 ≤ factor)
    (lower : ∀ fuel history,
      history ∈ (M.runBehavioral source fuel).support → ∀ who choice,
      factor * ((source who (M.infoOf who history.trace)) choice).toReal ≤
          ((target who (M.infoOf who history.trace)) choice).toReal)
    (fuel : Nat)
    (next : E.History) :
    factor ^ (Fintype.card Player * fuel) *
        ((M.runBehavioral source fuel) next).toReal ≤
      ((M.runBehavioral target fuel) next).toReal := by
  let baseline := source
  let stepFactor := factor ^ Fintype.card Player
  have stepNonnegative : 0 ≤ stepFactor := pow_nonneg nonnegative _
  have retained (count : Nat) (last : E.History) :
      stepFactor ^ count * ((M.runBehavioral baseline count) last).toReal ≤
        ((M.runBehavioral target count) last).toReal := by
    induction count generalizing last with
    | zero => simp only [pow_zero, one_mul]; exact le_rfl
    | succ count ih =>
        unfold InformationModel.runBehavioral
        rw [M.runBehavioralFrom_add baseline count 1,
          M.runBehavioralFrom_add target count 1, pow_succ]
        apply bind_supported_domination _ _ _ _ (stepFactor ^ count) stepFactor
          (pow_nonneg stepNonnegative _) (fun last => ih last)
        intro history reached next
        exact runBehavioral_step_domination_of_choices M source target factor nonnegative
          history (lower count history reached) next
  simpa only [stepFactor, ← pow_mul] using retained fuel next

/-- The supported-choice bound controls every event of whole initialized
histories, including private recall and pending-message observations. -/
theorem runBehavioral_withinTV_of_supported_choices
    (source target : ∀ who, M.BehavioralPolicy who)
    (factor : ℝ) (nonnegative : 0 ≤ factor) (small : factor ≤ 1)
    (lower : ∀ fuel history,
      history ∈ (M.runBehavioral source fuel).support → ∀ who choice,
      factor * ((source who (M.infoOf who history.trace)) choice).toReal ≤
          ((target who (M.infoOf who history.trace)) choice).toReal)
    (fuel : Nat) :
    PMF.WithinTV (1 - factor ^ (Fintype.card Player * fuel))
      (M.runBehavioral source fuel)
      (M.runBehavioral target fuel) := by
  apply withinTV_of_domination _ _ _ (pow_le_one₀ nonnegative small)
  exact M.runBehavioral_domination_of_supported_choices source target factor
    nonnegative lower fuel

end GameTheory.Protocol.InformationModel
