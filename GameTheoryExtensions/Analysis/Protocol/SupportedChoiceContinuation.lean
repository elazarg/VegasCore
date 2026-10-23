/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.TotalVariation
import GameTheory.Analysis.Protocol.RestrictionDomination

/-! # Continuations under choices dominated along the reference play

From any starting history, if a target profile gives every choice at least a
fixed fraction of the probability a reference profile gives it, at every
history the reference continuation reaches, then each history of the target
continuation of a given length keeps that fraction to the power of the number
of players times the length (`runBehavioralFrom_domination_of_supported_choices`),
and the two continuations are within the missing mass in total variation
(`runBehavioralFrom_withinTV_of_supported_choices`). The missing mass is at
most the number of players times the length times the per-choice loss
(`GameTheory.Math.Probability.one_sub_pow_le_mul`).
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability GameTheory.Protocol.ExecutionProtocol

variable {Player : Type*} [Fintype Player] {E : ExecutionProtocol Player}
  (M : InformationModel E)

/-- One step of play keeps the product over players of the per-choice
fraction. -/
theorem runBehavioralFrom_one_domination_of_choices
    (source target : ∀ who, M.BehavioralPolicy who)
    (factor : ℝ) (nonnegative : 0 ≤ factor) (history : E.History)
    (lower : ∀ who choice,
      factor * ((source who (M.infoOf who history.trace)) choice).toReal ≤
          ((target who (M.infoOf who history.trace)) choice).toReal)
    (next : E.History) :
    factor ^ Fintype.card Player *
        ((M.runBehavioralFrom source 1 history) next).toReal ≤
      ((M.runBehavioralFrom target 1 history) next).toReal := by
  rw [runBehavioralFrom_one_localStep, runBehavioralFrom_one_localStep]
  apply prob_bind_ge_mul _ _ _ _ (M.localStep history) next
  intro choices
  have lower := prob_pi_ge_prod_mul
    (fun who => source who (M.infoOf who history.trace))
    (fun who => target who (M.infoOf who history.trace))
    (fun _ => factor) (fun _ => nonnegative) lower choices
  simpa only [Finset.prod_const, Finset.card_univ] using lower

/-- **Continuation domination from supported choices.** Choice domination is
required only at histories the reference continuation reaches from the start. -/
theorem runBehavioralFrom_domination_of_supported_choices
    (source target : ∀ who, M.BehavioralPolicy who)
    (factor : ℝ) (nonnegative : 0 ≤ factor) (start : E.History)
    (lower : ∀ fuel history,
      history ∈ (M.runBehavioralFrom source fuel start).support → ∀ who choice,
      factor * ((source who (M.infoOf who history.trace)) choice).toReal ≤
          ((target who (M.infoOf who history.trace)) choice).toReal)
    (fuel : Nat) (next : E.History) :
    factor ^ (Fintype.card Player * fuel) *
        ((M.runBehavioralFrom source fuel start) next).toReal ≤
      ((M.runBehavioralFrom target fuel start) next).toReal := by
  let stepFactor := factor ^ Fintype.card Player
  have stepNonnegative : 0 ≤ stepFactor := pow_nonneg nonnegative _
  have retained (count : Nat) (last : E.History) :
      stepFactor ^ count * ((M.runBehavioralFrom source count start) last).toReal ≤
        ((M.runBehavioralFrom target count start) last).toReal := by
    induction count generalizing last with
    | zero => simp only [pow_zero, one_mul]; exact le_rfl
    | succ count ih =>
        rw [M.runBehavioralFrom_add source count 1, M.runBehavioralFrom_add target count 1,
          pow_succ]
        apply bind_supported_domination _ _ _ _ (stepFactor ^ count) stepFactor
          (pow_nonneg stepNonnegative _) (fun last => ih last)
        intro history reached next
        exact M.runBehavioralFrom_one_domination_of_choices source target factor nonnegative
          history (lower count history reached) next
  simpa only [stepFactor, ← pow_mul] using retained fuel next

/-- **Continuations within the missing mass.** Under the hypotheses of
`runBehavioralFrom_domination_of_supported_choices`, with a fraction at most
one, the two continuations are within the missing mass in total variation. -/
theorem runBehavioralFrom_withinTV_of_supported_choices
    (source target : ∀ who, M.BehavioralPolicy who)
    (factor : ℝ) (nonnegative : 0 ≤ factor) (small : factor ≤ 1) (start : E.History)
    (lower : ∀ fuel history,
      history ∈ (M.runBehavioralFrom source fuel start).support → ∀ who choice,
      factor * ((source who (M.infoOf who history.trace)) choice).toReal ≤
          ((target who (M.infoOf who history.trace)) choice).toReal)
    (fuel : Nat) :
    PMF.WithinTV (1 - factor ^ (Fintype.card Player * fuel))
      (M.runBehavioralFrom source fuel start)
      (M.runBehavioralFrom target fuel start) := by
  apply PMF.WithinTV.of_domination _ _ _ (pow_le_one₀ nonnegative small)
  exact M.runBehavioralFrom_domination_of_supported_choices source target factor
    nonnegative start lower fuel

end GameTheory.Protocol.InformationModel

namespace GameTheory.Math.Probability

/-- The mass missing from a power of a fraction is at most the exponent times
the mass missing from the fraction. -/
theorem one_sub_pow_le_mul {factor : ℝ} (nonnegative : 0 ≤ factor) (count : ℕ) :
    1 - factor ^ count ≤ count * (1 - factor) := by
  have bernoulli := one_add_mul_le_pow (a := factor - 1) (by linarith) count
  rw [add_sub_cancel] at bernoulli
  linarith

end GameTheory.Math.Probability
