/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

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

The active-choice form replaces the player count by an actual bound on the
number of active players at reference-supported histories. In particular, at
most one mover gives exponent `fuel`, independently of the ambient player
count. A chance step has no active player and its exact one-step factor is one;
its transition law is still the protocol's stochastic kernel.
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
    (factor : Player → ℝ) (nonnegative : ∀ who, 0 ≤ factor who) (history : E.History)
    (lower : ∀ who choice,
      factor who * ((source who (M.infoOf who history.trace)) choice).toReal ≤
          ((target who (M.infoOf who history.trace)) choice).toReal)
    (next : E.History) :
    (∏ who, factor who) *
        ((M.runBehavioralFrom source 1 history) next).toReal ≤
      ((M.runBehavioralFrom target 1 history) next).toReal := by
  rw [runBehavioralFrom_one_localStep, runBehavioralFrom_one_localStep]
  apply prob_bind_ge_mul _ _ _ _ (M.localStep history) next
  intro choices
  exact prob_pi_ge_prod_mul
    (fun who => source who (M.infoOf who history.trace))
    (fun who => target who (M.infoOf who history.trace)) factor nonnegative lower choices

open Classical in
/-- Only active players pay a per-choice factor. Inactive legal menus are
singletons, so their two choice laws agree and contribute factor one. -/
theorem runBehavioralFrom_one_domination_of_active_choices
    (source target : ∀ who, M.BehavioralPolicy who)
    (factor : ℝ) (nonnegative : 0 ≤ factor) (history : E.History)
    (lower : ∀ who, E.active history.state who → ∀ choice,
      factor * ((source who (M.infoOf who history.trace)) choice).toReal ≤
        ((target who (M.infoOf who history.trace)) choice).toReal)
    (next : E.History) :
    factor ^ (Finset.univ.filter (E.active history.state)).card *
        ((M.runBehavioralFrom source 1 history) next).toReal ≤
      ((M.runBehavioralFrom target 1 history) next).toReal := by
  classical
  have bound := M.runBehavioralFrom_one_domination_of_choices source target
    (fun who => if E.active history.state who then factor else 1)
    (fun who => by split <;> positivity) history (by
      intro who choice
      by_cases active : E.active history.state who
      · simpa [active] using lower who active choice
      · rw [ite_eq_right active, one_mul,
          M.behavioral_eq_of_not_active (source who) (target who) history.trace active]) next
  simpa only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one] using bound

private theorem runBehavioralFrom_domination_of_supported_steps
    (source target : ∀ who, M.BehavioralPolicy who)
    (factor : ℝ) (nonnegative : 0 ≤ factor) (start : E.History)
    (lower : ∀ fuel history,
      history ∈ (M.runBehavioralFrom source fuel start).support → ∀ next,
      factor * ((M.runBehavioralFrom source 1 history) next).toReal ≤
        ((M.runBehavioralFrom target 1 history) next).toReal)
    (fuel : Nat) (next : E.History) :
    factor ^ fuel * ((M.runBehavioralFrom source fuel start) next).toReal ≤
      ((M.runBehavioralFrom target fuel start) next).toReal := by
  induction fuel generalizing next with
  | zero => simp only [pow_zero, one_mul]; exact le_rfl
  | succ fuel ih =>
      rw [M.runBehavioralFrom_add source fuel 1, M.runBehavioralFrom_add target fuel 1, pow_succ]
      apply bind_supported_domination _ _ _ _ (factor ^ fuel) factor
        (pow_nonneg nonnegative _) (fun last => ih last)
      exact lower fuel

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
  have bound := M.runBehavioralFrom_domination_of_supported_steps source target
    (factor ^ Fintype.card Player) (pow_nonneg nonnegative _) start (by
      intro count history reached next
      have bound := M.runBehavioralFrom_one_domination_of_choices source target
        (fun _ => factor) (fun _ => nonnegative) history (lower count history reached) next
      simpa only [Finset.prod_const, Finset.card_univ] using bound) fuel next
  simpa only [← pow_mul] using bound

open Classical in
/-- A reference-support bound on the number of active players controls the
continuation exponent. Choice domination is needed only for those players and
only at histories reached by the reference continuation. -/
theorem runBehavioralFrom_domination_of_supported_active_choices
    (source target : ∀ who, M.BehavioralPolicy who)
    (factor : ℝ) (nonnegative : 0 ≤ factor) (small : factor ≤ 1) (start : E.History)
    (activeBound : ℕ)
    (activeCount : ∀ fuel history,
      history ∈ (M.runBehavioralFrom source fuel start).support →
        (Finset.univ.filter (E.active history.state)).card ≤ activeBound)
    (lower : ∀ fuel history,
      history ∈ (M.runBehavioralFrom source fuel start).support →
      ∀ who, E.active history.state who → ∀ choice,
      factor * ((source who (M.infoOf who history.trace)) choice).toReal ≤
        ((target who (M.infoOf who history.trace)) choice).toReal)
    (fuel : Nat) (next : E.History) :
    factor ^ (activeBound * fuel) *
        ((M.runBehavioralFrom source fuel start) next).toReal ≤
      ((M.runBehavioralFrom target fuel start) next).toReal := by
  classical
  have bound := M.runBehavioralFrom_domination_of_supported_steps source target
    (factor ^ activeBound) (pow_nonneg nonnegative _) start (by
      intro count history reached next
      exact (mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one nonnegative small (activeCount count history reached))
        ENNReal.toReal_nonneg).trans
          (M.runBehavioralFrom_one_domination_of_active_choices source target factor nonnegative
            history (lower count history reached) next)) fuel next
  simpa only [← pow_mul] using bound

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

open Classical in
/-- With a fixed active-player bound on reference-supported histories,
the continuation loses at most `1 - factor ^ (activeBound * fuel)` in TV. -/
theorem runBehavioralFrom_withinTV_of_supported_active_choices
    (source target : ∀ who, M.BehavioralPolicy who)
    (factor : ℝ) (nonnegative : 0 ≤ factor) (small : factor ≤ 1) (start : E.History)
    (activeBound : ℕ)
    (activeCount : ∀ fuel history,
      history ∈ (M.runBehavioralFrom source fuel start).support →
        (Finset.univ.filter (E.active history.state)).card ≤ activeBound)
    (lower : ∀ fuel history,
      history ∈ (M.runBehavioralFrom source fuel start).support →
      ∀ who, E.active history.state who → ∀ choice,
      factor * ((source who (M.infoOf who history.trace)) choice).toReal ≤
        ((target who (M.infoOf who history.trace)) choice).toReal)
    (fuel : Nat) :
    PMF.WithinTV (1 - factor ^ (activeBound * fuel))
      (M.runBehavioralFrom source fuel start) (M.runBehavioralFrom target fuel start) := by
  apply PMF.WithinTV.of_domination _ _ _ (pow_le_one₀ nonnegative small)
  exact M.runBehavioralFrom_domination_of_supported_active_choices source target factor
    nonnegative small start activeBound activeCount lower fuel

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
