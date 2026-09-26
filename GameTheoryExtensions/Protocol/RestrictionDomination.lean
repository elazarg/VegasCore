/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Protocol.RestrictionProfile
import GameTheoryExtensions.Math.Probability.ProductDomination
import GameTheoryExtensions.Math.Probability.KernelDomination

/-! # Actual execution retains almost all source mass under rare trembles

Pinned target decisions mix the corresponding source choice law with a small
full-support reference law. Their independent product retains a common source
fraction. The structural one-step square and kernel iteration propagate this
bound to complete history distributions; new-site policies are unrestricted.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type} [Fintype Player] {E T : ExecutionProtocol Player}
  {M : InformationModel E} {N : InformationModel T}

theorem runBehavioralFrom_one_localStep (profile : ∀ who, M.BehavioralPolicy who)
    (history : E.History) :
    M.runBehavioralFrom profile 1 history =
      (FinDist.pi fun who => profile who (M.infoOf who history.trace)).bind
        (M.localStep history) := by
  rw [M.runBehavioralFrom_succ_localStep profile 0]
  exact FinDist.bind_pure _

theorem runBehavioralFrom_eq_iterate (profile : ∀ who, M.BehavioralPolicy who)
    (fuel : Nat) (history : E.History) :
    M.runBehavioralFrom profile fuel history =
      (fun law => law.bind (M.runBehavioralFrom profile 1))^[fuel] (FinDist.pure history) := by
  induction fuel with
  | zero => rfl
  | succ fuel induction =>
      rw [M.runBehavioralFrom_add profile fuel 1 history, induction,
        Function.iterate_succ_apply']

namespace ActionRestriction

variable (restriction : M.ActionRestriction N)

theorem perturbed_step_domination
    (source : ∀ who, M.BehavioralPolicy who)
    (reference target : ∀ who, N.BehavioralPolicy who)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (perturbs : restriction.PerturbsProfile source reference target epsilon nonnegative small)
    (original : E.History) (next : T.History) :
    (1 - epsilon) ^ Fintype.card Player *
        ((M.runBehavioralFrom source 1 original).map restriction.history).prob next ≤
      (N.runBehavioralFrom target 1 (restriction.history original)).prob next := by
  classical
  by_cases stopped : E.terminal original.state
  · rw [M.runBehavioralFrom_of_terminal source _ stopped,
      N.runBehavioralFrom_of_terminal target _ ((restriction.terminal original).mpr stopped),
      FinDist.map_pure]
    have factor : (1 - epsilon) ^ Fintype.card Player ≤ 1 :=
      pow_le_one₀ (sub_nonneg.mpr small) (by linarith)
    exact mul_le_of_le_one_left (FinDist.prob_nonneg _ _) factor
  · let legal := restriction.extendProfile source reference
    have agrees := restriction.extendProfile_extends source reference
    rw [restriction.runFrom_law source legal agrees 1 original,
      runBehavioralFrom_one_localStep, runBehavioralFrom_one_localStep]
    have good := funext
      (restriction.extends_at_history source legal agrees original stopped)
    have bad := funext
      (restriction.perturbs_at_history source reference target epsilon nonnegative small
        perturbs original stopped)
    rw [good, bad]
    exact FinDist.prob_pi_mix_bind_lower _ _ epsilon nonnegative small
      (N.localStep (restriction.history original)) next

/-- Every target depth law dominates the embedded source law by the product
of the independent retained action probabilities. No restriction is imposed on
play after a departure, nor is a no-return-to-image premise needed. -/
theorem perturbed_run_domination [Finite T.History]
    (source : ∀ who, M.BehavioralPolicy who)
    (reference target : ∀ who, N.BehavioralPolicy who)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (perturbs : restriction.PerturbsProfile source reference target epsilon nonnegative small)
    (fuel : Nat) (next : T.History) :
    (1 - epsilon) ^ (Fintype.card Player * fuel) *
        ((M.runBehavioral source fuel).map restriction.history).prob next ≤
      (N.runBehavioral target fuel).prob next := by
  have bound := FinDist.iterate_prob_domination (FinDist.pure E.initHistory)
    restriction.history (M.runBehavioralFrom source 1) (N.runBehavioralFrom target 1)
    ((1 - epsilon) ^ Fintype.card Player) (pow_nonneg (sub_nonneg.mpr small) _)
    (restriction.perturbed_step_domination source reference target epsilon nonnegative small
      perturbs) fuel next
  simpa only [FinDist.map_pure, restriction.initial, ← runBehavioralFrom_eq_iterate,
    ← pow_mul, runBehavioral] using bound

end ActionRestriction

end GameTheory.Protocol.InformationModel
