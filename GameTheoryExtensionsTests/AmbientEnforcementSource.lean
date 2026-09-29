/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensionsTests.AmbientEnforcementInformation
import GameTheory.Analysis.Protocol.Examples
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Sequential equilibria of the ordinary guessing game

Bob always guesses a fair private bit held by Alice. The source has no ambient
disclosure action. At Bob's sole information set every guessing policy earns
one half. Every source profile therefore has a sequentially consistent,
sequentially rational assessment. This includes every randomized guess, not
only the fair policy used in the enforcement comparison.
-/

noncomputable section

namespace GameTheoryExtensionsTests.AmbientEnforcement

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter
open GameTheory.Protocol.ExecutionProtocol GameTheory.Analysis.Protocol.Examples

def sourceAssessment (profile : Profile (model false).behavioralSignature) :
    (model false).BehavioralAssessment where
  strategy := profile
  belief who site := by
    cases who
    · exact (source_no_alice_site site).elim
    · exact (PMF.uniformOfFintype Bool).map fun bit =>
        ⟨bobHistory false bit false, by rw [source_bob_site_eq site]; rfl⟩

theorem source_reach_bob (profile : Profile (model false).behavioralSignature) (bit : Bool) :
    (model false).historyReachWeight profile (bobHistory false bit false) = 2⁻¹ := by
  classical
  change ((model false).runBehavioralFrom profile 2 (arena false).initHistory)
    (bobHistory false bit false) = _
  rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
    (model false) (single false),
    ← pmf_map_apply_of_injective _ (state_injective false), run_states]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    PMF.pure_bind, initHistory, kernel, PMF.bind_map, Function.comp_def, Bool.false_and]
  have constant (x : Bool) (law : PMF Bool) :
      law.map (fun _ => State.bob x false) = PMF.pure (State.bob x false) :=
    PMF.map_const law _
  simp only [constant]
  rw [show (fun x => PMF.pure (State.bob x false)) =
      PMF.pure ∘ (fun x => State.bob x false) from rfl, PMF.bind_pure_comp]
  change ((PMF.uniformOfFintype Bool).map (fun x => State.bob x false))
    ((fun x => State.bob x false) bit) = _
  rw [pmf_map_apply_of_injective _ (fun _ _ same => (State.bob.inj same).1),
    PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat]

def sourceProfile (guesses : PMF Bool) : Profile (model false).behavioralSignature
  | false => choose false false false
  | true => fun info => guesses.bind fun guess => choose false true guess info

theorem source_profile_guess (guesses : PMF Bool) :
    choiceLaw (sourceProfile guesses) true (some none) = guesses := by
  simp [choiceLaw, sourceProfile, choose, decisionInfo, ← PMF.bind_pure_comp, Function.comp_def]

theorem source_initialized_law (profile : Profile (model false).behavioralSignature) :
    (((model false).runSingleMoverBehavioralFrom (single false) profile 3
      (arena false).initHistory).map History.state).map retained =
      (bindPairLaw (PMF.uniformOfFintype Bool)
        (fun _ => (choiceLaw profile true (some none)))).map some := by
  rw [run_initial]
  simp [Bool.false_and, resultLaw, retained,
    bindPairLaw, ← PMF.bind_pure_comp, Function.comp_def]

theorem source_mass_bob (profile : Profile (model false).behavioralSignature) :
    (model false).informationMass profile true (bobSilentSite false) = 1 := by
  unfold InformationModel.informationMass
  rw [← (silentHistories false).tsum_eq, tsum_fintype]
  change (∑ bit : Bool, (model false).historyReachWeight profile (bobHistory false bit false)) = _
  simp only [source_reach_bob, Fintype.sum_bool, ENNReal.inv_two_add_inv_two]

theorem source_belief_bob (profile : Profile (model false).behavioralSignature)
    (bit : Bool) :
    (sourceAssessment profile).belief true (bobSilentSite false) (silentHistory false bit) =
      2⁻¹ := by
  classical
  change ((PMF.uniformOfFintype Bool).map (silentHistory false)) (silentHistory false bit) = _
  rw [pmf_map_apply_of_injective _ (silentHistory_injective false),
    PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat]

theorem source_bayes (profile : Profile (model false).behavioralSignature) :
    InformationModel.BehavioralAssessment.IsBayesConsistent (model false)
      (sourceAssessment profile) (antichain false) := by
  intro who site _ history
  cases who
  · exact (source_no_alice_site site).elim
  · have same := source_bob_site_eq site
    subst site
    obtain ⟨bit, same⟩ := history_at_silent false history
    have historyEq : history = silentHistory false bit := Subtype.ext same
    subst history
    change (sourceAssessment profile).belief true (bobSilentSite false) (silentHistory false bit) =
      (model false).historyReachWeight profile (bobHistory false bit false) /
        (model false).informationMass profile true (bobSilentSite false)
    rw [source_belief_bob, source_reach_bob, source_mass_bob, div_one]

def sourceReference : (model false).BehavioralAssessment :=
  sourceAssessment fun who info =>
    mix (1 / 2) (by norm_num) (by norm_num)
      (choose false who false info) (choose false who true info)

theorem sourceReference_fullyMixed : sourceReference.IsFullyMixed := by
  intro who site choice
  cases who
  · exact (source_no_alice_site site).elim
  · have same := source_bob_site_eq site
    subst site
    rcases choice with ⟨value, legal⟩
    change (⟨value, legal⟩ : (model false).Choice true (some none)) ∈
      (mix (1 / 2) (by norm_num) (by norm_num)
        (choose false true false (some none)) (choose false true true (some none))).support
    change value.isSome = true at legal
    cases value with
    | none => cases legal
    | some value =>
        cases value
        · exact mem_support_mix_left _ _ _ (by norm_num) (by simp [choose, decisionInfo])
        · exact mem_support_mix_right _ _ _ (by norm_num) (by simp [choose, decisionInfo])

theorem source_consistent (profile : Profile (model false).behavioralSignature) :
    (sourceAssessment profile).IsSequentiallyConsistent (antichain false) := by
  let sequence (n : Nat) := sourceAssessment
    (sourceReference.perturb profile (trembleWeight n)
      (trembleWeight_nonneg n) (trembleWeight_le_one n)).strategy
  refine ⟨sequence, fun n => ⟨?_, source_bayes _⟩, ?_⟩
  · exact sourceReference.perturb_fullyMixed sourceReference_fullyMixed profile (trembleWeight n)
      (trembleWeight_nonneg n) (trembleWeight_le_one n) (trembleWeight_pos n)
  · constructor
    · intro who site
      exact sourceReference.perturb_strategy_converges profile trembleWeight trembleWeight_nonneg
        trembleWeight_le_one trembleWeight_tendsto_zero who site.1
    · intro who site
      exact pmfConvergesPointwise_const _

/-- A uniform silent posterior makes every whole guessing continuation worth
one half, in either game and for any deposit charged to Alice. -/
theorem uniform_silent_context_value (ambient : Bool)
    (assessment : (model ambient).BehavioralAssessment)
    (uniform : assessment.belief true (bobSilentSite ambient) =
      (PMF.uniformOfFintype Bool).map (silentHistory ambient))
    (deposit : ℝ) (alternative : (model ambient).BehavioralPolicy true) :
    (assessment.continuationContext (bobSilentSite ambient)
      (fun history => payoff deposit history.state true) 3).value alternative = 1 / 2 := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value, uniform]
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _), expect_map]
  simp_rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
    (model ambient) (single ambient)]
  change expect (PMF.uniformOfFintype Bool) (fun bit =>
    expect ((model ambient).runSingleMoverBehavioralFrom (single ambient)
      (Profile.update (sig := (model ambient).behavioralSignature)
        assessment.strategy true alternative)
        3 (bobHistory ambient bit false))
          (fun history => payoff deposit history.state true)) = _
  simp_rw [value_bob (ambient := ambient) _ _ _ (payoff deposit · true)]
  simp only [resultLaw, Bool.and_false, Bool.false_eq_true, ite_false, expect_map,
    Function.comp_def, payoff, Bool.not_true, sub_zero]
  rw [expect_comm_of_support_finite _ _ (Set.toFinite _) (Set.toFinite _)]
  have fair (guess : Bool) : expect (PMF.uniformOfFintype Bool)
      (fun bit => if guess = bit then (1 : ℝ) else 0) = 1 / 2 := by
    cases guess <;>
      norm_num [expect_eq_sum, Fintype.sum_bool, toReal_uniformOfFintype_apply]
  simp_rw [fair]
  exact expect_constant _ _

theorem source_context_value (profile : Profile (model false).behavioralSignature)
    (site : (model false).InformationSite true)
    (alternative : (model false).BehavioralPolicy true) :
    ((sourceAssessment profile).continuationContext site
      (fun history => payoff 0 history.state true) 3).value alternative = 1 / 2 := by
  rw [source_bob_site_eq site]
  exact uniform_silent_context_value false (sourceAssessment profile) rfl 0 alternative

theorem source_rational (profile : Profile (model false).behavioralSignature) :
    (sourceAssessment profile).IsSequentiallyRationalWithin
      (fun who history => payoff 0 history.state who) 3 := by
  intro who site
  cases who
  · exact (source_no_alice_site site).elim
  · refine (Context.isLocallyOptimal_iff_of_integrable (payoffIntegrable_of_finite _ _)
      fun _ _ => payoffIntegrable_of_finite _ _).mpr fun alternative _ => ?_
    rw [source_context_value, source_context_value]

/-- Every source policy profile has an explicit standard sequential equilibrium
assessment. The common fully mixed approximants retain the same uniform beliefs. -/
theorem source_sequential_equilibrium (profile : Profile (model false).behavioralSignature) :
    (sourceAssessment profile).IsSequentialEquilibriumFor (antichain false)
      (fun who site => (sourceAssessment profile).continuationContext site
        (fun history => payoff 0 history.state who) 3) :=
  ⟨source_rational profile, source_consistent profile⟩

end GameTheoryExtensionsTests.AmbientEnforcement
