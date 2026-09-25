/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensionsTests.AmbientEnforcementAssessment
import GameTheoryExtensionsTests.AmbientEnforcementSource

/-! # Sequential implementation with a penalty on ambient communication

The guessing game remains unchanged. Alice's additional disclosure action is
deterred if its best reward, minus the automatic fine, is no better than her
type's prescribed silent reward. Bob's response after disclosure stays correct.
A fine of one implements every source profile; a fine of one half suffices for
fair guessing. The compiler is playerwise and preserves the joint bit/guess law.
-/

noncomputable section

namespace GameTheoryExtensionsTests.AmbientEnforcement

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

def correct (bit guess : Bool) : ℝ := if guess = bit then 1 else 0

theorem silent_branch_value (guesses : FinDist Bool) (deposit : ℝ) (bit disclose : Bool) :
    (resultLaw (silentProfile guesses) bit disclose).expect (payoff deposit · false) =
      if disclose then 1 - deposit else guesses.expect (correct bit) := by
  unfold correct
  cases disclose <;>
    simp [resultLaw, choiceLaw, silentProfile, bobRespond, choose, decisionInfo,
      FinDist.expect_map, payoff]

theorem disclosed_bob_value (guesses : FinDist Bool) (deposit : ℝ) (bit : Bool) :
    (resultLaw (silentProfile guesses) bit true).expect (payoff deposit · true) = 1 := by
  simp [resultLaw, choiceLaw, silentProfile, bobRespond, choose, decisionInfo, payoff]

theorem resultLaw_update_alice (profile : Profile (model true).behavioralSignature)
    (alternative : (model true).BehavioralPolicy false) (bit disclose : Bool) :
    resultLaw (profile.update false alternative) bit disclose = resultLaw profile bit disclose := by
  simp [resultLaw, choiceLaw, Profile.update]

theorem target_rational (guesses : FinDist Bool) (deposit : ℝ)
    (deterrence : ∀ bit, 1 - deposit ≤ guesses.expect (correct bit)) :
    (targetAssessment (silentProfile guesses)).IsSequentiallyRationalWithin
      (fun who h => payoff deposit h.state who) 3 := by
  intro who decision alternative _
  cases who
  · obtain ⟨bit, rfl⟩ := alice_site_eq decision
    rw [alice_context _ bit (payoff deposit · false) alternative,
      alice_context _ bit (payoff deposit · false) _, Profile.update_eq_self]
    rw [value_alice _ _ (payoff deposit · false), value_alice _ _ (payoff deposit · false)]
    change (choiceLaw ((silentProfile guesses).update false alternative) false
      (some (some bit))).expect (fun disclose =>
        (resultLaw ((silentProfile guesses).update false alternative) bit
          (true && disclose)).expect (payoff deposit · false)) ≤
        (choiceLaw (silentProfile guesses) false (some (some bit))).expect (fun disclose =>
          (resultLaw (silentProfile guesses) bit (true && disclose)).expect
            (payoff deposit · false))
    simp_rw [Bool.true_and, resultLaw_update_alice, silent_branch_value]
    have stops : choiceLaw (silentProfile guesses) false (some (some bit)) =
        FinDist.pure false := by
      simp [choiceLaw, silentProfile, choose, decisionInfo]
    rw [stops, FinDist.expect_pure]
    simp only [Bool.false_eq_true, ite_false]
    apply FinDist.expect_le_of_forall
    intro disclose _
    cases disclose
    · exact le_rfl
    · exact deterrence bit
  · rcases target_bob_site_eq decision with rfl | ⟨bit, rfl⟩
    · have value := uniform_silent_context_value true (targetAssessment (silentProfile guesses))
        (target_silent_belief _) deposit
      exact le_of_eq ((value alternative).trans (value _).symm)
    · rw [disclosed_context _ bit (payoff deposit · true) alternative,
        disclosed_context _ bit (payoff deposit · true) _, Profile.update_eq_self]
      rw [value_bob _ _ _ (payoff deposit · true), value_bob _ _ _ (payoff deposit · true)]
      change (resultLaw ((silentProfile guesses).update true alternative) bit true).expect
        (payoff deposit · true) ≤
          (resultLaw (silentProfile guesses) bit true).expect (payoff deposit · true)
      rw [disclosed_bob_value]
      simp only [resultLaw, FinDist.expect_map, payoff, Bool.not_true, Bool.false_and]
      apply FinDist.expect_le_of_forall
      intro guess _
      split <;> norm_num

def isEquilibrium (deposit : ℝ) (assessment : (model true).BehavioralAssessment) : Prop :=
  assessment.IsSequentialEquilibriumFor (antichain true) (fun who decision =>
    assessment.continuationContext decision (fun h => payoff deposit h.state who) 3)

theorem target_sequential_equilibrium (guesses : FinDist Bool) (deposit : ℝ)
    (deterrence : ∀ bit, 1 - deposit ≤ guesses.expect (correct bit)) :
    isEquilibrium deposit (targetAssessment (silentProfile guesses)) :=
  ⟨target_rational guesses deposit deterrence, target_consistent guesses⟩

theorem correct_nonnegative (guesses : FinDist Bool) (bit : Bool) :
    0 ≤ guesses.expect (correct bit) := by
  have nonnegative := FinDist.expect_mono (μ := guesses)
    (u := fun _ => 0) (v := correct bit) (fun guess _ => by
      unfold correct
      split <;> norm_num)
  simpa only [FinDist.expect_const] using nonnegative

theorem universal_deposit_sequential_equilibrium (guesses : FinDist Bool) (deposit : ℝ)
    (enforced : 1 ≤ deposit) :
    isEquilibrium deposit (targetAssessment (silentProfile guesses)) := by
  apply target_sequential_equilibrium
  intro bit
  have nonnegative := correct_nonnegative guesses bit
  linarith

theorem fair_correct (bit : Bool) :
    (FinDist.uniformOfFintype (α := Bool)).expect (correct bit) = 1 / 2 := by
  cases bit <;>
    norm_num [correct, FinDist.expect_eq_sum, Fintype.sum_bool, FinDist.prob_uniformOfFintype]

theorem fair_sequential_equilibrium (deposit : ℝ) (enforced : 1 / 2 ≤ deposit) :
    isEquilibrium deposit (targetAssessment (silentProfile FinDist.uniformOfFintype)) := by
  apply target_sequential_equilibrium
  intro bit
  rw [fair_correct]
  linarith

theorem target_initialized_law (guesses : FinDist Bool) :
    (((model true).runSingleMoverBehavioralFrom (single true) (silentProfile guesses) 3
      (arena true).initHistory).map History.state).map retained =
        (FinDist.uniformOfFintype (α := Bool)).bind
          (fun bit => guesses.map (fun guess => some (bit, guess))) := by
  rw [run_initial]
  simp [choiceLaw, silentProfile, choose, decisionInfo, resultLaw, bobRespond,
    FinDist.map_eq_bind, retained]

/-- Each source player supplies only its own policy to this compilation. -/
def compile (who : Bool) (policy : (model false).BehavioralPolicy who) :
    (model true).BehavioralPolicy who := by
  cases who
  · exact choose true false false
  · exact bobRespond ((policy (some none)).map (fun choice => choice.val.getD false))

theorem compiled_profile (profile : Profile (model false).behavioralSignature) :
    Profile.map (target := (model true).behavioralSignature) compile profile =
      silentProfile (choiceLaw profile true (some none)) := by
  funext who
  cases who <;> rfl

theorem compile_initialized_law (profile : Profile (model false).behavioralSignature) :
    (((model true).runSingleMoverBehavioralFrom (single true)
      (Profile.map (target := (model true).behavioralSignature) compile profile) 3
        (arena true).initHistory).map History.state).map retained =
    (((model false).runSingleMoverBehavioralFrom (single false) profile 3
      (arena false).initHistory).map History.state).map retained := by
  rw [compiled_profile, target_initialized_law, source_initialized_law]
  simp [FinDist.product, FinDist.map_eq_bind]

theorem target_initialized_state_law (guesses : FinDist Bool) :
    ((model true).runSingleMoverBehavioralFrom (single true) (silentProfile guesses) 3
      (arena true).initHistory).map History.state =
        (FinDist.uniformOfFintype (α := Bool)).bind
          (fun bit => guesses.map (fun guess => State.done bit false guess)) := by
  rw [run_initial]
  simp [choiceLaw, silentProfile, choose, decisionInfo, resultLaw, bobRespond,
    FinDist.map_eq_bind]

theorem source_initialized_state_law (profile : Profile (model false).behavioralSignature) :
    ((model false).runSingleMoverBehavioralFrom (single false) profile 3
      (arena false).initHistory).map History.state =
        (FinDist.uniformOfFintype (α := Bool)).bind
          (fun bit => (choiceLaw profile true (some none)).map
            (fun guess => State.done bit false guess)) := by
  rw [run_initial]
  simp [Bool.false_and, resultLaw]

/-- Complete state-law preservation includes the absence of disclosure. -/
theorem compile_initialized_state_law (profile : Profile (model false).behavioralSignature) :
    ((model true).runSingleMoverBehavioralFrom (single true)
      (Profile.map (target := (model true).behavioralSignature) compile profile) 3
        (arena true).initHistory).map History.state =
      ((model false).runSingleMoverBehavioralFrom (single false) profile 3
        (arena false).initHistory).map History.state := by
  rw [compiled_profile, target_initialized_state_law, source_initialized_state_law]

/-- Actual payoffs, including the enforcement deduction, have their source
law: the compiled play never takes the penalized ambient action. -/
theorem compile_payoff_law (deposit : ℝ)
    (profile : Profile (model false).behavioralSignature) :
    (((model true).runSingleMoverBehavioralFrom (single true)
      (Profile.map (target := (model true).behavioralSignature) compile profile) 3
        (arena true).initHistory).map History.state).map
          (fun state who => payoff deposit state who) =
    (((model false).runSingleMoverBehavioralFrom (single false) profile 3
      (arena false).initHistory).map History.state).map (fun state who => payoff 0 state who) := by
  rw [compile_initialized_state_law, source_initialized_state_law]
  simp [FinDist.map_bind, FinDist.map_comp, Function.comp_def, payoff]

/-- In this fixed guessing game, automatic penalties implement every source
SE profile and preserve its complete retained law. Enforcement is assumed. -/
theorem all_source_profiles_implemented (deposit : ℝ) (enforced : 1 ≤ deposit)
    (profile : Profile (model false).behavioralSignature) :
    isEquilibrium deposit
      (targetAssessment
        (Profile.map (target := (model true).behavioralSignature) compile profile)) ∧
    (((model true).runSingleMoverBehavioralFrom (single true)
      (Profile.map (target := (model true).behavioralSignature) compile profile) 3
        (arena true).initHistory).map History.state).map retained =
    (((model false).runSingleMoverBehavioralFrom (single false) profile 3
      (arena false).initHistory).map History.state).map retained ∧
    (((model true).runSingleMoverBehavioralFrom (single true)
      (Profile.map (target := (model true).behavioralSignature) compile profile) 3
        (arena true).initHistory).map History.state).map
          (fun state who => payoff deposit state who) =
    (((model false).runSingleMoverBehavioralFrom (single false) profile 3
      (arena false).initHistory).map History.state).map (fun state who => payoff 0 state who) := by
  refine ⟨?_, compile_initialized_law profile, compile_payoff_law deposit profile⟩
  rw [compiled_profile]
  exact universal_deposit_sequential_equilibrium _ deposit enforced

theorem silent_reward_nonnegative (deposit : ℝ)
    (profile : Profile (model true).behavioralSignature) (bit : Bool) :
    0 ≤ (resultLaw profile bit false).expect (payoff deposit · false) := by
  simp only [resultLaw, Bool.false_eq_true, ite_false, FinDist.expect_map, payoff,
    Bool.not_false, Bool.and_false, sub_zero]
  have nonnegative := FinDist.expect_mono
    (μ := choiceLaw profile true (some none)) (u := fun _ => 0)
    (v := fun guess => if guess = bit then (1 : ℝ) else 0)
    (fun guess _ => by split <;> norm_num)
  simpa only [FinDist.expect_const] using nonnegative

theorem disclosed_reward_upper (deposit : ℝ)
    (profile : Profile (model true).behavioralSignature) (bit : Bool) :
    (resultLaw profile bit true).expect (payoff deposit · false) ≤ 1 - deposit := by
  simp only [resultLaw, ite_true, FinDist.expect_map, payoff, Bool.not_false,
    Bool.true_and]
  apply FinDist.expect_le_of_forall
  intro guess _
  split <;> simp

/-- With strict collateral, disclosure is strictly worse than silence at
each private type, regardless of Bob's beliefs or continuation strategy. -/
theorem strict_deposit_silence (deposit : ℝ) (strict : 1 < deposit)
    (assessment : (model true).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who h => payoff deposit h.state who) 3) (bit : Bool) :
    choiceLaw assessment.strategy false (some (some bit)) = FinDist.pure false := by
  have best := rational false (aliceSite bit) (choose true false false) (Set.mem_univ _)
  rw [alice_context assessment bit (payoff deposit · false) (choose true false false),
    alice_context assessment bit (payoff deposit · false) (assessment.strategy false),
    Profile.update_eq_self,
    value_alice _ _ (payoff deposit · false), value_alice _ _ (payoff deposit · false)] at best
  simp_rw [Bool.true_and, resultLaw_update_alice] at best
  have silence : choiceLaw
      (Profile.update (sig := (model true).behavioralSignature) assessment.strategy false
        (choose true false false)) false (some (some bit)) = FinDist.pure false := by
    simp [choiceLaw, Profile.update, choose, decisionInfo]
  rw [silence, FinDist.expect_pure] at best
  have worse : (resultLaw assessment.strategy bit true).expect (payoff deposit · false) <
      (resultLaw assessment.strategy bit false).expect (payoff deposit · false) := by
    have upper := disclosed_reward_upper deposit assessment.strategy bit
    have lower := silent_reward_nonnegative deposit assessment.strategy bit
    linarith
  apply FinDist.eq_pure_of_support_subset_singleton
  intro disclose supported
  cases disclose
  · exact Set.mem_singleton false
  · have loses := FinDist.expect_lt_of_mem_support
      (choiceLaw assessment.strategy false (some (some bit)))
      (fun disclose => (resultLaw assessment.strategy bit disclose).expect (payoff deposit · false))
      ((resultLaw assessment.strategy bit false).expect (payoff deposit · false))
      (fun disclose _ => by
        cases disclose
        · exact le_rfl
        · exact worse.le) supported worse
    exact (not_lt_of_ge best loses).elim

def reflectedProfile (profile : Profile (model true).behavioralSignature) :
    Profile (model false).behavioralSignature :=
  sourceProfile (choiceLaw profile true (some none))

/-- Strict collateral makes every rational target's full initialized state
law a source law; this is independent of the proposed forward compiler. -/
theorem strict_deposit_state_law (deposit : ℝ) (strict : 1 < deposit)
    (assessment : (model true).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who h => payoff deposit h.state who) 3) :
    ((model true).runSingleMoverBehavioralFrom (single true) assessment.strategy 3
      (arena true).initHistory).map History.state =
    ((model false).runSingleMoverBehavioralFrom (single false)
      (reflectedProfile assessment.strategy) 3 (arena false).initHistory).map History.state := by
  rw [run_initial, source_initialized_state_law]
  simp_rw [strict_deposit_silence deposit strict assessment rational]
  simp [reflectedProfile, source_profile_guess, resultLaw]

theorem strict_deposit_payoff_law (deposit : ℝ) (strict : 1 < deposit)
    (assessment : (model true).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who h => payoff deposit h.state who) 3) :
    (((model true).runSingleMoverBehavioralFrom (single true) assessment.strategy 3
      (arena true).initHistory).map History.state).map (fun state who => payoff deposit state who) =
    (((model false).runSingleMoverBehavioralFrom (single false)
      (reflectedProfile assessment.strategy) 3 (arena false).initHistory).map History.state).map
        (fun state who => payoff 0 state who) := by
  rw [strict_deposit_state_law deposit strict assessment rational, source_initialized_state_law]
  simp [FinDist.map_bind, FinDist.map_comp, Function.comp_def, payoff]

/-- Every target sequential equilibrium under strict collateral has the full
state law and actual payoff law of a source sequential equilibrium. -/
theorem strict_deposit_reflects_equilibrium (deposit : ℝ) (strict : 1 < deposit)
    (assessment : (model true).BehavioralAssessment)
    (equilibrium : isEquilibrium deposit assessment) :
    (sourceAssessment (reflectedProfile assessment.strategy)).IsSequentialEquilibriumFor
      (antichain false) (fun who decision =>
        (sourceAssessment (reflectedProfile assessment.strategy)).continuationContext decision
          (fun h => payoff 0 h.state who) 3) ∧
    ((model true).runSingleMoverBehavioralFrom (single true) assessment.strategy 3
      (arena true).initHistory).map History.state =
    ((model false).runSingleMoverBehavioralFrom (single false)
      (reflectedProfile assessment.strategy) 3 (arena false).initHistory).map History.state ∧
    (((model true).runSingleMoverBehavioralFrom (single true) assessment.strategy 3
      (arena true).initHistory).map History.state).map (fun state who => payoff deposit state who) =
    (((model false).runSingleMoverBehavioralFrom (single false)
      (reflectedProfile assessment.strategy) 3 (arena false).initHistory).map History.state).map
        (fun state who => payoff 0 state who) :=
  ⟨source_sequential_equilibrium _,
    strict_deposit_state_law deposit strict assessment equilibrium.1,
    strict_deposit_payoff_law deposit strict assessment equilibrium.1⟩

end GameTheoryExtensionsTests.AmbientEnforcement
