/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensionsTests.OffPathDisclosure
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Disclosure after a deviation creates additional SPE obligations

The same source behavioral profile is SPE for two opposite Bob utilities.
No target behavioral profile is SPE for both. The obstruction concerns a
utility-independent translation, even one allowed to inspect the whole profile.
-/

noncomputable section

namespace GameTheoryExtensionsTests.OffPathDisclosure

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol

def choose (disclose who value : Bool) : (model disclose).BehavioralPolicy who :=
  fun info => PMF.pure ⟨if info.isSome then some value else none, by
    cases info <;> rfl⟩

def prescribed (disclose : Bool) : Profile (model disclose).behavioralSignature :=
  fun who => choose disclose who false

def choiceLaw {disclose : Bool} (profile : Profile (model disclose).behavioralSignature)
    (who : Bool) (info : Option Bool) : PMF Bool :=
  (profile who info).map (fun choice => choice.val.getD false)

def kernel {disclose : Bool} (profile : Profile (model disclose).behavioralSignature) :
    State → PMF State
  | .initial => (PMF.uniformOfFintype Bool).map State.alice
  | .alice bit => (choiceLaw profile false (some bit)).map
      (fun ask => if ask then .bob bit else .done bit none)
  | .bob bit => (choiceLaw profile true (some (if disclose then bit else false))).map
      (fun guess => .done bit (some guess))
  | .done bit guess => PMF.pure (.done bit guess)

theorem chooser_kernel {disclose : Bool}
    (profile : Profile (model disclose).behavioralSignature) (history : arena.History)
    (running : ¬ arena.terminal history.state) :
    ((model disclose).singleMoverChooser single profile history running).bind
      (arena.step history.state) = kernel profile history.state := by
  rcases history with ⟨state, trace⟩
  cases state with
  | initial => simp [arena, transition, kernel]
  | alice bit =>
      have marginal := (model disclose).singleMoverJoint_marginal single
        profile ⟨_, trace⟩ running false
      rw [info_state] at marginal
      change ((model disclose).singleMoverJoint single profile ⟨_, trace⟩ running).map
        (fun joint => joint.1 false) = (profile false (some bit)).map Subtype.val at marginal
      have mapped := congrArg (fun law => law.map
        (fun choice : Option Bool => if choice.getD false then State.bob bit
          else State.done bit none)) marginal
      simpa only [InformationModel.singleMoverChooser, arena, transition,
        kernel, choiceLaw, observation, ↓reduceIte, PMF.map_comp,
        Function.comp_def, ← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind, PMF.pure_bind,
        ite_true] using mapped
  | bob bit =>
      have marginal := (model disclose).singleMoverJoint_marginal single
        profile ⟨_, trace⟩ running true
      rw [info_state] at marginal
      change ((model disclose).singleMoverJoint single profile ⟨_, trace⟩ running).map
        (fun joint => joint.1 true) =
          (profile true (some (if disclose then bit else false))).map Subtype.val at marginal
      have mapped := congrArg (fun law => law.map
        (fun choice : Option Bool => State.done bit (some (choice.getD false)))) marginal
      simpa only [InformationModel.singleMoverChooser, arena, transition,
        kernel, choiceLaw, observation, ↓reduceIte, PMF.map_comp,
        Function.comp_def, ← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind, PMF.pure_bind,
        ite_true] using mapped
  | done bit guess => exact (running trivial).elim

theorem run_states {disclose : Bool}
    (profile : Profile (model disclose).behavioralSignature) (fuel : Nat)
    (history : arena.History) :
    ((model disclose).runSingleMoverBehavioralFrom single profile fuel history).map
      History.state = (fun law => law.bind (kernel profile))^[fuel]
        (PMF.pure history.state) := by
  apply runRandomizedFor_map_state
  · intro state stopped
    cases state <;> try contradiction
    rfl
  · exact chooser_kernel profile

def resultLaw {disclose : Bool} (profile : Profile (model disclose).behavioralSignature)
    (bit : Bool) : PMF State :=
  (choiceLaw profile true (some (if disclose then bit else false))).map
    (fun guess => .done bit (some guess))

theorem run_bob {disclose : Bool}
    (profile : Profile (model disclose).behavioralSignature) (bit : Bool) :
    ((model disclose).runSingleMoverBehavioralFrom single profile 3 (bobHistory bit)).map
      History.state = resultLaw profile bit := by
  rw [run_states]
  simp [Function.iterate_succ_apply', kernel, resultLaw,
    bobHistory, aliceHistory, History.extend, aliceJoint, ← PMF.bind_pure_comp, Function.comp_def]

theorem run_initial {disclose : Bool}
    (profile : Profile (model disclose).behavioralSignature) :
    ((model disclose).runSingleMoverBehavioralFrom single profile 3 arena.initHistory).map
      History.state = (PMF.uniformOfFintype Bool).bind fun bit =>
        (choiceLaw profile false (some bit)).bind fun ask =>
          if ask then resultLaw profile bit else PMF.pure (.done bit none) := by
  rw [run_states]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    ExecutionProtocol.initHistory, PMF.pure_bind, kernel, PMF.bind_map, PMF.bind_bind]
  apply bind_congr_on_support _
  intro bit _
  apply bind_congr_on_support _
  intro ask _
  cases ask <;> simp [resultLaw]

theorem value_bob {disclose : Bool}
    (profile : Profile (model disclose).behavioralSignature) (bit : Bool) (u : State → ℝ) :
    expect ((model disclose).runSingleMoverBehavioralFrom single profile 3 (bobHistory bit))
      (fun h => u h.state) = expect (resultLaw profile bit) u := by
  have values := congrArg (fun law => expect law u) (run_bob profile bit)
  simpa only [expect_map] using values

theorem value_initial {disclose : Bool}
    (profile : Profile (model disclose).behavioralSignature) (u : State → ℝ) :
    expect ((model disclose).runSingleMoverBehavioralFrom single profile 3 arena.initHistory)
      (fun h => u h.state) = expect ((PMF.uniformOfFintype Bool).bind fun bit =>
        (choiceLaw profile false (some bit)).bind fun ask =>
          if ask then resultLaw profile bit else PMF.pure (.done bit none)) u := by
  have values := congrArg (fun law => expect law u) (run_initial profile)
  simpa only [expect_map] using values

/-- A utility depends on the original private bit and public result. -/
def utility (matchBit : Bool) : State → Bool → ℝ
  | .done bit (some guess), true => if (guess == bit) = matchBit then 1 else 0
  | _, _ => 0

def payoff (matchBit : Bool) (history : arena.History) (who : Bool) : ℝ :=
  utility matchBit history.state who

theorem initial_bob_zero (disclose matchBit : Bool)
    (replacement : (model disclose).BehavioralPolicy true) :
    expect ((model disclose).runSingleMoverBehavioralFrom single
      (Profile.update (prescribed disclose) true replacement) 3 arena.initHistory)
      (payoff matchBit · true) = 0 := by
  unfold payoff
  rw [value_initial (disclose := disclose) _ (utility matchBit · true)]
  simp [choiceLaw, Profile.update, prescribed, choose, utility, FinDist.expect_bind]

theorem prescribed_bob_zero (disclose matchBit : Bool) :
    expect ((model disclose).runSingleMoverBehavioralFrom single (prescribed disclose)
      3 arena.initHistory) (payoff matchBit · true) = 0 := by
  have same : Profile.update (prescribed disclose) true (choose disclose true false) =
      prescribed disclose := by simp [prescribed, Profile.update]
  rw [← same]
  exact initial_bob_zero disclose matchBit _

theorem source_spe (matchBit : Bool) :
    (model false).IsSingleMoverBehavioralSubgamePerfect single bounded (prescribed false)
      (payoff matchBit) := by
  rw [InformationModel.isSingleMoverBehavioralSubgamePerfect_iff]
  intro history proper who alternative
  rcases source_proper_initial_or_terminal history proper with rfl | stopped
  · cases who
    · simp [payoff, utility]
    · rw [initial_bob_zero, prescribed_bob_zero]
  · simp only [InformationModel.runSingleMoverBehavioralFrom,
      runRandomizedFor_of_terminal _ _ stopped, expect_pure]
    exact le_rfl

theorem bob_deviation_value (matchBit : Bool)
    (profile : Profile (model true).behavioralSignature) :
    expect ((model true).runSingleMoverBehavioralFrom single
      (Profile.update profile true (choose true true (!matchBit))) 3 (bobHistory false))
      (payoff matchBit · true) = 1 := by
  unfold payoff
  rw [value_bob (disclose := true) _ false (utility matchBit · true)]
  cases matchBit <;> simp [resultLaw, choiceLaw, Profile.update, choose, utility]

theorem bob_utility_sum (profile : Profile (model true).behavioralSignature) :
    expect ((model true).runSingleMoverBehavioralFrom single profile 3 (bobHistory false))
        (payoff true · true) +
      expect ((model true).runSingleMoverBehavioralFrom single profile 3 (bobHistory false))
        (payoff false · true) = 1 := by
  unfold payoff
  rw [value_bob profile false (utility true · true), value_bob profile false (utility false · true)]
  simp only [resultLaw, expect_map, ← FinDist.expect_add]
  have constant : (fun guess => utility true (.done false (some guess)) true +
      utility false (.done false (some guess)) true) = fun _ => (1 : ℝ) := by
    funext guess
    cases guess <;> norm_num [utility]
  rw [constant, expect_constant]

theorem no_common_target_spe : ¬ ∃ profile : Profile (model true).behavioralSignature,
    (model true).IsSingleMoverBehavioralSubgamePerfect single bounded profile (payoff true) ∧
      (model true).IsSingleMoverBehavioralSubgamePerfect single bounded profile (payoff false) := by
  rintro ⟨profile, matchOptimal, mismatchOptimal⟩
  rw [InformationModel.isSingleMoverBehavioralSubgamePerfect_iff] at matchOptimal mismatchOptimal
  have first := matchOptimal (bobHistory false) (bob_proper false) true (choose true true false)
  have second := mismatchOptimal (bobHistory false) (bob_proper false) true (choose true true true)
  have firstValue := bob_deviation_value true profile
  have secondValue := bob_deviation_value false profile
  have total := bob_utility_sum profile
  simp only [Bool.not_true, Bool.not_false] at firstValue secondValue
  linarith

/-- Failure already holds for an arbitrary whole-profile translator. -/
theorem no_utility_independent_spe_translation : ¬ ∃ translate :
    Profile (model false).behavioralSignature → Profile (model true).behavioralSignature,
    ∀ matchBit, (model false).IsSingleMoverBehavioralSubgamePerfect single bounded (prescribed false)
      (payoff matchBit) → (model true).IsSingleMoverBehavioralSubgamePerfect single bounded
        (translate (prescribed false)) (payoff matchBit) := by
  rintro ⟨translate, preserves⟩
  exact no_common_target_spe ⟨translate (prescribed false),
    preserves true (source_spe true), preserves false (source_spe false)⟩

end GameTheoryExtensionsTests.OffPathDisclosure
