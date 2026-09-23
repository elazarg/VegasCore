/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensionsTests.SequentialCredibility
import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheory.Analysis.Protocol.Examples

/-! # A genuine off-path information set with consistent beliefs

Alice stops and Bob would choose true. Perturb both players at every decision
site. Alice's probability of asking Bob is independent of her private bit,
so Bob's posterior stays uniform as his information set becomes off path.
-/

noncomputable section

namespace GameTheoryExtensionsTests.SequentialBeliefs

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter
open GameTheory.Protocol.ExecutionProtocol OffPathDisclosure SequentialCredibility
open GameTheory.Analysis.Protocol.Examples

def limitProfile : Profile (model false).behavioralSignature := fun who => choose false who who

def perturbedProfile (n : Nat) : Profile (model false).behavioralSignature := fun who info =>
  FinDist.mix (trembleWeight n) (trembleWeight_nonneg n) (trembleWeight_le_one n)
    (choose false who (!who) info) (choose false who who info)

theorem perturbed_full (n : Nat) :
    (InformationModel.BehavioralAssessment.ofStrategy (perturbedProfile n)).IsFullyMixed := by
  intro who ⟨info, valid⟩ ⟨value, legal⟩
  change (⟨value, legal⟩ : (model false).Choice who info) ∈
    (perturbedProfile n who info).support
  rw [perturbedProfile]
  simp only [choose]
  rw [FinDist.mem_support_mix_pure_iff _ _ _ (trembleWeight_pos n) (trembleWeight_lt_one n)]
  simp only [Subtype.mk.injEq]
  change value.isSome = info.isSome at legal
  cases info <;> cases value <;> cases who
  all_goals simp_all only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
    Bool.true_eq_false, Bool.not_false, Bool.not_true, ite_true, ite_false]
  all_goals first | trivial | (rename_i value; cases value <;> simp)

instance : Finite arena.History := (perturbed_full 0).finite_history bounded

instance : Fintype arena.History := Fintype.ofFinite _

instance (disclose who : Bool) (site : (model disclose).InformationSite who) :
    Fintype ((model disclose).InformationHistory who site.1) := by
  classical
  infer_instance

def aliceSite (bit : Bool) : (model false).InformationSite false :=
  (model false).informationSite false (aliceHistory bit) false (by exact id) rfl

theorem alice_site_eq (site : (model false).InformationSite false) :
    ∃ bit, site = aliceSite bit := by
  obtain ⟨history, running, action, legal⟩ := site.2
  have active := InformationModel.InformationSite.active (model false) site history
  have known : Classified history.1 := classified history.1.trace
  rcases known with same | ⟨bit, same⟩ | ⟨bit, same⟩ |
    ⟨bit, same⟩ | ⟨bit, guess, same⟩
  all_goals rw [same] at active
  all_goals try simp [arena, actor, aliceHistory, bobHistory, stopHistory, guessHistory,
    aliceJoint, bobJoint] at active
  refine ⟨bit, Subtype.ext ?_⟩
  have observed := history.2.symm
  rw [same] at observed
  exact observed

theorem bob_site_eq (site : (model false).InformationSite true) : site = bobSite := by
  obtain ⟨history, running, action, legal⟩ := site.2
  have active := InformationModel.InformationSite.active (model false) site history
  have known : Classified history.1 := classified history.1.trace
  rcases known with same | ⟨bit, same⟩ | ⟨bit, same⟩ |
    ⟨bit, same⟩ | ⟨bit, guess, same⟩
  all_goals rw [same] at active
  all_goals try simp [arena, actor, aliceHistory, bobHistory, stopHistory, guessHistory,
    aliceJoint, bobJoint] at active
  apply Subtype.ext
  have observed := history.2.symm
  rw [same] at observed
  exact observed

theorem history_at_alice (bit : Bool)
    (history : (model false).InformationHistory false (aliceSite bit).1) :
    history.1 = aliceHistory bit := by
  have observed := history.2
  rw [info_state] at observed
  have known : Classified history.1 := classified history.1.trace
  rcases known with same | ⟨other, same⟩ | ⟨other, same⟩ |
    ⟨other, same⟩ | ⟨other, guess, same⟩
  all_goals rw [same] at observed
  all_goals try cases observed
  exact same

theorem antichain : (model false).DecisionInformationAntichain := by
  intro who site first second joint legal target realized fuel reached
  have lengths : first.1.trace.length = second.1.trace.length := by
    cases who
    · obtain ⟨bit, rfl⟩ := alice_site_eq site
      rw [history_at_alice bit first, history_at_alice bit second]
    · have siteEq := bob_site_eq site
      subst site
      obtain ⟨left, leftEq⟩ := history_at_bob first
      obtain ⟨right, rightEq⟩ := history_at_bob second
      rw [leftEq, rightEq]
      rfl
  have increase := reached.trace_length_le
  change first.1.trace.length + 1 ≤ second.1.trace.length at increase
  omega

def assessment (profile : Profile (model false).behavioralSignature) :
    (model false).BehavioralAssessment where
  strategy := profile
  belief who site := by
    cases who
    · exact FinDist.pure ⟨aliceHistory (site.1.getD false), by
        obtain ⟨bit, rfl⟩ := alice_site_eq site; rfl⟩
    · exact (FinDist.uniformOfFintype (α := Bool)).map fun bit =>
        ⟨bobHistory bit, by rw [bob_site_eq site]; rfl⟩

def historyOfState : State → arena.History
  | .initial => arena.initHistory
  | .alice bit => aliceHistory bit
  | .bob bit => bobHistory bit
  | .done bit none => stopHistory bit
  | .done bit (some guess) => guessHistory bit guess

theorem historyOfState_state (history : arena.History) :
    historyOfState history.state = history := by
  have known : Classified history := classified history.trace
  rcases known with rfl | ⟨bit, rfl⟩ | ⟨bit, rfl⟩ |
    ⟨bit, rfl⟩ | ⟨bit, guess, rfl⟩ <;> rfl

theorem state_injective : Function.Injective (History.state (E := arena)) :=
  Function.LeftInverse.injective historyOfState_state

theorem reach_alice (profile : Profile (model false).behavioralSignature) (bit : Bool) :
    (model false).historyReachProbability profile (aliceHistory bit) = 1 / 2 := by
  classical
  change ((model false).runBehavioralFrom profile 1 arena.initHistory).prob (aliceHistory bit) = _
  rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom (model false) single,
    ← FinDist.prob_map_of_injective History.state state_injective, run_states]
  simp only [Function.iterate_one, FinDist.pure_bind]
  change ((FinDist.uniformOfFintype (α := Bool)).map State.alice).prob (.alice bit) = _
  rw [FinDist.prob_map_of_injective State.alice (fun _ _ same => State.alice.inj same)]
  norm_num [FinDist.prob_uniformOfFintype, Fintype.card_bool]

theorem reach_bob (n : Nat) (bit : Bool) :
    (model false).historyReachProbability (perturbedProfile n) (bobHistory bit) =
      trembleWeight n / 2 := by
  classical
  change ((model false).runBehavioralFrom (perturbedProfile n) 2 arena.initHistory).prob
    (bobHistory bit) = _
  rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom (model false) single,
    ← FinDist.prob_map_of_injective History.state state_injective, run_states]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    FinDist.pure_bind, initHistory, kernel, FinDist.bind_map, FinDist.prob_bind]
  change (FinDist.uniformOfFintype (α := Bool)).expect (fun hidden =>
    ((choiceLaw (perturbedProfile n) false (some hidden)).map
      (fun ask => if ask then State.bob hidden else .done hidden none)).prob (.bob bit)) = _
  rw [FinDist.expect_eq_sum, Fintype.sum_bool]
  cases bit <;>
    simp [choiceLaw, perturbedProfile, choose, FinDist.map_mix, FinDist.prob_mix,
      FinDist.prob_uniformOfFintype, Fintype.card_bool, FinDist.prob_pure_eq_ite] <;> ring

def bobInformationHistory (bit : Bool) : (model false).InformationHistory true bobSite.1 :=
  ⟨bobHistory bit, rfl⟩

theorem bobInformationHistory_injective : Function.Injective bobInformationHistory := by
  intro first second same
  have states := congrArg (fun history => history.1.state) same
  change State.bob first = State.bob second at states
  exact State.bob.inj states

def bobHistories : Bool ≃ (model false).InformationHistory true bobSite.1 :=
  Equiv.ofBijective bobInformationHistory ⟨bobInformationHistory_injective, fun history => by
    obtain ⟨bit, same⟩ := history_at_bob history
    exact ⟨bit, Subtype.ext same.symm⟩⟩

theorem mass_bob (n : Nat) :
    (model false).informationMass (perturbedProfile n) true bobSite = trembleWeight n := by
  unfold InformationModel.informationMass
  rw [← bobHistories.sum_comp]
  change (∑ bit : Bool, (model false).historyReachProbability (perturbedProfile n)
    (bobHistory bit)) = _
  simp only [reach_bob, Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  ring

theorem belief_bob_prob (profile : Profile (model false).behavioralSignature) (bit : Bool) :
    ((assessment profile).belief true bobSite).prob (bobInformationHistory bit) = 1 / 2 := by
  classical
  change ((FinDist.uniformOfFintype (α := Bool)).map bobInformationHistory).prob
    (bobInformationHistory bit) = _
  rw [FinDist.prob_map_of_injective _ bobInformationHistory_injective]
  norm_num [FinDist.prob_uniformOfFintype, Fintype.card_bool]

instance (bit : Bool) : Subsingleton ((model false).InformationHistory false (aliceSite bit).1) :=
  ⟨fun first second => Subtype.ext
    ((history_at_alice bit first).trans (history_at_alice bit second).symm)⟩

theorem perturbed_bayes (n : Nat) :
    InformationModel.BehavioralAssessment.IsBayesConsistent (model false)
      (assessment (perturbedProfile n)) antichain := by
  intro who site positive history
  cases who
  · obtain ⟨bit, rfl⟩ := alice_site_eq site
    have equal : (assessment (perturbedProfile n)).belief false (aliceSite bit) =
        (model false).bayesBelief (perturbedProfile n) false (aliceSite bit)
          (antichain false (aliceSite bit)) positive := by
      exact (FinDist.eq_pure_of_subsingleton _ history).trans
        (FinDist.eq_pure_of_subsingleton _ history).symm
    rw [equal]
    exact InformationModel.bayesBelief_prob _ _ _ _ _ _ _
  · have same := bob_site_eq site
    subst site
    obtain ⟨bit, same⟩ := history_at_bob history
    have historyEq : history = bobInformationHistory bit := Subtype.ext same
    subst history
    change ((assessment (perturbedProfile n)).belief true bobSite).prob
      (bobInformationHistory bit) = (model false).historyReachProbability (perturbedProfile n)
        (bobHistory bit) / (model false).informationMass (perturbedProfile n) true bobSite
    rw [belief_bob_prob, reach_bob, mass_bob]
    field_simp [(trembleWeight_pos n).ne']

theorem assessment_converges : InformationModel.BehavioralAssessmentConvergesPointwise
    (fun n => assessment (perturbedProfile n)) (assessment limitProfile) := by
  constructor
  · intro who site choice
    change Tendsto (fun n => (perturbedProfile n who site.1).prob choice) atTop
      (nhds ((limitProfile who site.1).prob choice))
    simp only [perturbedProfile, FinDist.prob_mix]
    have left := trembleWeight_tendsto_zero.mul_const
      ((choose false who (!who) site.1).prob choice)
    have one : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have right := (one.sub trembleWeight_tendsto_zero).mul_const
      ((choose false who who site.1).prob choice)
    simpa only [zero_mul, sub_zero, one_mul, zero_add, limitProfile] using left.add right
  · intro who site
    exact finDistConvergesPointwise_const _

theorem consistent : (assessment limitProfile).IsSequentiallyConsistent antichain :=
  ⟨fun n => assessment (perturbedProfile n),
    fun n => ⟨perturbed_full n, perturbed_bayes n⟩, assessment_converges⟩

theorem reach_bob_limit (bit : Bool) :
    (model false).historyReachProbability limitProfile (bobHistory bit) = 0 := by
  classical
  change ((model false).runBehavioralFrom limitProfile 2 arena.initHistory).prob
    (bobHistory bit) = _
  rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom (model false) single,
    ← FinDist.prob_map_of_injective History.state state_injective, run_states]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    FinDist.pure_bind, initHistory, kernel, FinDist.bind_map, FinDist.prob_bind]
  change (FinDist.uniformOfFintype (α := Bool)).expect (fun hidden =>
    ((choiceLaw limitProfile false (some hidden)).map
      (fun ask => if ask then State.bob hidden else .done hidden none)).prob (.bob bit)) = _
  simp [choiceLaw, limitProfile, choose, FinDist.prob_pure_eq_ite]

theorem bob_off_path : (model false).informationMass limitProfile true bobSite = 0 := by
  unfold InformationModel.informationMass
  rw [← bobHistories.sum_comp]
  change (∑ bit : Bool, (model false).historyReachProbability limitProfile (bobHistory bit)) = _
  simp [reach_bob_limit]

end GameTheoryExtensionsTests.SequentialBeliefs
