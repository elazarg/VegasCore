/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeHistory
import Interaction.ReactiveFiniteAssessment
import Interaction.ReactiveResponseEvaluation
import GameTheoryExtensions.Analysis.Protocol.BehavioralContinuity

/-! # A common consistent native completion of receiver responses

Keep the prescribed policy at Bob's ordinary information site. At every other
native observation, choose an optimal response to each fully mixed prefix and
take one common limit of policies and Bayes beliefs. Alice and Watcher retain
their prescribed policies. This module proves Bob's off-path rationality;
the prescribed site's posterior and the other players' incentives are proved
from the concrete execution separately.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.InformationModel GameTheory.Math.Probability Filter

abbrev nativeAntichain :=
  nativeMenu.decisionInformationAntichain nativeInitialLaw nativeHorizon nativeScheduler

def nativeReference : nativeModel.BehavioralAssessment :=
  nativeMenu.uniformAssessment nativeInitialLaw nativeHorizon nativeScheduler

theorem nativeReference_mixed : nativeReference.IsFullyMixed :=
  nativeMenu.uniform_fullyMixed nativeInitialLaw nativeHorizon nativeScheduler

/-- The assessment continuation is the original native runner averaged over
the assessment's state belief. The bound covers every legal history. -/
theorem native_context_value (assessment : nativeModel.BehavioralAssessment)
    (who : Player) (site : nativeModel.InformationSite who) (deposit : ℝ)
    (alternative : nativeModel.BehavioralPolicy who) :
    (assessment.continuationContext site
      (fun history => nativeUtility deposit who history.state) (2 * nativeHorizon + 1)).value
        alternative =
      ((assessment.belief who site).map (fun history => history.1.state)).expect (fun state =>
        (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler
          (nativeMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler
            (Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy who
              alternative)) state).expect (nativeUtility deposit who)) := by
  simp only [BehavioralAssessment.continuationContext_value, FinDist.expect_bind,
    FinDist.expect_map]
  apply FinDist.expect_congr
  intro history _
  have bound := nativeApp.trace_bound nativeInitialLaw nativeHorizon nativeScheduler
    (nativeMenu.toRawTrace nativeInitialLaw nativeHorizon nativeScheduler history.1.trace)
  have law := nativeMenu.run_eq_finish nativeInitialLaw nativeHorizon nativeScheduler
    (Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy who alternative)
    (2 * nativeHorizon + 1) history.1 (by
      change nativeApp.rank nativeHorizon history.1.state ≤ 2 * nativeHorizon + 1
      omega)
  have value := congrArg (fun outcomes : FinDist nativeApp.ProtocolState =>
    outcomes.expect (nativeUtility deposit who)) law
  simpa only [FinDist.expect_map] using value

private def weight (n : ℕ) : ℝ := (1 / ((n : ℝ) + 1)) / 2

private theorem weight_positive (n : ℕ) : 0 < weight n := by
  dsimp [weight]
  positivity

private theorem weight_below_one (n : ℕ) : weight n < 1 := by
  have upper : 1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  dsimp [weight]
  linarith

private theorem weight_vanishes : Tendsto weight atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) / 2) atTop (nhds 0)
  simpa only [zero_div] using
    tendsto_one_div_add_atTop_nhds_zero_nat.div_const (2 : ℝ)

private def baseTremble (baseline : Profile nativeModel.behavioralSignature) (n : ℕ) :
    nativeModel.BehavioralAssessment :=
  nativeReference.perturb baseline (weight n) (weight_positive n).le (weight_below_one n).le

private theorem baseTremble_mixed (baseline : Profile nativeModel.behavioralSignature) (n : ℕ) :
    (baseTremble baseline n).IsFullyMixed :=
  nativeReference.perturb_fullyMixed nativeReference_mixed baseline (weight n)
    (weight_positive n).le (weight_below_one n).le (weight_positive n)

private def response (baseline : Profile nativeModel.behavioralSignature)
    (quiet : nativeModel.InformationSite bob) (deposit : ℝ) (n : ℕ) :
    nativeModel.BehavioralPolicy bob := fun info => by
  classical
  exact if info = quiet.1 then baseline bob info else
    bestLastPolicy (baseTremble baseline n) (baseTremble_mixed baseline n) nativeAntichain bob
      (fun history => nativeUtility deposit bob history.state) (2 * nativeHorizon) info

private def responseLaw (baseline : Profile nativeModel.behavioralSignature)
    (quiet : nativeModel.InformationSite bob) (deposit : ℝ) (n : ℕ) :
    nativeModel.BehavioralPolicy bob := fun info =>
  FinDist.mix (weight n) (weight_positive n).le (weight_below_one n).le
    (nativeReference.strategy bob info) (response baseline quiet deposit n info)

private def responseProfile (baseline : Profile nativeModel.behavioralSignature)
    (quiet : nativeModel.InformationSite bob) (deposit : ℝ) (n : ℕ) :
    Profile nativeModel.behavioralSignature :=
  Profile.update (sig := nativeModel.behavioralSignature)
    (baseTremble baseline n).strategy bob (responseLaw baseline quiet deposit n)

private theorem responseProfile_mixed (baseline : Profile nativeModel.behavioralSignature)
    (quiet : nativeModel.InformationSite bob) (deposit : ℝ) (n : ℕ) :
    (BehavioralAssessment.ofStrategy (responseProfile baseline quiet deposit n)).IsFullyMixed := by
  intro who site choice
  by_cases own : who = bob
  · subst who
    change choice ∈ (responseLaw baseline quiet deposit n site.1).support
    exact FinDist.mem_support_mix_left _ _ _ (weight_positive n)
      (nativeReference_mixed bob site choice)
  · change choice ∈ (Profile.update (sig := nativeModel.behavioralSignature)
      (baseTremble baseline n).strategy bob
      (responseLaw baseline quiet deposit n) who site.1).support
    rw [Profile.update_of_ne _ _ own]
    exact baseTremble_mixed baseline n who site choice

private def sequence (baseline : Profile nativeModel.behavioralSignature)
    (quiet : nativeModel.InformationSite bob) (deposit : ℝ) (n : ℕ) :
    nativeModel.BehavioralAssessment :=
  (BehavioralAssessment.ofStrategy (responseProfile baseline quiet deposit n)).bayes
    (responseProfile_mixed baseline quiet deposit n) nativeAntichain

private theorem bob_belief (baseline : Profile nativeModel.behavioralSignature)
    (quiet : nativeModel.InformationSite bob) (deposit : ℝ) (n : ℕ)
    (site : nativeModel.InformationSite bob) :
    (sequence baseline quiet deposit n).belief bob site =
      ((baseTremble baseline n).bayes (baseTremble_mixed baseline n)
        nativeAntichain).belief bob site := by
  apply FinDist.ext_of_prob
  intro history
  have mass : nativeModel.informationMass (responseProfile baseline quiet deposit n) bob site =
      nativeModel.informationMass (baseTremble baseline n).strategy bob site := by
    unfold InformationModel.informationMass
    apply Finset.sum_congr rfl
    intro next _
    exact bob_decision_reach_invariant (baseTremble baseline n).strategy
      (responseLaw baseline quiet deposit n) site next
  simp only [sequence, BehavioralAssessment.bayes, BehavioralAssessment.ofStrategy_strategy,
    bayesBelief_prob, mass]
  exact congrArg (fun value => value /
    nativeModel.informationMass (baseTremble baseline n).strategy bob site)
    (bob_decision_reach_invariant (baseTremble baseline n).strategy
      (responseLaw baseline quiet deposit n) site history)

private theorem bob_value (baseline : Profile nativeModel.behavioralSignature)
    (quiet : nativeModel.InformationSite bob) (deposit : ℝ) (n : ℕ)
    (site : nativeModel.InformationSite bob) (alternative : nativeModel.BehavioralPolicy bob) :
    ((sequence baseline quiet deposit n).continuationContext site
      (fun history => nativeUtility deposit bob history.state) (2 * nativeHorizon + 1)).value
        alternative =
      (((baseTremble baseline n).bayes (baseTremble_mixed baseline n)
        nativeAntichain).continuationContext
        site (fun history => nativeUtility deposit bob history.state)
          (2 * nativeHorizon + 1)).value alternative := by
  have profiles : Profile.update (sig := nativeModel.behavioralSignature)
      (sequence baseline quiet deposit n).strategy bob alternative =
        Profile.update (sig := nativeModel.behavioralSignature)
          (baseTremble baseline n).strategy bob alternative := by
    change Profile.update (sig := nativeModel.behavioralSignature)
      (Profile.update (sig := nativeModel.behavioralSignature) (baseTremble baseline n).strategy
        bob (responseLaw baseline quiet deposit n)) bob alternative = _
    exact Profile.update_idem _ _ _ _
  simp only [BehavioralAssessment.continuationContext_value, bob_belief, profiles]
  rfl

private theorem response_optimal (baseline : Profile nativeModel.behavioralSignature)
    (quiet : nativeModel.InformationSite bob) (deposit : ℝ) (n : ℕ)
    (site : nativeModel.InformationSite bob) (different : site ≠ quiet)
    (alternative : nativeModel.BehavioralPolicy bob) :
    ((sequence baseline quiet deposit n).continuationContext site
      (fun history => nativeUtility deposit bob history.state) (2 * nativeHorizon + 1)).value
        alternative ≤
      ((sequence baseline quiet deposit n).continuationContext site
        (fun history => nativeUtility deposit bob history.state) (2 * nativeHorizon + 1)).value
          (response baseline quiet deposit n) := by
  classical
  rw [bob_value, bob_value]
  have differentInfo : site.1 ≠ quiet.1 := fun same => different (Subtype.ext same)
  have same : response baseline quiet deposit n site.1 =
      bestLastPolicy (baseTremble baseline n) (baseTremble_mixed baseline n) nativeAntichain bob
        (fun history => nativeUtility deposit bob history.state) (2 * nativeHorizon) site.1 := by
    simp only [response, ite_eq_right differentInfo]
  rw [native_bob_last_decision.context_value_eq_expect _ site (native_bob_allNonterminal site)
    _ (2 * nativeHorizon) (response baseline quiet deposit n), same,
    ← native_bob_last_decision.context_value_eq_expect _ site (native_bob_allNonterminal site)
      _ (2 * nativeHorizon)
      (bestLastPolicy (baseTremble baseline n) (baseTremble_mixed baseline n) nativeAntichain bob
        (fun history => nativeUtility deposit bob history.state) (2 * nativeHorizon))]
  exact bestLastPolicy_optimal (baseTremble baseline n) (baseTremble_mixed baseline n)
    nativeAntichain bob
    (fun history => nativeUtility deposit bob history.state) (2 * nativeHorizon)
    native_bob_last_decision site (native_bob_allNonterminal site) alternative

/-- The actual bounded native game admits one consistent completion whose
receiver is rational at every information site other than the prescribed quiet
site. The latter's fixed response can therefore preserve any source mixture;
its optimality is checked using the source prior and the concrete silent run. -/
theorem exists_native_bob_completion (baseline : Profile nativeModel.behavioralSignature)
    (quiet : nativeModel.InformationSite bob) (deposit : ℝ) :
    ∃ assessment : nativeModel.BehavioralAssessment,
      (∀ who, who ≠ bob → assessment.strategy who = baseline who) ∧
      assessment.strategy bob quiet.1 = baseline bob quiet.1 ∧
      assessment.IsSequentiallyConsistent nativeAntichain ∧
      ∀ site : nativeModel.InformationSite bob, site ≠ quiet →
        assessment.IsSequentiallyRationalAt site (assessment.continuationContext site
          (fun history => nativeUtility deposit bob history.state) (2 * nativeHorizon + 1)) := by
  classical
  have mixed (n : ℕ) : (sequence baseline quiet deposit n).IsFullyMixed :=
    BehavioralAssessment.bayes_isFullyMixed _ _ _
  have bayes (n : ℕ) : BehavioralAssessment.IsBayesConsistent nativeModel
      (sequence baseline quiet deposit n) nativeAntichain :=
    BehavioralAssessment.bayes_isBayesConsistent _ _ _
  obtain ⟨original, index, increasing, originalConverges, _⟩ :=
    BehavioralAssessment.exists_sequentiallyConsistent_subsequence nativeAntichain
      (sequence baseline quiet deposit) mixed bayes
  let completedBob : nativeModel.BehavioralPolicy bob := fun info =>
    if info = quiet.1 then baseline bob info else original.strategy bob info
  let completed : nativeModel.BehavioralAssessment :=
    ⟨Profile.update (sig := nativeModel.behavioralSignature) baseline bob completedBob,
      original.belief⟩
  have baselineConverges (who : Player) (info : nativeApp.Info) :
      FinDistConvergesPointwise (fun n => (baseTremble baseline (index n)).strategy who info)
        (baseline who info) :=
    (nativeReference.perturb_strategy_converges baseline weight
      (fun n => (weight_positive n).le) (fun n => (weight_below_one n).le)
      weight_vanishes who info).subsequence increasing
  have converges : BehavioralAssessmentConvergesPointwise
      (fun n => sequence baseline quiet deposit (index n)) completed := by
    constructor
    · intro who site
      by_cases own : who = bob
      · subst who
        by_cases same : site = quiet
        · subst site
          change FinDistConvergesPointwise
            (fun n => responseLaw baseline quiet deposit (index n) quiet.1)
            (completedBob quiet.1)
          have limit := baselineConverges bob quiet.1
          change FinDistConvergesPointwise (fun n => FinDist.mix (weight (index n))
            (weight_positive (index n)).le (weight_below_one (index n)).le
            (nativeReference.strategy bob quiet.1) (baseline bob quiet.1))
            (baseline bob quiet.1) at limit
          simpa only [responseLaw, response, completedBob, ite_true] using
            limit
        · have different : site.1 ≠ quiet.1 := fun equal => same (Subtype.ext equal)
          change FinDistConvergesPointwise
            (fun n => responseLaw baseline quiet deposit (index n) site.1)
            (completedBob site.1)
          rw [show completedBob site.1 = original.strategy bob site.1 by
            simp only [completedBob, ite_eq_right different]]
          exact originalConverges.strategy bob site
      · change FinDistConvergesPointwise
          (fun n => Profile.update (sig := nativeModel.behavioralSignature)
            (baseTremble baseline (index n)).strategy bob
              (responseLaw baseline quiet deposit (index n)) who site.1)
          (Profile.update (sig := nativeModel.behavioralSignature) baseline bob
            completedBob who site.1)
        simp only [Profile.update_of_ne _ _ own]
        exact baselineConverges who site.1
    · exact originalConverges.belief
  have responsesConverge (site : nativeModel.InformationSite bob) :
      FinDistConvergesPointwise
        (fun n => response baseline quiet deposit (index n) site.1)
        (completed.strategy bob site.1) := by
    apply FinDistConvergesPointwise.of_mix_vanishing
      (nativeReference.strategy bob site.1) _ _ (fun n => weight (index n))
      (fun n => (weight_positive (index n)).le) (fun n => weight_below_one (index n))
      (weight_vanishes.comp increasing.tendsto_atTop)
    exact converges.strategy bob site
  refine ⟨completed, ?_, ?_, ?_, ?_⟩
  · intro who different
    exact Profile.update_of_ne _ _ different
  · change completedBob quiet.1 = baseline bob quiet.1
    simp only [completedBob, ite_true]
  · exact ⟨fun n => sequence baseline quiet deposit (index n),
      fun n => ⟨mixed (index n), bayes (index n)⟩, converges⟩
  · intro site different
    exact converges.rationalAt_of_optimal_responses nativeReference nativeReference_mixed site
      (fun history => nativeUtility deposit bob history.state) (2 * nativeHorizon + 1)
      (fun n => response baseline quiet deposit (index n)) responsesConverge
      (fun n alternative => response_optimal baseline quiet deposit (index n) site
        different alternative)

end VegasTests.MonitoredGuessing
