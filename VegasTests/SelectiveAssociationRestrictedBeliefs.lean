/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedPrefixExecution
import VegasTests.SelectiveAssociationRestrictedProbability
import VegasTests.SelectiveAssociationRestrictedPrefixPosterior
import VegasTests.SelectiveAssociationRestrictedGuessOutcome
import GameTheoryExtensions.Analysis.Protocol.FixedDepthBayes
import GameTheoryExtensions.Math.Probability.ConditionalComparison

/-! # Native Bayes beliefs from actual response-prefix probabilities

The belief comparison is transported from the original protocol's response
law at the exact depth of each guessing information set. Division uses the
same information-event probability for both successful Alice bindings.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

def tremble (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1) :
    model.BehavioralAssessment :=
  menu.perturbedAssessment (FinDist.pure nativeInitial) nativeHorizon scheduler profile
    weight positive atMostOne

theorem history_observe (who : Player) (history : arena.History) :
    model.infoOf who history.trace = app.observe who history.state :=
  menu.info (FinDist.pure nativeInitial) nativeHorizon scheduler who history.trace

theorem information_depth (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (event : nativeGraph.EventId)
    (granted : view.application.publicView.serviceGrant = some event)
    (history : model.InformationHistory who (some (past, view))) :
    history.1.trace.length = Prefix.decisionDepth event := by
  obtain ⟨control, stateEq, active, _, observed⟩ := information_control who past view history
  rcases history with ⟨⟨state, trace⟩, historyInfo⟩
  change state = some control at stateEq
  subst state
  have grant : control.execution.application.serviceGrant = some event := by
    rw [← observed] at granted
    exact granted
  exact Prefix.decision_depth event control trace who active grant

theorem carol_history_joint (players : Profile model.behavioralSignature)
    (input : List app.PlayerEntry × app.PlayerView) (bit : Bool) :
    (model.runBehavioral players 13).probOf
      {history | model.infoOf carol history.trace = some input ∧ hasAliceBit bit history.state} =
    (Prefix.carolLaw (menu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon scheduler
      players)).probOf {responses |
        ((Prefix.carolInput responses).recall carol,
          (Prefix.carolInput responses).observe app carol) = input ∧
        aliceBindingRef.get? (Prefix.carolInput responses).application.config.store =
          some (.success bit)} := by
  have mapped := congrArg (fun law : FinDist app.ProtocolState =>
    law.probOf {state | app.observe carol state = some input ∧ hasAliceBit bit state})
      (Prefix.carol_history_law players)
  simp only [FinDist.probOf_map, Set.preimage_ofPred_eq, history_observe, Prefix.carolControl,
    ReactiveApplication.observe, ite_true, Option.some.injEq, hasAliceBit, Option.elim_some]
      at mapped ⊢
  exact mapped

theorem bob_history_joint (players : Profile model.behavioralSignature)
    (input : List app.PlayerEntry × app.PlayerView) (bit : Bool) :
    (model.runBehavioral players 20).probOf
      {history | model.infoOf bob history.trace = some input ∧ hasAliceBit bit history.state} =
    (Prefix.bobLaw (menu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon scheduler
      players)).probOf {responses |
        ((Prefix.bobInput responses).recall bob,
          (Prefix.bobInput responses).observe app bob) = input ∧
        aliceBindingRef.get? (Prefix.bobInput responses).application.config.store =
          some (.success bit)} := by
  have mapped := congrArg (fun law : FinDist app.ProtocolState =>
    law.probOf {state | app.observe bob state = some input ∧ hasAliceBit bit state})
      (Prefix.bob_history_law players)
  simp only [FinDist.probOf_map, Set.preimage_ofPred_eq, history_observe, Prefix.bobControl,
    ReactiveApplication.observe, ite_true, Option.some.injEq, hasAliceBit, Option.elim_some]
      at mapped ⊢
  exact mapped

theorem tremble_bit_belief_ratio (weight : ℝ) (positive : 0 < weight)
    (atMostOne : weight ≤ 1) (who : Player) (site : model.InformationSite who) (depth : Nat)
    (sameDepth : ∀ history : model.InformationHistory who site.1,
      history.1.trace.length = depth) (bit : Bool) :
    ((tremble weight positive atMostOne).belief who site).probOf
        {history | hasAliceBit bit history.1.state} =
      (model.runBehavioral (tremble weight positive atMostOne).strategy depth).probOf
        {history | model.infoOf who history.trace = site.1 ∧ hasAliceBit bit history.state} /
      (model.runBehavioral (tremble weight positive atMostOne).strategy depth).probOf
        {history | model.infoOf who history.trace = site.1} := by
  have mixed := menu.perturbedAssessment_fullyMixed (FinDist.pure nativeInitial) nativeHorizon
    scheduler profile weight positive atMostOne
  have meet : ∃ history ∈ {history | model.infoOf who history.trace = site.1},
      history ∈ (model.runBehavioral (tremble weight positive atMostOne).strategy
        depth).support := by
    obtain ⟨history, _⟩ := site.2
    refine ⟨history.1, history.2, ?_⟩
    have reached := mixed.history_supported history.1.trace
    rwa [sameDepth history] at reached
  have conditioned := model.bayesBelief_map_eq_condOn (tremble weight positive atMostOne).strategy
    who site depth sameDepth
    (menu.decisionInformationAntichain (FinDist.pure nativeInitial) nativeHorizon
      scheduler who site)
    (mixed.informationMass_pos who site) meet
  have beliefEq : (tremble weight positive atMostOne).belief who site =
      model.bayesBelief (tremble weight positive atMostOne).strategy who site
        (menu.decisionInformationAntichain (FinDist.pure nativeInitial) nativeHorizon
          scheduler who site) (mixed.informationMass_pos who site) := rfl
  rw [← beliefEq] at conditioned
  have events := congrArg (fun law : FinDist arena.History =>
    law.probOf {history | hasAliceBit bit history.state}) conditioned
  rw [FinDist.probOf_map, FinDist.probOf_condOn_eq_inter] at events
  exact events

theorem tremble_bit_belief_le (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1)
    (who : Player) (site : model.InformationSite who) (depth : Nat)
    (sameDepth : ∀ history : model.InformationHistory who site.1,
      history.1.trace.length = depth)
    (joint : (model.runBehavioral (tremble weight positive atMostOne).strategy depth).probOf
        {history | model.infoOf who history.trace = site.1 ∧ hasAliceBit true history.state} ≤
      (model.runBehavioral (tremble weight positive atMostOne).strategy depth).probOf
        {history | model.infoOf who history.trace = site.1 ∧ hasAliceBit false history.state}) :
    ((tremble weight positive atMostOne).belief who site).probOf
      {history | hasAliceBit true history.1.state} ≤
        ((tremble weight positive atMostOne).belief who site).probOf
          {history | hasAliceBit false history.1.state} := by
  rw [tremble_bit_belief_ratio weight positive atMostOne who site depth sameDepth,
    tremble_bit_belief_ratio weight positive atMostOne who site depth sameDepth]
  exact div_le_div_of_nonneg_right joint ENNReal.toReal_nonneg

def GuessBeliefs (assessment : model.BehavioralAssessment) : Prop :=
  ∀ (who : Player) (site : model.InformationSite who)
    (past : List app.PlayerEntry) (view : app.PlayerView),
    site.1 = some (past, view) → who ≠ alice →
    view.application.publicView.serviceGrant = some (nativeBindingEvent who) →
    publicGuess view = false →
    (assessment.belief who site).probOf {history | hasAliceBit true history.1.state} ≤
      (assessment.belief who site).probOf {history | hasAliceBit false history.1.state}

theorem tremble_guessBeliefs_of_prefix_comparison (weight : ℝ) (positive : 0 < weight)
    (atMostOne : weight ≤ 1)
    (carolComparison : ∀ (past : List app.PlayerEntry) (view : app.PlayerView),
      publicGuess view = false →
      (Prefix.carolLaw (Prefix.mixed weight positive.le atMostOne)).probOf {responses |
        ((Prefix.carolInput responses).recall carol,
          (Prefix.carolInput responses).observe app carol) = (past, view) ∧
        aliceBindingRef.get? (Prefix.carolInput responses).application.config.store =
          some (.success true)} ≤
      (Prefix.carolLaw (Prefix.mixed weight positive.le atMostOne)).probOf {responses |
        ((Prefix.carolInput responses).recall carol,
          (Prefix.carolInput responses).observe app carol) = (past, view) ∧
        aliceBindingRef.get? (Prefix.carolInput responses).application.config.store =
          some (.success false)})
    (bobComparison : ∀ (past : List app.PlayerEntry) (view : app.PlayerView),
      publicGuess view = false →
      (Prefix.bobLaw (Prefix.mixed weight positive.le atMostOne)).probOf {responses |
        ((Prefix.bobInput responses).recall bob,
          (Prefix.bobInput responses).observe app bob) = (past, view) ∧
        aliceBindingRef.get? (Prefix.bobInput responses).application.config.store =
          some (.success true)} ≤
      (Prefix.bobLaw (Prefix.mixed weight positive.le atMostOne)).probOf {responses |
        ((Prefix.bobInput responses).recall bob,
          (Prefix.bobInput responses).observe app bob) = (past, view) ∧
        aliceBindingRef.get? (Prefix.bobInput responses).application.config.store =
          some (.success false)}) : GuessBeliefs (tremble weight positive atMostOne) := by
  intro who site past view observed guesser granted hidden
  fin_cases who
  · exact False.elim (guesser rfl)
  · apply tremble_bit_belief_le weight positive atMostOne bob site 20
      (fun history => (information_depth bob past view bobBinding granted
        ⟨history.1, history.2.trans observed⟩).trans Prefix.bob_depth)
    rw [observed, bob_history_joint, bob_history_joint]
    simp only [tremble, Prefix.decode_perturbed]
    exact bobComparison past view hidden
  · apply tremble_bit_belief_le weight positive atMostOne carol site 13
      (fun history => (information_depth carol past view carolBinding granted
        ⟨history.1, history.2.trans observed⟩).trans Prefix.carol_depth)
    rw [observed, carol_history_joint, carol_history_joint]
    simp only [tremble, Prefix.decode_perturbed]
    exact carolComparison past view hidden

theorem guessBeliefs_limit (sequence : Nat → model.BehavioralAssessment)
    (assessment : model.BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment)
    (comparison : ∀ n, GuessBeliefs (sequence n)) : GuessBeliefs assessment := by
  intro who site past view observed guesser granted hidden
  exact (converges.belief who site).probOf_le
    {history | hasAliceBit true history.1.state} {history | hasAliceBit false history.1.state}
      (fun n => comparison n who site past view observed guesser granted hidden)

/-- One common subsequence supplies all limiting beliefs. The hypothesis
is the concrete posterior comparison for every positive perturbation. -/
theorem exists_consistent_guess_assessment_of_tremble
    (comparison : ∀ (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1),
      GuessBeliefs (tremble weight positive atMostOne)) :
    ∃ assessment : model.BehavioralAssessment,
      assessment.strategy = profile ∧ assessment.IsSequentiallyConsistent
        (menu.decisionInformationAntichain (FinDist.pure nativeInitial) nativeHorizon scheduler) ∧
      GuessBeliefs assessment := by
  let weight (n : Nat) : ℝ := 1 / ((n : ℝ) + 1)
  have positive (n : Nat) : 0 < weight n := by dsimp [weight]; positivity
  have atMostOne (n : Nat) : weight n ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have vanishes : Filter.Tendsto weight Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let sequence n := tremble (weight n) (positive n) (atMostOne n)
  obtain ⟨assessment, strategy, index, _increasing, converges, consistent⟩ :=
    InformationModel.BehavioralAssessment.exists_consistent_completion_subsequence
      (menu.decisionInformationAntichain (FinDist.pure nativeInitial) nativeHorizon scheduler)
      profile sequence
      (fun n => menu.perturbedAssessment_fullyMixed (FinDist.pure nativeInitial) nativeHorizon
        scheduler profile (weight n) (positive n) (atMostOne n))
      (fun n => menu.perturbedAssessment_bayes (FinDist.pure nativeInitial) nativeHorizon
        scheduler profile (weight n) (positive n) (atMostOne n))
      (fun who site => menu.perturbedAssessment_strategy_converges (FinDist.pure nativeInitial)
        nativeHorizon scheduler profile weight positive atMostOne vanishes who site.1)
  exact ⟨assessment, strategy, consistent,
    guessBeliefs_limit (fun n => sequence (index n)) assessment converges
      (fun n => comparison (weight (index n)) (positive (index n)) (atMostOne (index n)))⟩

/-- A consistent assessment of the complete native game with the posterior
comparisons required at both guessing decisions. All beliefs arise from the
same fully mixed sequence; no site is assigned a posterior independently. -/
theorem exists_consistent_guess_assessment :
    ∃ assessment : model.BehavioralAssessment,
      assessment.strategy = profile ∧ assessment.IsSequentiallyConsistent
        (menu.decisionInformationAntichain (FinDist.pure nativeInitial) nativeHorizon scheduler) ∧
      GuessBeliefs assessment := by
  apply exists_consistent_guess_assessment_of_tremble
  intro weight positive atMostOne
  exact tremble_guessBeliefs_of_prefix_comparison weight positive atMostOne
    (Prefix.carol_joint_le weight positive atMostOne)
    (Prefix.bob_joint_le weight positive atMostOne)

end VegasTests.SelectiveAssociation.Restricted
