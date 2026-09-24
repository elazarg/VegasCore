/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceBeliefs
import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion

/-! # One consistent source assessment with fair hidden-binding beliefs

One subsequence of the common fully mixed assessment sequence supplies all
beliefs. The resulting strategy is exactly the prescribed profile. This file
proves consistency and the conditional fairness needed by guessing incentives;
sequential rationality is a separate obligation.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter

def FairGuessBeliefs (Claim : Type) [Fintype Claim]
    (assessment : (model Claim).BehavioralAssessment) : Prop :=
  ∀ (who : Player) (site : (model Claim).InformationSite who)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView),
    site.1 = some (past, view) →
    ((who = carol ∧ view.application.visit = some 1) ∨
      (who = bob ∧ view.application.visit = some 2)) → NoPublicAlice view →
    (assessment.belief who site).probOf {history | hasAliceBit false history.1.state} =
      (assessment.belief who site).probOf {history | hasAliceBit true history.1.state}

theorem tremble_fairGuessBeliefs (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1) :
    FairGuessBeliefs Claim (tremble Claim defaultClaim weight positive atMostOne) := by
  intro who site past view observed decision hidden
  rcases decision with ⟨rfl, granted⟩ | ⟨rfl, granted⟩
  · exact carol_tremble_fair Claim defaultClaim weight positive atMostOne
      site past view observed granted hidden
  · exact bob_tremble_fair Claim defaultClaim weight positive atMostOne
      site past view observed granted hidden

theorem fairGuessBeliefs_limit (Claim : Type) [Fintype Claim]
    (sequence : Nat → (model Claim).BehavioralAssessment)
    (assessment : (model Claim).BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment)
    (fair : ∀ n, FairGuessBeliefs Claim (sequence n)) : FairGuessBeliefs Claim assessment := by
  classical
  intro who site past view observed decision hidden
  have eventLimit (event : Set ((model Claim).InformationHistory who site.1)) :
      Tendsto (fun n => ((sequence n).belief who site).probOf event) atTop
        (nhds ((assessment.belief who site).probOf event)) := by
    simpa only [FinDist.expect_indicator_eq_probOf] using
      (converges.belief who site).expect (fun history => if history ∈ event then (1 : ℝ) else 0)
  have first := eventLimit {history | hasAliceBit false history.1.state}
  have second := eventLimit {history | hasAliceBit true history.1.state}
  have same : (fun n => (sequence n).belief who site |>.probOf
      {history | hasAliceBit false history.1.state}) =
      fun n => (sequence n).belief who site |>.probOf
        {history | hasAliceBit true history.1.state} := by
    funext n
    exact fair n who site past view observed decision hidden
  rw [same] at first
  exact tendsto_nhds_unique first second

theorem exists_consistent_fair_assessment (Claim : Type) [Fintype Claim] (defaultClaim : Claim) :
    ∃ assessment : (model Claim).BehavioralAssessment,
      assessment.strategy = profile Claim defaultClaim ∧
      assessment.IsSequentiallyConsistent
        ((menu Claim).decisionInformationAntichain (FinDist.pure initial)
          horizon (scheduler Claim)) ∧ FairGuessBeliefs Claim assessment := by
  let weight (n : Nat) : ℝ := 1 / ((n : ℝ) + 1)
  have positive (n : Nat) : 0 < weight n := by dsimp [weight]; positivity
  have atMostOne (n : Nat) : weight n ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have vanishes : Tendsto weight atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let sequence n := tremble Claim defaultClaim (weight n) (positive n) (atMostOne n)
  obtain ⟨assessment, strategy, index, _increasing, converges, consistent⟩ :=
    InformationModel.BehavioralAssessment.exists_consistent_completion_subsequence
      ((menu Claim).decisionInformationAntichain (FinDist.pure initial)
        horizon (scheduler Claim))
      (profile Claim defaultClaim) sequence
      (fun n => tremble_fullyMixed Claim defaultClaim (weight n) (positive n) (atMostOne n))
      (fun n => tremble_bayes Claim defaultClaim (weight n) (positive n) (atMostOne n))
      (fun who site => (menu Claim).perturbedAssessment_strategy_converges
        (FinDist.pure initial) horizon (scheduler Claim) (profile Claim defaultClaim)
        weight positive atMostOne vanishes who site.1)
  refine ⟨assessment, strategy, consistent, ?_⟩
  exact fairGuessBeliefs_limit Claim (fun n => sequence (index n)) assessment converges
    (fun n => tremble_fairGuessBeliefs Claim defaultClaim (weight (index n))
      (positive (index n)) (atMostOne (index n)))

end VegasTests.SelectiveAssociation.NamedSource
