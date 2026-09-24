/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ContinuationDecision
import GameTheoryExtensions.Analysis.Protocol.DecisionExperiment

/-! # Partial information at an actual protocol decision

The generic local reduction applies to every information site of the existing
terminal experiment protocol, with arbitrary state-dependent rewards. The
biased-bit example keeps both states possible and has a unique optimal answer;
its obstruction uses one fixed payoff rather than opposite utility parameters.
-/

noncomputable section

namespace GameTheoryExtensionsTests.ContinuationDecision

open GameTheory GameTheory.Protocol GameTheory.DecisionExperiment
open GameTheory.Math.Probability

open GameTheory.DecisionExperiment.Protocol

variable {State Signal Action : Type} [Nonempty Action]

def decision (prior : FinDist State) (observe : State → Signal)
    (site : (model (Action := Action) prior observe).InformationSite ())
    (utility : State → Action → ℝ) :
    (model prior observe).ContinuationDecision
      (fun _ history => payoff utility history.state) 2 State Action where
  player := ()
  site := site
  state history := latent prior history.1.state
  response profile := response prior observe (profile ()) (siteSignal prior observe site)
  reward := utility
  policy action := policy prior observe (fun _ => FinDist.pure action)
  history_value profile history := by
    obtain ⟨state, supported, same, observed⟩ := history_at_site prior observe site history
    have signalEq := Option.some.inj (observed.trans (site_signal prior observe site))
    have law := congrArg (fun law => law.expect (payoff utility))
      (run_decision prior observe profile state supported)
    rw [same]
    change _ = (response prior observe (profile ()) (siteSignal prior observe site)).expect
      (utility state)
    simpa only [FinDist.expect_map, signalEq, payoff, latent] using law
  realize profile action := by
    simp only [Profile.update_same, response_policy]

def biasedBit : FinDist Bool :=
  FinDist.mix (1 / 4) (by norm_num) (by norm_num) (FinDist.pure false) (FinDist.pure true)

theorem biasedBit_full : biasedBit.FullSupport := by
  intro bit
  apply FinDist.prob_pos_iff.mp
  cases bit <;> norm_num [biasedBit, FinDist.prob_mix, FinDist.prob_pure_of_ne]

def hiddenSite : (model (Action := Bool) biasedBit (fun _ => ())).InformationSite () :=
  site biasedBit (fun _ => ()) false (biasedBit_full false)

def guess : (model biasedBit (fun _ => ())).ContinuationDecision
    (fun _ history => payoff (reportUtility id) history.state) 2 Bool Bool :=
  decision biasedBit (fun _ => ()) hiddenSite (reportUtility id)

def hiddenHistory (bit : Bool) :
    (model (Action := Bool) biasedBit (fun _ => ())).InformationHistory () hiddenSite.1 :=
  ⟨decisionHistory biasedBit bit (biasedBit_full bit), rfl⟩

theorem canonical_posterior (original : Unit → FinDist Bool) :
    guess.posterior (assessment biasedBit (fun _ => ()) original) = biasedBit := by
  classical
  apply FinDist.ext_of_prob
  intro bit
  calc
    _ = ((assessment biasedBit (fun _ => ()) original).belief () hiddenSite).prob
        (hiddenHistory bit) := by
      exact FinDist.prob_map_of_injective guess.state
        (information_state_injective biasedBit (fun _ => ()) hiddenSite) _ (hiddenHistory bit)
    _ = biasedBit.prob bit := by
      change (((reference biasedBit (fun _ => ())).bayes
        (reference_mixed biasedBit (fun _ => ()))
        (antichain biasedBit (fun _ => ()))).belief () hiddenSite).prob (hiddenHistory bit) = _
      rw [InformationModel.BehavioralAssessment.bayes, InformationModel.bayesBelief_prob,
        information_mass]
      change (model biasedBit (fun _ => ())).historyReachProbability _
        (decisionHistory biasedBit bit (biasedBit_full bit)) /
          biasedBit.probOf ((fun _ : Bool => ()) ⁻¹'
            {siteSignal biasedBit (fun _ => ()) hiddenSite}) = _
      rw [reach_decision]
      have all : (fun _ : Bool => ()) ⁻¹' {siteSignal biasedBit (fun _ => ()) hiddenSite} =
          Set.univ := by
        ext state
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ]
      have mass : biasedBit.probOf Set.univ = 1 := by
        rw [← FinDist.expect_indicator_eq_probOf]
        simp
      rw [all, mass, div_one]

/-- A non-degenerate posterior prefers `true`; certainty about the latent
state is not a premise of the continuation theorem. -/
theorem posterior_rewards
    (assessment : (model (Action := Bool) biasedBit (fun _ => ())).BehavioralAssessment)
    (posterior : guess.posterior assessment = biasedBit) :
    guess.expectedReward assessment false = 1 / 4 ∧
      guess.expectedReward assessment true = 3 / 4 := by
  simp only [InformationModel.ContinuationDecision.expectedReward, posterior]
  norm_num [guess, decision, reportUtility, biasedBit, FinDist.expect_mix,
    FinDist.expect_pure]

/-- A response using the minority guess cannot be rational for this fixed
payoff, even though both latent states have positive probability. -/
theorem minority_guess_not_rational
    (assessment : (model (Action := Bool) biasedBit (fun _ => ())).BehavioralAssessment)
    (posterior : guess.posterior assessment = biasedBit)
    (minority : false ∈ (guess.response assessment.strategy).support) :
    ¬ assessment.IsSequentiallyRationalWithin
      (fun _ history => payoff (reportUtility id) history.state) 2 := by
  apply guess.not_rational_of_supported_inferior assessment false true minority
  obtain ⟨low, high⟩ := posterior_rewards assessment posterior
  rw [low, high]
  norm_num

/-- The posterior premise above is attained by consistent assessments of the
actual protocol. The always-minority strategy is nevertheless not rational. -/
theorem consistent_minority_not_rational :
    (assessment biasedBit (fun _ => ()) (fun _ => FinDist.pure false)).IsSequentiallyConsistent
        (antichain biasedBit (fun _ => ())) ∧
      ¬ (assessment biasedBit (fun _ => ())
        (fun _ => FinDist.pure false)).IsSequentiallyRationalWithin
        (fun _ history => payoff (reportUtility id) history.state) 2 := by
  refine ⟨assessment_consistent _ _ _, minority_guess_not_rational _ (canonical_posterior _) ?_⟩
  change false ∈ (response biasedBit (fun _ => ())
    (policy biasedBit (fun _ => ()) (fun _ => FinDist.pure false)) _).support
  rw [response_policy]
  exact FinDist.mem_support_pure.mpr rfl

end GameTheoryExtensionsTests.ContinuationDecision
