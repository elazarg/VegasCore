/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ContinuationDecision
import GameTheoryExtensions.Analysis.Protocol.DecisionExperiment
import GameTheoryExtensions.Math.Probability.Support

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

variable {State Signal Action : Type} [Nonempty Action] [Finite State] [Finite Action]

omit [Finite State] [Finite Action] in
/-- Terminal play of the decision arena, certified by its horizon. -/
theorem certificate (prior : PMF State) : (arena (Action := Action) prior).WellFoundedHistories :=
  (bounded prior).wellFoundedHistories

/-- The terminal decision is a continuation decision of terminal play. -/
def decision (prior : PMF State) (observe : State → Signal)
    (site : (model (Action := Action) prior observe).InformationSite ())
    (utility : State → Action → ℝ) :
    (model prior observe).ContinuationDecision
      (fun _ history => payoff utility history.state)
      ((model prior observe).runBehavioralTerminalFrom (certificate prior)) State Action where
  player := ()
  site := site
  state history := latent prior history.1.state
  response profile := response prior observe (profile ()) (siteSignal prior observe site)
  response_finite _ := Set.toFinite _
  reward := utility
  policy action := policy prior observe (fun _ => PMF.pure action)
  history_value profile history := by
    rw [InformationModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded _ _
      (bounded prior)]
    obtain ⟨state, supported, same, observed⟩ := history_at_site prior observe site history
    have signalEq := Option.some.inj (observed.trans (site_signal prior observe site))
    have law := congrArg (fun law => expect law (payoff utility))
      (run_decision prior observe profile state supported)
    rw [same]
    change _ = expect (response prior observe (profile ()) (siteSignal prior observe site))
      (utility state)
    simpa only [expect_map, Function.comp_def, signalEq, payoff, latent] using law
  realize profile action := by
    simp only [Profile.update_same, response_policy]

def biasedBit : PMF Bool :=
  mix (1 / 4) (by norm_num) (by norm_num) (PMF.pure false) (PMF.pure true)

theorem biasedBit_full : FullSupport biasedBit := by
  intro bit
  apply pmf_toReal_pos_iff.mp
  cases bit <;> norm_num [biasedBit, mix_apply_toReal, toReal_pure_apply]

def hiddenSite : (model (Action := Bool) biasedBit (fun _ => ())).InformationSite () :=
  site biasedBit (fun _ => ()) false (biasedBit_full false)

def guess : (model biasedBit (fun _ => ())).ContinuationDecision
    (fun _ history => payoff (reportUtility id) history.state)
    ((model biasedBit (fun _ => ())).runBehavioralTerminalFrom (certificate biasedBit))
    Bool Bool :=
  decision biasedBit (fun _ => ()) hiddenSite (reportUtility id)

def hiddenHistory (bit : Bool) :
    (model (Action := Bool) biasedBit (fun _ => ())).InformationHistory () hiddenSite.1 :=
  ⟨decisionHistory biasedBit bit (biasedBit_full bit), rfl⟩

theorem canonical_posterior (original : Unit → PMF Bool) :
    guess.posterior (assessment biasedBit (fun _ => ()) original) = biasedBit := by
  classical
  ext bit
  calc
    _ = ((assessment biasedBit (fun _ => ()) original).belief () hiddenSite) (hiddenHistory bit) :=
      pmf_map_apply_of_injective _
        (information_state_injective biasedBit (fun _ => ()) hiddenSite) (hiddenHistory bit)
    _ = biasedBit bit := by
      change (InformationModel.bayesAssessment _ (reference biasedBit (fun _ => ())).strategy
        (reference_mixed biasedBit (fun _ => ())) (antichain biasedBit (fun _ => ()))).belief ()
          hiddenSite (hiddenHistory bit) = _
      rw [InformationModel.bayesAssessment, InformationModel.bayesBelief_apply,
        information_mass]
      change (model biasedBit (fun _ => ())).historyReachWeight _
          (decisionHistory biasedBit bit (biasedBit_full bit)) /
        biasedBit.toOuterMeasure ((fun _ : Bool => ()) ⁻¹'
          {siteSignal biasedBit (fun _ => ()) hiddenSite}) = _
      rw [reach_decision]
      have all : (fun _ : Bool => ()) ⁻¹' {siteSignal biasedBit (fun _ => ()) hiddenSite} =
          Set.univ := by
        ext state
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ]
      have mass : biasedBit.toOuterMeasure Set.univ = 1 := by
        rw [PMF.toOuterMeasure_apply, Set.indicator_univ]
        exact biasedBit.tsum_coe
      rw [all, mass, div_one]

/-- A non-degenerate posterior prefers `true`; certainty about the latent
state is not a premise of the continuation theorem. -/
theorem posterior_rewards
    (assessment : (model (Action := Bool) biasedBit (fun _ => ())).BehavioralAssessment)
    (posterior : guess.posterior assessment = biasedBit) :
    guess.expectedReward assessment false = 1 / 4 ∧
      guess.expectedReward assessment true = 3 / 4 := by
  simp only [InformationModel.ContinuationDecision.expectedReward, posterior]
  norm_num [guess, decision, reportUtility, biasedBit, expect_mix_of_finite,
    expect_pure]

/-- A response using the minority guess cannot be rational for this fixed
payoff, even though both latent states have positive probability. -/
theorem minority_guess_not_rational
    (assessment : (model (Action := Bool) biasedBit (fun _ => ())).BehavioralAssessment)
    (posterior : guess.posterior assessment = biasedBit)
    (minority : false ∈ (guess.response assessment.strategy).support) :
    ¬ assessment.IsSequentiallyRational (certificate biasedBit)
        (fun _ history => payoff (reportUtility id) history.state) := by
  apply guess.not_rational_of_supported_inferior assessment false true minority
  obtain ⟨low, high⟩ := posterior_rewards assessment posterior
  rw [low, high]
  norm_num

/-- The posterior premise above is attained by consistent assessments of the
actual protocol. The always-minority strategy is nevertheless not rational. -/
theorem consistent_minority_not_rational :
    (assessment biasedBit (fun _ => ()) (fun _ => PMF.pure false)).IsSequentiallyConsistent
        (antichain biasedBit (fun _ => ())) ∧
      ¬ (assessment biasedBit (fun _ => ()) (fun _ => PMF.pure false)).IsSequentiallyRational
        (certificate biasedBit) (fun _ history => payoff (reportUtility id) history.state) := by
  refine ⟨assessment_consistent _ _ _, minority_guess_not_rational _ (canonical_posterior _) ?_⟩
  change false ∈ (response biasedBit (fun _ => ())
    (policy biasedBit (fun _ => ()) (fun _ => PMF.pure false)) _).support
  rw [response_policy]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

end GameTheoryExtensionsTests.ContinuationDecision
