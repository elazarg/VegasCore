/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.OneShotDeviation
import GameTheory.Analysis.Protocol.BeliefTransport
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Support
import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheoryExtensions.Analysis.Protocol.BehavioralContinuity

/-! # Averaging local deviation bounds after an arbitrary own-policy prefix

Under decision-site recall, changing one's earlier behavior does not change the
posterior at a reached information site. The one-step gain after such a prefix
therefore obeys the baseline assessment's conditional bound. The bound may vary
by information state, allowing zero outside a selected continuation branch.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} (M : InformationModel E) [Finite E.History]
  (assessment : M.BehavioralAssessment) (recall : M.DecisionRecall)
  (mixed : assessment.IsFullyMixed)
  (bayes : BehavioralAssessment.IsBayesConsistent M assessment
    recall.decisionInformationAntichain)
  (who : Player) (alternative : M.BehavioralPolicy who)

omit [Finite E.History] in
include recall mixed bayes in
/-- The actual cut-law posterior after any own-policy deviation equals the
baseline assessment's belief at every reached common-depth decision site. -/
theorem own_prefix_conditional_eq_belief (depth : Nat) (site : M.InformationSite who)
    (sameDepth : InformationSite.CommonDepth M site depth)
    (reached : ∃ history ∈ {history | M.infoOf who history.trace = site.1},
      history ∈ (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who alternative) depth).support) :
    fiberPosterior (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
      assessment.strategy who alternative) depth)
        (fun history => M.infoOf who history.trace) site.1 =
      (assessment.belief who site).map Subtype.val := by
  classical
  let updated := Profile.update (sig := M.behavioralSignature) assessment.strategy who alternative
  let antichain := recall.decisionInformationAntichain who site
  have positive : 0 < M.informationMass updated who site := by
    rw [M.informationMass_eq_fixedDepth_toOuterMeasure updated who site depth sameDepth]
    exact pos_iff_ne_zero.mpr ((toOuterMeasure_ne_zero_iff _ _).mpr reached)
  have originalPositive := M.informationMass_pos_of_fullSupport _ mixed who site
  have originalBelief : assessment.belief who site =
      M.bayesBelief assessment.strategy who site antichain originalPositive := by
    ext history
    rw [M.bayesBelief_apply]
    exact bayes who site originalPositive history
  have sameBelief := M.bayesBelief_eq_of_eq_off updated assessment.strategy who site antichain
    (fun player different => Profile.update_of_ne _ _ different)
    (M.commonPlayerReachAt_of_decisionRecall recall updated who site)
    (M.commonPlayerReachAt_of_decisionRecall recall assessment.strategy who site)
    positive originalPositive
  rw [originalBelief, ← sameBelief,
    M.bayesBelief_map_eq_filter updated who site depth sameDepth antichain positive reached]
  exact dite_eq_left reached

include recall mixed bayes in
/-- Local conditional gain bounds remain valid after any own-policy prefix.
The allowance can be zero off a selected branch; no inverse reach probability
appears in the conclusion. -/
theorem one_step_gain_le_after_own_prefix
    [DecidableEq (M.InfoState who)]
    (clock : ∀ site : M.InformationSite who,
      ∃ depth, InformationSite.CommonDepth M site depth)
    (depth fuel : Nat) (payoff : E.History → ℝ)
    (allowance : M.InfoState who → ℝ) (nonnegative : ∀ info, 0 ≤ allowance info)
    (localBound : ∀ site : M.InformationSite who,
      InformationSite.CommonDepth M site depth →
      (assessment.truncatedContinuationContext site payoff (fuel + 1)).value
          ((assessment.strategy who).withLaw site.1 (alternative site.1)) -
        (assessment.truncatedContinuationContext site payoff (fuel + 1)).value
          (assessment.strategy who) ≤ allowance site.1) :
    expect (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
      assessment.strategy who alternative) depth) (fun history =>
        expect ((M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
          assessment.strategy who alternative) 1 history).bind
            (M.runBehavioralFrom assessment.strategy fuel)) payoff -
          expect (M.runBehavioralFrom assessment.strategy (fuel + 1) history) payoff) ≤
      expect (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who alternative) depth)
          (fun history => allowance (M.infoOf who history.trace)) := by
  classical
  let updated := Profile.update (sig := M.behavioralSignature) assessment.strategy who alternative
  let prefixLaw := M.runBehavioral updated depth
  let observation := fun history : E.History => M.infoOf who history.trace
  let gain := fun history : E.History =>
    expect ((M.runBehavioralFrom updated 1 history).bind
      (M.runBehavioralFrom assessment.strategy fuel)) payoff -
        expect (M.runBehavioralFrom assessment.strategy (fuel + 1) history) payoff
  have conditionalBound (info : M.InfoState who)
      (supported : info ∈ (prefixLaw.map observation).support) :
      expect (fiberPosterior prefixLaw observation info) gain ≤ allowance info := by
    obtain ⟨witness, witnessSupported, observed⟩ := PMF.support_map .. ▸ supported
    have meet : ∃ history ∈ observation ⁻¹' {info}, history ∈ prefixLaw.support :=
      ⟨witness, observed, witnessSupported⟩
    by_cases decision : ∃ history ∈ prefixLaw.support,
        observation history = info ∧ ¬ E.terminal history.state ∧ E.active history.state who
    · obtain ⟨history, historySupported, observed, running, active⟩ := decision
      obtain ⟨joint, jointLegal⟩ := E.progress history.state running
      have legal : E.Legal history.state joint := ⟨running, jointLegal⟩
      obtain ⟨action, chosen⟩ := (E.legalOption_of_legal legal who).exists_eq_some_of_active
        (joint who) active
      have allowed : some action ∈ M.menu who info := by
        rw [← observed]
        apply (M.menu_adequate who history.trace (some action)).mpr
        simpa only [chosen] using E.legalOption_of_legal legal who
      let site : M.InformationSite who := ⟨info, ⟨⟨history, observed⟩, running, action, allowed⟩⟩
      obtain ⟨siteDepth, uniformDepth⟩ := clock site
      have reachedDepth := M.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
        updated depth E.initHistory history historySupported
      have historyDepth : history.trace.length = depth := by
        rcases reachedDepth with stopped | length
        · exact False.elim (running stopped)
        · simpa only [initHistory, Trace.length, zero_add] using length
      have siteDepthEq : siteDepth = depth := by
        have same := uniformDepth ⟨history, observed⟩
        change history.trace.length = siteDepth at same
        omega
      have sameDepth : InformationSite.CommonDepth M site depth := siteDepthEq ▸ uniformDepth
      have posterior := M.own_prefix_conditional_eq_belief assessment recall mixed bayes who
        alternative depth site sameDepth meet
      rw [posterior, expect_map]
      calc
        _ = (assessment.truncatedContinuationContext site payoff (fuel + 1)).value
              ((assessment.strategy who).withLaw site.1 (alternative site.1)) -
            (assessment.truncatedContinuationContext site payoff (fuel + 1)).value
              (assessment.strategy who) := by
          rw [BehavioralAssessment.truncatedContinuationContext_value,
            BehavioralAssessment.truncatedContinuationContext_value, Profile.update_eq_self,
            expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _),
            expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _),
            ← expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
          apply expect_congr_on_support
          intro compatible _
          dsimp only [gain, updated, Function.comp_apply]
          rw [M.one_step_then_baseline_eq_local_law recall.decisionInformationAntichain
            assessment.strategy who alternative compatible.1 (InformationSite.active M site
                compatible) fuel, compatible.2]
        _ ≤ allowance info := localBound site sameDepth
    · have zero : expect (fiberPosterior prefixLaw observation info) gain = 0 := by
        rw [← expect_constant (fiberPosterior prefixLaw observation info) (0 : ℝ)]
        apply expect_congr_on_support
        intro history historySupported
        rw [fiberPosterior_eq_filter _ _ meet] at historySupported
        obtain ⟨observed, historySupported⟩ := (PMF.mem_support_filter_iff _).mp historySupported
        by_cases stopped : E.terminal history.state
        · simp only [gain, M.runBehavioralFrom_of_terminal _ _ stopped,
            PMF.pure_bind, sub_self]
        · have inactive : ¬ E.active history.state who := by
            intro active
            exact decision ⟨history, historySupported, observed, stopped, active⟩
          dsimp only [gain]
          rw [M.one_step_then_baseline_eq_of_inactive assessment.strategy who alternative
            history inactive fuel, sub_self]
      rw [zero]
      exact nonnegative info
  have observedFinite : (prefixLaw.map observation).support.Finite := by
    rw [PMF.support_map]
    exact (Set.toFinite _).image _
  calc
    expect prefixLaw gain =
        expect (prefixLaw.map observation) (fun info =>
          expect (fiberPosterior prefixLaw observation info) gain) := by
      conv_lhs => rw [← fiberPosterior_reconstruct prefixLaw observation]
      exact expect_bind_tower _ _ _ (payoffIntegrable_of_finite _ _)
    _ ≤ expect (prefixLaw.map observation) allowance :=
      expect_mono conditionalBound (payoffIntegrable_of_finite_support _ _ observedFinite)
        (payoffIntegrable_of_finite_support _ _ observedFinite)
    _ = _ := expect_map ..

end GameTheory.Protocol.InformationModel
