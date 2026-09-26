/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.OneShotDeviation
import GameTheoryExtensions.Analysis.Protocol.CounterfactualBeliefs
import GameTheoryExtensions.Analysis.Protocol.FixedDepthBayes

/-! # Averaging local deviation bounds after an arbitrary own-policy prefix

Under perfect recall, changing one's earlier behavior does not change the
posterior at a reached information site. The one-step gain after such a prefix
therefore obeys the baseline assessment's conditional bound. The bound may vary
by information state, allowing zero outside a selected continuation branch.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} (M : InformationModel E) [Finite E.History]
  [∀ who (site : M.InformationSite who), Fintype (M.InformationHistory who site.1)]
  (assessment : M.BehavioralAssessment) (recall : M.PerfectRecall)
  (mixed : assessment.IsFullyMixed)
  (bayes : BehavioralAssessment.IsBayesConsistent M assessment
    (M.decisionInformationAntichain_of_perfectRecall recall))
  (who : Player) (alternative : M.BehavioralPolicy who)

include recall mixed bayes in
/-- The actual cut-law posterior after any own-policy deviation equals the
baseline assessment's belief at every reached common-depth decision site. -/
theorem own_prefix_conditional_eq_belief (depth : Nat) (site : M.InformationSite who)
    (sameDepth : InformationSite.CommonDepth M site depth)
    (reached : ∃ history ∈ {history | M.infoOf who history.trace = site.1},
      history ∈ (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who alternative) depth).support) :
    (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
      assessment.strategy who alternative) depth).condOnFibre
        (fun history => M.infoOf who history.trace) site.1 =
      (assessment.belief who site).map Subtype.val := by
  classical
  let updated := Profile.update (sig := M.behavioralSignature) assessment.strategy who alternative
  let antichain := M.decisionInformationAntichain_of_perfectRecall recall who site
  have positive : 0 < M.informationMass updated who site := by
    rw [M.informationMass_eq_fixedDepth_probOf updated who site depth sameDepth]
    exact FinDist.probOf_pos reached
  have originalPositive := mixed.informationMass_pos who site
  have originalBelief : assessment.belief who site =
      M.bayesBelief assessment.strategy who site antichain originalPositive := by
    apply FinDist.ext_of_prob
    intro history
    rw [M.bayesBelief_prob]
    exact bayes who site originalPositive history
  have sameBelief := M.bayesBelief_eq_of_eq_off updated assessment.strategy who site antichain
    (fun player different => Profile.update_of_ne _ _ different)
    (M.commonPlayerReachAt_of_perfectRecall recall updated who site)
    (M.commonPlayerReachAt_of_perfectRecall recall assessment.strategy who site)
    positive originalPositive
  rw [originalBelief, ← sameBelief,
    M.bayesBelief_map_eq_condOn updated who site depth sameDepth antichain positive reached]
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
      (assessment.continuationContext site payoff (fuel + 1)).value
          ((assessment.strategy who).withLaw site.1 (alternative site.1)) -
        (assessment.continuationContext site payoff (fuel + 1)).value
          (assessment.strategy who) ≤ allowance site.1) :
    (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
      assessment.strategy who alternative) depth).expect (fun history =>
        ((M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
          assessment.strategy who alternative) 1 history).bind
            (M.runBehavioralFrom assessment.strategy fuel)).expect payoff -
          (M.runBehavioralFrom assessment.strategy (fuel + 1) history).expect payoff) ≤
      (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who alternative) depth).expect
          (fun history => allowance (M.infoOf who history.trace)) := by
  classical
  let updated := Profile.update (sig := M.behavioralSignature) assessment.strategy who alternative
  let prefixLaw := M.runBehavioral updated depth
  let observation := fun history : E.History => M.infoOf who history.trace
  let gain := fun history : E.History =>
    ((M.runBehavioralFrom updated 1 history).bind
      (M.runBehavioralFrom assessment.strategy fuel)).expect payoff -
        (M.runBehavioralFrom assessment.strategy (fuel + 1) history).expect payoff
  have conditionalBound (info : M.InfoState who)
      (supported : info ∈ (prefixLaw.map observation).support) :
      (prefixLaw.condOnFibre observation info).expect gain ≤ allowance info := by
    obtain ⟨witness, witnessSupported, observed⟩ := FinDist.support_map .. ▸ supported
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
      rw [posterior, FinDist.expect_map]
      calc
        _ = (assessment.continuationContext site payoff (fuel + 1)).value
              ((assessment.strategy who).withLaw site.1 (alternative site.1)) -
            (assessment.continuationContext site payoff (fuel + 1)).value
              (assessment.strategy who) := by
          rw [BehavioralAssessment.continuationContext_value,
            BehavioralAssessment.continuationContext_value, Profile.update_eq_self,
            FinDist.expect_bind, FinDist.expect_bind, ← FinDist.expect_sub]
          apply FinDist.expect_congr
          intro compatible _
          dsimp only [gain]
          rw [M.one_step_then_baseline_eq_local_law recall assessment.strategy who alternative
            compatible.1 (InformationSite.active M site compatible) fuel, compatible.2]
        _ ≤ allowance info := localBound site sameDepth
    · have zero : (prefixLaw.condOnFibre observation info).expect gain = 0 := by
        rw [← FinDist.expect_const (prefixLaw.condOnFibre observation info) (0 : ℝ)]
        apply FinDist.expect_congr
        intro history historySupported
        rw [FinDist.condOnFibre, dite_eq_left meet] at historySupported
        obtain ⟨observed, historySupported⟩ := FinDist.support_condOn _ _ _ historySupported
        by_cases stopped : E.terminal history.state
        · simp only [gain, M.runBehavioralFrom_of_terminal _ _ stopped,
            FinDist.pure_bind, sub_self]
        · have inactive : ¬ E.active history.state who := by
            intro active
            exact decision ⟨history, historySupported, observed, stopped, active⟩
          dsimp only [gain]
          rw [M.one_step_then_baseline_eq_of_inactive assessment.strategy who alternative
            history inactive fuel, sub_self]
      rw [zero]
      exact nonnegative info
  calc
    prefixLaw.expect gain =
        (prefixLaw.map observation).expect (fun info =>
          (prefixLaw.condOnFibre observation info).expect gain) := by
      conv_lhs => rw [prefixLaw.eq_bind_condOnFibre observation]
      exact FinDist.expect_bind ..
    _ ≤ (prefixLaw.map observation).expect allowance :=
      FinDist.expect_mono conditionalBound
    _ = _ := FinDist.expect_map ..

end GameTheory.Protocol.InformationModel
