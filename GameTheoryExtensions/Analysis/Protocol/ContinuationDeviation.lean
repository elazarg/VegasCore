/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.LocalDeviation
import GameTheoryExtensions.Math.Probability.Support

/-! # Implementing a whole continuation deviation at one information site

Decision-site recall lets a player recognize that it has passed a specified own
decision. A policy can therefore switch to an arbitrary alternative precisely
at and after that decision, while preserving play on the other branches.
The switch uses the player's information record, never the hidden history.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type} {E : ExecutionProtocol Player} (M : InformationModel E)

/-- A complete own-action record only mentions strictly earlier information
states. This supplies trace-depth facts without exposing histories to policies. -/
theorem actedAt_has_earlier_history (who : Player) {state : E.State}
    (trace : E.Trace state) {info : M.InfoState who} (recorded : info ∈ M.actedAt who trace) :
    ∃ history : E.History,
      M.infoOf who history.trace = info ∧ history.trace.length < trace.length := by
  induction trace with
  | start => cases recorded
  | extend prior joint legal realized ih =>
      cases chosen : joint who with
      | none =>
          simp only [InfoSignals.actedAt, chosen] at recorded
          obtain ⟨history, observed, shorter⟩ := ih recorded
          exact ⟨history, observed, by simp only [Trace.length]; omega⟩
      | some action =>
          simp only [InfoSignals.actedAt, chosen, List.mem_cons] at recorded
          rcases recorded with same | recorded
          · exact ⟨⟨_, prior⟩, same.symm, by simp only [Trace.length]; omega⟩
          · obtain ⟨history, observed, shorter⟩ := ih recorded
            exact ⟨history, observed, by simp only [Trace.length]; omega⟩

/-- A common-depth site cannot already occur in the player's action record at
or before that depth. -/
theorem site_not_recorded_before_depth (who : Player) (site : M.InformationSite who)
    (depth : Nat) (sameDepth : InformationSite.CommonDepth M site depth)
    (history : E.History) (early : history.trace.length ≤ depth) :
    site.1 ∉ M.actedAt who history.trace := by
  intro recorded
  obtain ⟨earlier, observed, shorter⟩ := M.actedAt_has_earlier_history who history.trace recorded
  have atDepth := sameDepth ⟨earlier, observed⟩
  change earlier.trace.length = depth at atDepth
  omega

open scoped Classical in
/-- The player changes its policy only after recognizing the selected own
decision. The recorded-information test is a function of its information state. -/
def BehavioralPolicy.switchAt {who : Player} (baseline alternative : M.BehavioralPolicy who)
    (site : M.InformationSite who) : M.BehavioralPolicy who := fun info =>
  if info = site.1 ∨ site.1 ∈ (M.recordAt who info).map Prod.fst
  then alternative info else baseline info

open scoped Classical in
theorem switchAt_at_history (recall : M.DecisionRecall) {who : Player}
    (baseline alternative : M.BehavioralPolicy who) (site : M.InformationSite who)
    (history : E.History) (running : ¬ E.terminal history.state) :
    baseline.switchAt M alternative site (M.infoOf who history.trace) =
      if M.infoOf who history.trace = site.1 ∨ site.1 ∈ M.actedAt who history.trace
      then alternative (M.infoOf who history.trace) else baseline (M.infoOf who history.trace) := by
  classical
  by_cases active : E.active history.state who
  · simp only [BehavioralPolicy.switchAt,
      recall.recordAt_eq_ownPlay_of_active who history running active,
      ← InfoSignals.actedAt_eq_map_ownPlay]
  · have same := M.behavioral_eq_of_not_active baseline alternative history.trace active
    unfold BehavioralPolicy.switchAt
    split <;> split <;> first | rfl | exact same | exact same.symm

theorem site_recorded_after_step {who : Player} (site : M.InformationSite who)
    (history : M.InformationHistory who site.1)
    {joint : ∀ player, Option (E.Action player)} (legal : E.Legal history.1.state joint)
    {target : E.State} (realized : target ∈ (E.step history.1.state ⟨joint, legal⟩).support)
    {fuel : Nat} {later : E.History}
    (reached : E.ReachesWithin fuel (history.1.extend legal realized) later) :
    site.1 ∈ M.actedAt who later.trace := by
  obtain ⟨action, chosen⟩ := (E.legalOption_of_legal legal who).exists_eq_some_of_active
    (joint who) (InformationSite.active M site history)
  apply (M.actedAt_isSuffix_of_reachesWithin who reached).subset
  simp [History.extend, InfoSignals.actedAt, chosen, history.2]

variable [Fintype Player] [DecidableEq Player]

/-- From the selected site onward, the switched policy implements the entire
alternative behavioral policy, including all later decisions of the player. -/
theorem run_switchAt_from_site (recall : M.DecisionRecall)
    (profile : ∀ player, M.BehavioralPolicy player) (who : Player)
    (site : M.InformationSite who) (alternative : M.BehavioralPolicy who)
    (history : M.InformationHistory who site.1) (fuel : Nat) :
    M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature) profile who
      ((profile who).switchAt M alternative site)) fuel history.1 =
      M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature) profile who
        alternative) fuel history.1 := by
  apply M.runBehavioralFrom_congr
  intro later reached running player
  by_cases same : player = who
  · subst player
    simp only [Profile.update_same, M.switchAt_at_history recall _ _ _ later running]
    apply ite_eq_left
    cases reached with
    | refl => exact Or.inl history.2
    | step joint legal realized rest =>
        exact Or.inr (M.site_recorded_after_step site history legal realized rest)
  · simp only [Profile.update_of_ne _ _ same]

omit [Fintype Player] [DecidableEq Player] in
/-- Once the decision depth has passed on another branch, no later history
can enter the selected site or acquire it in the own-action record. -/
theorem site_unvisited_after_depth (who : Player) (site : M.InformationSite who)
    (depth : Nat) (sameDepth : InformationSite.CommonDepth M site depth)
    {fuel : Nat} {first last : E.History} (reached : E.ReachesWithin fuel first last) :
    depth ≤ first.trace.length → M.infoOf who first.trace ≠ site.1 →
      site.1 ∉ M.actedAt who first.trace →
        M.infoOf who last.trace ≠ site.1 ∧ site.1 ∉ M.actedAt who last.trace := by
  induction reached with
  | refl => exact fun _ different absent => ⟨different, absent⟩
  | @step fuel first last joint legal target realized rest ih =>
      intro after different absent
      apply ih
      · simp only [History.extend, Trace.length]
        omega
      · intro same
        have atDepth := sameDepth ⟨first.extend legal realized, same⟩
        change first.trace.length + 1 = depth at atDepth
        omega
      · cases chosen : joint who <;>
          simp [History.extend, InfoSignals.actedAt, chosen, Ne.symm different, absent]

/-- The switch leaves the entire initialized prefix before the selected
decision depth unchanged. -/
theorem run_switchAt_prefix (recall : M.DecisionRecall)
    (profile : ∀ player, M.BehavioralPolicy player) (who : Player)
    (site : M.InformationSite who) (alternative : M.BehavioralPolicy who)
    (depth : Nat) (sameDepth : InformationSite.CommonDepth M site depth) :
    M.runBehavioral (Profile.update (sig := M.behavioralSignature) profile who
      ((profile who).switchAt M alternative site)) depth =
      M.runBehavioral profile depth := by
  unfold runBehavioral
  apply M.runBehavioralFrom_congr_before
  intro history _ running before player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, M.switchAt_at_history recall _ _ _ history running]
    apply ite_eq_right
    have early : history.trace.length < depth := by
      simpa only [initHistory, Trace.length, zero_add] using before
    have absent := M.site_not_recorded_before_depth who site depth sameDepth history early.le
    have different : M.infoOf who history.trace ≠ site.1 := by
      intro observed
      have atDepth := sameDepth ⟨history, observed⟩
      change history.trace.length = depth at atDepth
      omega
    exact not_or.mpr ⟨different, absent⟩
  · simp only [Profile.update_of_ne _ _ same]

/-- At the decision-depth cut, the entire continuation on every other branch
is unchanged, not only its immediate action or public result. -/
theorem run_switchAt_outside_site (recall : M.DecisionRecall)
    (profile : ∀ player, M.BehavioralPolicy player) (who : Player)
    (site : M.InformationSite who) (alternative : M.BehavioralPolicy who)
    (depth : Nat) (sameDepth : InformationSite.CommonDepth M site depth)
    (history : E.History) (atDepth : history.trace.length = depth)
    (outside : M.infoOf who history.trace ≠ site.1) (fuel : Nat) :
    M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature) profile who
      ((profile who).switchAt M alternative site)) fuel history =
      M.runBehavioralFrom profile fuel history := by
  have absent := M.site_not_recorded_before_depth who site depth sameDepth history atDepth.le
  apply M.runBehavioralFrom_congr
  intro later reached running player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, M.switchAt_at_history recall _ _ _ later running]
    exact ite_eq_right (not_or.mpr (M.site_unvisited_after_depth who site depth sameDepth
      reached atDepth.ge outside absent))
  · simp only [Profile.update_of_ne _ _ same]

section ConditionalGain

variable (assessment : M.BehavioralAssessment) (recall : M.DecisionRecall)
  (who : Player) (site : M.InformationSite who)
  [Finite (M.InformationHistory who site.1)]
  (depth fuel : Nat) (sameDepth : InformationSite.CommonDepth M site depth)
  (positive : 0 < M.informationMass assessment.strategy who site)
  (bayes : BehavioralAssessment.IsBayesConsistentAt M assessment who site
    (recall.decisionInformationAntichain who site) positive)
  (payoff : E.History → ℝ)

omit [DecidableEq Player] [Finite (M.InformationHistory who site.1)] in
include sameDepth in
/-- A decision history with positive reach lies in the support of the prefix
law at the site's depth. -/
private theorem mem_prefix_support_of_reach (strategy : ∀ player, M.BehavioralPolicy player)
    (history : M.InformationHistory who site.1)
    (reached : M.historyReachWeight strategy history.1 ≠ 0) :
    history.1 ∈ (M.runBehavioral strategy depth).support := by
  have atDepth := sameDepth history
  change history.1.trace.length = depth at atDepth
  rw [PMF.mem_support_iff]
  simpa only [historyReachWeight, atDepth] using reached

omit [DecidableEq Player] [Finite (M.InformationHistory who site.1)] in
include bayes in
/-- A history the Bayes belief supports has positive reach. -/
private theorem reach_ne_zero_of_belief (history : M.InformationHistory who site.1)
    (supported : history ∈ (assessment.belief who site).support) :
    M.historyReachWeight assessment.strategy history.1 ≠ 0 := by
  intro zero
  rw [PMF.mem_support_iff, bayes history, zero, ENNReal.zero_div] at supported
  exact supported rfl

include recall sameDepth bayes in
/-- Root integrability of the switched deviation and of the baseline gives a
finite continuation value at the selected site. -/
private theorem context_integrableAt_of_root (alternative : M.BehavioralPolicy who)
    (switchedIntegrable : PayoffIntegrable (M.runBehavioral
      (Profile.update (sig := M.behavioralSignature) assessment.strategy who
        ((assessment.strategy who).switchAt M alternative site)) (depth + fuel)) payoff)
    (baselineIntegrable : PayoffIntegrable
      (M.runBehavioral assessment.strategy (depth + fuel)) payoff) :
    (assessment.continuationContext site payoff fuel).IntegrableAt alternative := by
  obtain ⟨_, _, conditional, _⟩ := M.rootGain_eq_prefixExpectation
    (Profile.update (sig := M.behavioralSignature) assessment.strategy who
      ((assessment.strategy who).switchAt M alternative site))
    assessment.strategy payoff depth fuel
    (M.run_switchAt_prefix recall assessment.strategy who site alternative depth sameDepth)
    switchedIntegrable baselineIntegrable
  change PayoffIntegrable ((assessment.belief who site).bind fun history =>
    M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature) assessment.strategy who
      alternative) fuel history.1) payoff
  apply payoffIntegrable_bind_of_finite_support _ _ _ (Set.toFinite _)
  intro history supported
  have inPrefix := M.mem_prefix_support_of_reach who site depth sameDepth assessment.strategy
    history (M.reach_ne_zero_of_belief assessment recall who site positive bayes history supported)
  have integrable := (conditional history.1 inPrefix).1
  rwa [M.run_switchAt_from_site recall assessment.strategy who site alternative history fuel]
    at integrable

include recall sameDepth positive bayes in
/-- Every whole-policy conditional deviation has an information-local
initialized implementation. When its root payoff and the baseline's are
integrable, its ex ante gain is exactly the probability of reaching the
selected site times its conditional continuation gain. -/
theorem switched_root_gain_eq_mass_mul_context_gain
    (alternative : M.BehavioralPolicy who)
    (switchedIntegrable : PayoffIntegrable (M.runBehavioral
      (Profile.update (sig := M.behavioralSignature) assessment.strategy who
        ((assessment.strategy who).switchAt M alternative site)) (depth + fuel)) payoff)
    (baselineIntegrable : PayoffIntegrable
      (M.runBehavioral assessment.strategy (depth + fuel)) payoff) :
    expect (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
      assessment.strategy who ((assessment.strategy who).switchAt M alternative site))
        (depth + fuel)) payoff -
      expect (M.runBehavioral assessment.strategy (depth + fuel)) payoff =
    (M.informationMass assessment.strategy who site).toReal *
      ((assessment.continuationContext site payoff fuel).value alternative -
        (assessment.continuationContext site payoff fuel).value (assessment.strategy who)) := by
  let _ : Fintype (M.InformationHistory who site.1) := Fintype.ofFinite _
  obtain ⟨gain, _, conditional, rootGain⟩ := M.rootGain_eq_prefixExpectation
    (Profile.update (sig := M.behavioralSignature) assessment.strategy who
      ((assessment.strategy who).switchAt M alternative site))
    assessment.strategy payoff depth fuel
    (M.run_switchAt_prefix recall assessment.strategy who site alternative depth sameDepth)
    switchedIntegrable baselineIntegrable
  obtain ⟨ownReach, shared⟩ :=
    M.commonPlayerReachAt_of_decisionRecall recall assessment.strategy who site
  have ownPositive := M.commonPlayerReach_pos ownReach shared positive
  have noGain (history : E.History)
      (supported : history ∈ (M.runBehavioral assessment.strategy depth).support)
      (outside : M.infoOf who history.trace ≠ site.1) : gain history = 0 := by
    rw [(conditional history supported).2.2]
    by_cases terminal : E.terminal history.state
    · simp only [M.runBehavioralFrom_of_terminal _ _ terminal, sub_self]
    · rcases M.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
        assessment.strategy depth E.initHistory history supported with stopped | atDepth
      · exact False.elim (terminal stopped)
      · have actualDepth : history.trace.length = depth := by
          simpa only [initHistory, Trace.length, zero_add] using atDepth
        rw [M.run_switchAt_outside_site recall assessment.strategy who site alternative
          depth sameDepth history actualDepth outside fuel, sub_self]
  let localGain (history : M.InformationHistory who site.1) : ℝ :=
    expect (M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who alternative) fuel history.1) payoff -
      expect (M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who (assessment.strategy who)) fuel history.1) payoff
  have localSame (history : M.InformationHistory who site.1)
      (supported : history.1 ∈ (M.runBehavioral assessment.strategy depth).support) :
      gain history.1 = localGain history := by
    rw [(conditional history.1 supported).2.2,
      M.run_switchAt_from_site recall assessment.strategy who site alternative history fuel]
    simp only [localGain, Profile.update_eq_self]
  have inPrefix (history : M.InformationHistory who site.1)
      (nonzero : M.counterfactualReachProbability assessment.strategy who history.1.trace ≠ 0) :
      history.1 ∈ (M.runBehavioral assessment.strategy depth).support := by
    apply M.mem_prefix_support_of_reach who site depth sameDepth assessment.strategy history
    intro zero
    have factor := M.historyReachProbability_eq_player_mul_counterfactual
      assessment.strategy who history.1.trace
    rw [shared history] at factor
    change (M.historyReachWeight assessment.strategy history.1).toReal = _ at factor
    rw [zero, ENNReal.toReal_zero] at factor
    exact nonzero ((mul_eq_zero.mp factor.symm).resolve_left ownPositive.ne')
  have alternativeIntegrable : CounterfactualContinuationIntegrable M assessment.strategy who
      site alternative payoff fuel := by
    intro history nonzero
    have integrable := (conditional history.1 (inPrefix history nonzero)).1
    rwa [M.run_switchAt_from_site recall assessment.strategy who site alternative history fuel]
      at integrable
  have incumbentIntegrable : CounterfactualContinuationIntegrable M assessment.strategy who
      site (assessment.strategy who) payoff fuel := by
    intro history nonzero
    rw [Profile.update_eq_self]
    exact (conditional history.1 (inPrefix history nonzero)).2.1
  have belief : assessment.belief who site = M.bayesBelief assessment.strategy who site
      (recall.decisionInformationAntichain who site) positive := by
    ext history
    rw [M.bayesBelief_apply]
    exact bayes history
  have context (policy : M.BehavioralPolicy who) :
      (assessment.continuationContext site payoff fuel).value policy =
        M.bayesContinuationValue assessment.strategy who site
          (recall.decisionInformationAntichain who site) positive policy payoff fuel := by
    rw [BehavioralAssessment.continuationContext_value, belief]
    rfl
  calc
    _ = expect (M.runBehavioral assessment.strategy depth) gain := rootGain
    _ = ownReach * ∑ history : M.InformationHistory who site.1,
          M.counterfactualReachProbability assessment.strategy who history.1.trace *
            localGain history :=
      M.prefixExpectation_eq_ownReach_mul_counterfactualSum assessment.strategy who site
        depth sameDepth ownReach shared gain localGain noGain localSame
    _ = ownReach * M.counterfactualRegret assessment.strategy who site payoff fuel
          alternative := by
      rw [M.counterfactualRegret_eq_sum_behavioralContinuationGain]
    _ = _ := by
      rw [context, context]
      exact (M.informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret
        assessment.strategy who site (recall.decisionInformationAntichain who site) positive
        ownReach shared alternative payoff fuel alternativeIntegrable incumbentIntegrable).symm

include recall sameDepth positive bayes in
/-- Ex ante optimality against all information-local policies implies actual
whole-policy sequential rationality at every positive-mass Bayes site, when
every own deviation has a finite expected root payoff. -/
theorem sequentiallyRationalAt_of_root_optimal
    (integrable : ∀ policy : M.BehavioralPolicy who,
      PayoffIntegrable (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who policy) (depth + fuel)) payoff)
    (optimal : ∀ alternative : M.BehavioralPolicy who,
      expect (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who alternative) (depth + fuel)) payoff ≤
        expect (M.runBehavioral assessment.strategy (depth + fuel)) payoff) :
    assessment.IsSequentiallyRationalAt site (assessment.continuationContext site payoff fuel) := by
  have baseline := integrable (assessment.strategy who)
  rw [Profile.update_eq_self] at baseline
  have contextIntegrable (policy : M.BehavioralPolicy who) :=
    M.context_integrableAt_of_root assessment recall who site depth fuel sameDepth positive bayes
      payoff policy (integrable _) baseline
  refine (Context.isLocallyOptimal_iff_of_integrable (contextIntegrable _)
    fun alternative _ => contextIntegrable alternative).mpr fun alternative _ => ?_
  have bound := optimal ((assessment.strategy who).switchAt M alternative site)
  have exactGain := M.switched_root_gain_eq_mass_mul_context_gain assessment recall who site
    depth fuel sameDepth positive bayes payoff alternative (integrable _) baseline
  have massPositive : 0 < (M.informationMass assessment.strategy who site).toReal :=
    ENNReal.toReal_pos positive.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top
      (M.informationMass_le_one _ who site (recall.decisionInformationAntichain who site)))
  nlinarith

end ConditionalGain

end GameTheory.Protocol.InformationModel
