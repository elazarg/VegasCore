/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.LocalDeviation

/-! # Implementing a whole continuation deviation at one information site

Perfect recall lets a player recognize that it has passed a specified own
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
theorem switchAt_at_history (recall : M.PerfectRecall) {who : Player}
    (baseline alternative : M.BehavioralPolicy who) (site : M.InformationSite who)
    (history : E.History) :
    baseline.switchAt M alternative site (M.infoOf who history.trace) =
      if M.infoOf who history.trace = site.1 ∨ site.1 ∈ M.actedAt who history.trace
      then alternative (M.infoOf who history.trace) else baseline (M.infoOf who history.trace) := by
  classical
  simp only [BehavioralPolicy.switchAt, M.recordAt_eq_ownPlay recall,
    ← InfoSignals.actedAt_eq_map_ownPlay]

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
theorem run_switchAt_from_site (recall : M.PerfectRecall)
    (profile : ∀ player, M.BehavioralPolicy player) (who : Player)
    (site : M.InformationSite who) (alternative : M.BehavioralPolicy who)
    (history : M.InformationHistory who site.1) (fuel : Nat) :
    M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature) profile who
      ((profile who).switchAt M alternative site)) fuel history.1 =
      M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature) profile who
        alternative) fuel history.1 := by
  apply M.runBehavioralFrom_congr
  intro later reached _ player
  by_cases same : player = who
  · subst player
    simp only [Profile.update_same, M.switchAt_at_history recall]
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
theorem run_switchAt_prefix (recall : M.PerfectRecall)
    (profile : ∀ player, M.BehavioralPolicy player) (who : Player)
    (site : M.InformationSite who) (alternative : M.BehavioralPolicy who)
    (depth : Nat) (sameDepth : InformationSite.CommonDepth M site depth) :
    M.runBehavioral (Profile.update (sig := M.behavioralSignature) profile who
      ((profile who).switchAt M alternative site)) depth =
      M.runBehavioral profile depth := by
  unfold runBehavioral
  apply M.runBehavioralFrom_congr_before
  intro history _ _ before player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, M.switchAt_at_history recall]
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
theorem run_switchAt_outside_site (recall : M.PerfectRecall)
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
  intro later reached _ player
  by_cases same : player = who
  · subst player
    rw [Profile.update_same, M.switchAt_at_history recall]
    exact ite_eq_right (not_or.mpr (M.site_unvisited_after_depth who site depth sameDepth
      reached atDepth.ge outside absent))
  · simp only [Profile.update_of_ne _ _ same]

section ConditionalGain

variable (assessment : M.BehavioralAssessment) (recall : M.PerfectRecall)
  (who : Player) (site : M.InformationSite who)
  [Fintype (M.InformationHistory who site.1)]
  (depth fuel : Nat) (sameDepth : InformationSite.CommonDepth M site depth)
  (positive : 0 < M.informationMass assessment.strategy who site)
  (bayes : BehavioralAssessment.IsBayesConsistentAt M assessment who site
    (M.decisionInformationAntichain_of_perfectRecall recall who site) positive)
  (payoff : E.History → ℝ)

include recall sameDepth positive bayes in
/-- Every whole-policy conditional deviation has an information-local
initialized implementation. Its ex ante gain is exactly the probability of
reaching the selected site times its conditional continuation gain. -/
theorem switched_root_gain_eq_mass_mul_context_gain
    (alternative : M.BehavioralPolicy who) :
    (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
      assessment.strategy who ((assessment.strategy who).switchAt M alternative site))
        (depth + fuel)).expect payoff -
      (M.runBehavioral assessment.strategy (depth + fuel)).expect payoff =
    M.informationMass assessment.strategy who site *
      ((assessment.continuationContext site payoff fuel).value alternative -
        (assessment.continuationContext site payoff fuel).value (assessment.strategy who)) := by
  let switched := (assessment.strategy who).switchAt M alternative site
  let updated := Profile.update (sig := M.behavioralSignature) assessment.strategy who switched
  let gain := fun history : E.History =>
    (M.runBehavioralFrom updated fuel history).expect payoff -
      (M.runBehavioralFrom assessment.strategy fuel history).expect payoff
  have noGain (history : E.History)
      (supported : history ∈ (M.runBehavioral assessment.strategy depth).support)
      (outside : M.infoOf who history.trace ≠ site.1) : gain history = 0 := by
    by_cases terminal : E.terminal history.state
    · simp only [gain, M.runBehavioralFrom_of_terminal _ _ terminal, sub_self]
    · have atDepth := M.terminal_or_trace_length_eq_of_mem_support_runBehavioralFrom
        assessment.strategy depth E.initHistory history supported
      rcases atDepth with stopped | atDepth
      · exact False.elim (terminal stopped)
      · have actualDepth : history.trace.length = depth := by
          simpa only [initHistory, Trace.length, zero_add] using atDepth
        dsimp only [gain]
        rw [M.run_switchAt_outside_site recall assessment.strategy who site alternative
          depth sameDepth history actualDepth outside fuel, sub_self]
  obtain ⟨ownReach, shared⟩ :=
    M.commonPlayerReachAt_of_perfectRecall recall assessment.strategy who site
  have first :
      (M.runBehavioral updated (depth + fuel)).expect payoff -
          (M.runBehavioral assessment.strategy (depth + fuel)).expect payoff =
        ownReach * M.counterfactualRegret assessment.strategy who site payoff fuel alternative := by
    rw [M.rootGain_eq_prefixExpectation updated assessment.strategy payoff depth fuel
      (M.run_switchAt_prefix recall assessment.strategy who site alternative depth sameDepth)]
    rw [M.prefixExpectation_eq_ownReach_mul_counterfactualSum assessment.strategy who site
      depth sameDepth ownReach shared gain noGain]
    rw [M.counterfactualRegret_eq_sum_behavioralContinuationGain]
    congr 1
    apply Finset.sum_congr rfl
    intro history _
    dsimp only [gain]
    rw [M.run_switchAt_from_site recall assessment.strategy who site alternative history fuel]
  let antichain := M.decisionInformationAntichain_of_perfectRecall recall who site
  have belief : assessment.belief who site =
      M.bayesBelief assessment.strategy who site antichain positive := by
    apply FinDist.ext_of_prob
    intro history
    rw [M.bayesBelief_prob]
    exact bayes history
  have context (policy : M.BehavioralPolicy who) :
      (assessment.continuationContext site payoff fuel).value policy =
        M.bayesContinuationValue assessment.strategy who site antichain positive
          policy payoff fuel := by
    rw [BehavioralAssessment.continuationContext_value, belief, FinDist.expect_bind]
    rfl
  rw [first, context, context]
  exact (M.informationMass_mul_bayesGain_eq_ownReach_mul_counterfactualRegret
    assessment.strategy who site antichain positive ownReach shared alternative payoff fuel).symm

include recall sameDepth positive bayes in
/-- Ex ante optimality against all information-local policies implies actual
whole-policy sequential rationality at every positive-mass Bayes site. -/
theorem sequentiallyRationalAt_of_root_optimal
    (optimal : ∀ alternative : M.BehavioralPolicy who,
      (M.runBehavioral (Profile.update (sig := M.behavioralSignature)
        assessment.strategy who alternative) (depth + fuel)).expect payoff ≤
        (M.runBehavioral assessment.strategy (depth + fuel)).expect payoff) :
    assessment.IsSequentiallyRationalAt site (assessment.continuationContext site payoff fuel) := by
  intro alternative _
  have bound := optimal ((assessment.strategy who).switchAt M alternative site)
  have exactGain := M.switched_root_gain_eq_mass_mul_context_gain assessment recall who site
    depth fuel sameDepth positive bayes payoff alternative
  nlinarith

end ConditionalGain

end GameTheory.Protocol.InformationModel
