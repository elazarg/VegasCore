module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.BindingSubmission
public import Vegas.EventGraph.PrefixPolicy
public import Vegas.EventGraph.SequentialNormalization
public import Vegas.EventGraph.SequentialLaw

@[expose] public section

/-! # Source-prefix policies agree with canonical submitting execution

At an actual source prefix, padding adds no source slots and ignoring private
binding default markers loses no information in a submitting run. Therefore
prefix compilation preserves its complete canonical configuration law.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Repairing binding omissions commutes with source-prefix observation. -/
theorem submitProfile_prefixProfile (profile : graph.BehavioralProfile) :
    graph.submitProfile (graph.prefixProfile profile) =
      graph.prefixProfile (graph.submitProfile profile) := rfl

/-- At a complete source prefix without binding-default markers, the prefix
observation is exactly the ordinary rank-normalized observation. -/
theorem prefixObservation_playerObserve_of_prefix
    (who : Player) (event : graph.EventId) (config : graph.Config)
    (ordered : config.cut.IsPrefix event.val) (clean : config.NoBindingDefaults) :
    graph.prefixObservation who event (graph.playerObserve who config) =
      graph.normalizeObservation who (graph.playerObserve who config) := by
  have prefixRanks : graph.decisionPrefix event =
      graph.rankSort (config.history.map EventCompletion.event) := by
    unfold decisionPrefix rankSort
    apply List.filter_congr
    intro prior _
    simp only [config.history_exact, ordered.2]
  apply EventPlayerObservation.ext
  · exact prefixRanks
  · rfl
  · change ((graph.normalizeObservation who (graph.playerObserve who config)).ownActions.filter
      (fun completion => completion.event.val < event.val)) = _
    apply List.filter_eq_self.mpr
    intro completion member
    rw [normalizeObservation_playerObserve] at member
    obtain ⟨prior, _inside, found⟩ := List.mem_filterMap.mp member
    obtain ⟨found, _owned⟩ := Option.filter_eq_some_iff.mp found
    have actual := (completionOf_eq_some_iff config prior completion).mp found
    have completed : completion.event ∈ config.cut.completed :=
      (config.history_exact completion.event).mp
        (List.mem_map.mpr ⟨completion, actual.1, rfl⟩)
    simpa only [decide_eq_true_eq] using (ordered.2 completion.event).mp completed
  · change DefaultHistory.mk
        (((graph.decisionPrefix event).map fun prior =>
          if (graph.outputLayout prior).IsPublic then
            graph.observedDefaultOf (graph.playerObserve who config) prior else none).reverse) =
      DefaultHistory.mk (((graph.rankSort (config.history.map EventCompletion.event)).map
        (graph.observedDefaultOf (graph.playerObserve who config))).reverse)
    rw [prefixRanks]
    congr 2
    apply List.map_congr_left
    intro prior _
    by_cases isPublic : (graph.outputLayout prior).IsPublic
    · simp only [ite_eq_left isPublic]
    · rw [ite_eq_right isPublic, observedDefaultOf_playerObserve,
        clean.defaultOf_private prior isPublic]

omit [DecidableEq Player] in
private theorem ready_prefix_of_total
    (total : ∀ prior event : graph.EventId, prior.val < event.val →
      prior ∈ graph.order.predecessors event)
    (config : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event) :
    config.cut.IsPrefix event.val := by
  refine ⟨event.isLt.le, fun prior => ⟨?_, fun earlier => ready.2 (total prior event earlier)⟩⟩
  intro completed
  by_contra notBefore
  rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt notBefore) with same | later
  · exact ready.1 (Fin.ext same ▸ completed)
  · exact ready.1 (config.cut.predecessor_closed completed (total event prior later))

private theorem reachable_of_planReachable
    {profile : graph.BehavioralProfile} {scheduler : graph.PublicScheduler}
    {inputs : graph.Inputs} {config : graph.Config}
    (reach : PlanReachable profile scheduler (Config.initial inputs) config) :
    config.Reachable inputs := by
  induction reach with
  | refl => exact .initial
  | tail _ moved ih =>
    obtain ⟨event, ready, action, supported⟩ := moved.toStep
    exact .step ih event ready action _ supported

private theorem policy_congr {who : Player} (policy : graph.BehavioralPolicy who)
    (event : graph.EventId) (actor : graph.actor? event = some who)
    {left right : graph.PlayerObservation who} (same : left = right)
    (leftActive : who ∉ left.defaulted) (rightActive : who ∉ right.defaulted) :
    policy event actor left leftActive = policy event actor right rightActive := by
  subst same
  rfl

private theorem runPolicies_canonical_prefixProfile_of_total
    (total : ∀ prior event : graph.EventId, prior.val < event.val →
      prior ∈ graph.order.predecessors event)
    (profile : graph.BehavioralProfile) (submits : graph.SubmitsBindings profile)
    (inputs : graph.Inputs) :
    graph.runPolicies graph.canonicalScheduler (graph.prefixProfile profile) inputs =
      graph.runPolicies graph.canonicalScheduler profile inputs := by
  unfold runPolicies EventGraph.run
  symm
  apply runPlan_congr_profile profile (graph.prefixProfile profile) graph.canonicalScheduler
  intro config reach event ready
  have reachable := reachable_of_planReachable reach
  have clean := noBindingDefaults_of_planReachable profile submits graph.canonicalScheduler
    inputs config reach
  have observed (who : Player) :
      graph.prefixObservation who event (graph.playerObserve who config) =
        graph.playerObserve who config :=
    (prefixObservation_playerObserve_of_prefix who event config
      (ready_prefix_of_total total config event ready) clean).trans
        (graph.normalizeObservation_playerObserve_of_rankOrdered who config
          (rankSort_history_of_reachable total reachable))
  cases actor : (graph.nodes event).actor with
  | none => rw [actionLaw_of_ownerless _ _ actor, actionLaw_of_ownerless _ _ actor]
  | some who =>
    rw [actionLaw_of_actor _ _ actor, actionLaw_of_actor _ _ actor]
    by_cases inactive : who ∈ config.defaulted
    · rw [dite_eq_left inactive, dite_eq_left inactive]
    · rw [dite_eq_right inactive, dite_eq_right inactive]
      change profile who event actor _ _ = profile who event actor _ _
      exact policy_congr _ event actor (observed who).symm _ _

/-- Prefix compilation preserves the full canonical law of every submitting
profile on any graph. Publication kernels may use arbitrary observations. -/
theorem runPolicies_canonical_prefixProfile
    (profile : graph.BehavioralProfile) (submits : graph.SubmitsBindings profile)
    (inputs : graph.Inputs) :
    graph.runPolicies graph.canonicalScheduler (graph.prefixProfile profile) inputs =
      graph.runPolicies graph.canonicalScheduler profile inputs := by
  calc
    graph.runPolicies graph.canonicalScheduler (graph.prefixProfile profile) inputs =
        (graph.sequentialize.runPolicies graph.sequentialize.canonicalScheduler
          (graph.sequentialize.prefixProfile profile) inputs).map graph.fromSequentialConfig :=
      (graph.canonical_fromSequential_config_law (graph.sequentialize.prefixProfile profile)
        inputs).symm
    _ = (graph.sequentialize.runPolicies graph.sequentialize.canonicalScheduler profile
        inputs).map graph.fromSequentialConfig := by
      rw [runPolicies_canonical_prefixProfile_of_total (graph := graph.sequentialize)
        (fun prior event earlier =>
          (EventOrder.sequential.mem_predecessors prior event).mpr earlier) profile submits inputs]
    _ = graph.runPolicies graph.canonicalScheduler profile inputs :=
      graph.canonical_fromSequential_config_law profile inputs

private theorem terminalOutcomes_canonical_prefixProfile
    (profile : graph.BehavioralProfile) (submits : graph.SubmitsBindings profile)
    (inputs : graph.Inputs) :
    graph.terminalOutcomes graph.canonicalScheduler (graph.prefixProfile profile) inputs =
      graph.terminalOutcomes graph.canonicalScheduler profile inputs := by
  have keyLaw :
      (graph.terminalOutcomes graph.canonicalScheduler (graph.prefixProfile profile) inputs).map
          Subtype.val =
        (graph.terminalOutcomes graph.canonicalScheduler profile inputs).map Subtype.val := by
    rw [terminalOutcomes_map_val, terminalOutcomes_map_val,
      runPolicies_canonical_prefixProfile profile submits inputs]
  have same := bind_eq_of_map_key_eq Subtype.val Set.univ _ _ (Set.subset_univ _)
    (Set.subset_univ _) keyLaw PMF.pure
    (fun left _ right _ equal => congrArg PMF.pure (Subtype.ext equal))
  simpa only [PMF.bind_pure] using same

/-- Adding terminality certificates and mixing the inputs preserves the same
canonical profile identity. -/
theorem gameForm_canonical_prefixProfile
    (profile : graph.BehavioralProfile) (submits : graph.SubmitsBindings profile)
    (inputs : PMF graph.Inputs) :
    (graph.gameForm inputs graph.canonicalScheduler).play (graph.prefixProfile profile) =
      (graph.gameForm inputs graph.canonicalScheduler).play profile := by
  apply bind_congr_on_support _
  intro initial _
  exact terminalOutcomes_canonical_prefixProfile profile submits initial

end Vegas.EventGraph
