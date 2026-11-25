module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.PrefixReplay
public import Vegas.EventGraph.BindingSubmission
public import Vegas.EventGraph.RevealDeviation

@[expose] public section

/-! # Deviations against prescribed source-prefix policies

A submitting deviation may use the full chronological observation. After fixing
a public scheduling tape, its source-prefix replay has exactly the same run.
Predrawing the tape and applying scheduler erasure expresses its final law as a
mixture of canonical source-prefix deviations. The comparison retains the full
store and each event's original completion record.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Profile congruence only needs agreement at events the scheduler actually selects. -/
theorem runPlan_congr_profile_selected (left right : graph.BehavioralProfile)
    (scheduler : graph.PublicScheduler) :
    ∀ fuel (config : graph.Config),
      (∀ next, PlanReachable left scheduler config next →
        ∀ (notTerminal : ¬ next.cut.Terminal)
          (selected : {event : graph.EventId // event ∈ next.cut.enabled}),
          selected ∈ (scheduler (graph.publicObserve next) next.cut.enabled
            (enabled_nonempty_of_not_terminal next notTerminal)).support →
          actionDistribution left next selected.1 = actionDistribution right next selected.1) →
      graph.runPlan (graph.policyPlan left scheduler) fuel config =
        graph.runPlan (graph.policyPlan right scheduler) fuel config := by
  intro fuel
  induction fuel with
  | zero => intro config _; rfl
  | succ fuel ih =>
    intro config agree
    by_cases terminal : config.cut.Terminal
    · simp only [EventGraph.runPlan, dite_eq_left terminal]
    · rw [runPlan_policyPlan_succ left scheduler fuel config terminal,
        runPlan_policyPlan_succ right scheduler fuel config terminal]
      apply bind_congr_on_support _
      intro selected chosen
      unfold eventStep
      rw [← agree config Relation.ReflTransGen.refl terminal selected chosen]
      apply bind_congr_on_support _
      intro next member
      apply ih next
      intro later reach
      exact agree later (Relation.ReflTransGen.head ⟨terminal, selected, chosen,
        by unfold eventStep; exact member⟩ reach)

/-- Replay a binding at the actual observation of a reachable configuration where that same
binding is selected next. Publications retain the supplied observation-oblivious kernel. -/
def prefixReplayPolicy (profile : graph.BehavioralProfile)
    (assignment : graph.ScheduleSite → Option graph.EventId) (who : Player)
    (policy : graph.BehavioralPolicy who) : graph.BehavioralPolicy who :=
  fun event actor observation active =>
    open Classical in
    if _publication : (graph.outputLayout event).IsPublication then
      policy event actor observation active
    else if found : ∃ (inputs : graph.Inputs) (config : graph.Config),
        PlanReachable profile (assignedScheduler assignment) (Config.initial inputs) config ∧
          ∃ ready : config.cut.Ready event,
            assignedSelection assignment config ready.not_terminal = event ∧
            graph.prefixObservation who event (graph.playerObserve who config) = observation ∧
            who ∉ (graph.playerObserve who config).defaulted then
      policy event actor (graph.playerObserve who found.choose_spec.choose)
        found.choose_spec.choose_spec.2.choose_spec.2.2
    else policy event actor observation active

theorem PolicyObliviousAtPublications.prefix {who : Player}
    {policy : graph.BehavioralPolicy who}
    (oblivious : graph.PolicyObliviousAtPublications who policy) :
    graph.PolicyObliviousAtPublications who (graph.prefixPolicy who policy) := by
  intro event actor publication left right leftActive rightActive
  exact oblivious event actor publication _ _ _ _

theorem PolicyObliviousAtPublications.prefixReplay {profile : graph.BehavioralProfile}
    {assignment : graph.ScheduleSite → Option graph.EventId} {who : Player}
    {policy : graph.BehavioralPolicy who}
    (oblivious : graph.PolicyObliviousAtPublications who policy) :
    graph.PolicyObliviousAtPublications who (prefixReplayPolicy profile assignment who policy) := by
  intro event actor publication left right leftActive rightActive
  simpa only [prefixReplayPolicy, dite_eq_left publication] using
    oblivious event actor publication left right leftActive rightActive

theorem PolicySubmitsBindings.prefix {who : Player} {policy : graph.BehavioralPolicy who}
    (submits : graph.PolicySubmitsBindings who policy) :
    graph.PolicySubmitsBindings who (graph.prefixPolicy who policy) := by
  intro event actor observation active action supported
  exact submits event actor _ _ action supported

theorem PolicySubmitsBindings.prefixReplay {profile : graph.BehavioralProfile}
    {assignment : graph.ScheduleSite → Option graph.EventId} {who : Player}
    {policy : graph.BehavioralPolicy who} (submits : graph.PolicySubmitsBindings who policy) :
    graph.PolicySubmitsBindings who (prefixReplayPolicy profile assignment who policy) := by
  intro event actor observation active action supported
  unfold prefixReplayPolicy at supported
  split at supported
  · exact submits event actor _ _ action supported
  · split at supported <;> exact submits event actor _ _ action supported

theorem SubmitsBindings.prefix {profile : graph.BehavioralProfile}
    (submits : graph.SubmitsBindings profile) :
    graph.SubmitsBindings (graph.prefixProfile profile) :=
  fun who => (submits who).prefix

theorem prefixProfile_update (profile : graph.BehavioralProfile) (who : Player)
    (policy : graph.BehavioralPolicy who) :
    graph.prefixProfile (Profile.update (sig := graph.gameSignature) profile who policy) =
      Profile.update (sig := graph.gameSignature) (graph.prefixProfile profile) who
        (graph.prefixPolicy who policy) := by
  funext owner
  by_cases same : owner = who
  · subst owner
    simp only [prefixProfile, Profile.update_same]
  · simp only [prefixProfile, Profile.update_of_ne _ _ same]

private theorem policy_congr {who : Player} (policy : graph.BehavioralPolicy who)
    (event : graph.EventId) (actor : graph.actor? event = some who)
    {left right : graph.PlayerObservation who} (same : left = right)
    (leftActive : who ∉ left.defaulted) (rightActive : who ∉ right.defaulted) :
    policy event actor left leftActive = policy event actor right rightActive := by
  subst same
  rfl

/-- Under an assigned scheduler, prefix replay changes no actual configuration law for a
submitting profile whose focal player ignores the observation at publications. -/
theorem runPolicies_prefixReplay (relaxed : graph.RevealRelaxedOrdered)
    (profile : graph.BehavioralProfile) (submits : graph.SubmitsBindings profile)
    (assignment : graph.ScheduleSite → Option graph.EventId) (who : Player)
    (oblivious : graph.PolicyObliviousAtPublications who (profile who))
    (inputs : graph.Inputs) :
    graph.runPolicies (assignedScheduler assignment)
        (Profile.update (sig := graph.gameSignature) profile who
          (graph.prefixPolicy who (prefixReplayPolicy profile assignment who (profile who))))
        inputs =
      graph.runPolicies (assignedScheduler assignment) profile inputs := by
  unfold EventGraph.runPolicies EventGraph.run
  symm
  apply runPlan_congr_profile_selected
  intro config reach notTerminal selected chosen
  have ready := (EventOrder.Cut.mem_enabled _ _).mp selected.2
  have selectedEq : assignedSelection assignment config notTerminal = selected.1 := by
    change selected ∈ ((PMF.pure (assignment (scheduleSite config))).map _).support at chosen
    rw [PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff] at chosen
    exact congrArg Subtype.val chosen.symm
  cases ownerEq : (graph.nodes selected.1).actor with
  | none => rw [actionDistribution_of_ownerless _ _ ownerEq, actionDistribution_of_ownerless _ _
    ownerEq]
  | some owner =>
    rw [actionDistribution_of_actor _ _ ownerEq, actionDistribution_of_actor _ _ ownerEq]
    by_cases inactive : owner ∈ config.defaulted
    · rw [dite_eq_left inactive, dite_eq_left inactive]
    rw [dite_eq_right inactive, dite_eq_right inactive]
    by_cases same : owner = who
    · subst owner
      rw [Profile.update_same]
      change _ = prefixReplayPolicy profile assignment who (profile who) selected.1 ownerEq _ _
      by_cases publication : (graph.outputLayout selected.1).IsPublication
      · simp only [prefixReplayPolicy, dite_eq_left publication]
        exact oblivious selected.1 ownerEq publication _ _ _ _
      · unfold prefixReplayPolicy
        rw [dite_eq_right publication]
        have found : ∃ (initial : graph.Inputs) (other : graph.Config),
            PlanReachable profile (assignedScheduler assignment) (Config.initial initial) other ∧
              ∃ ready : other.cut.Ready selected.1,
                assignedSelection assignment other ready.not_terminal = selected.1 ∧
                graph.prefixObservation who selected.1 (graph.playerObserve who other) =
                  graph.prefixObservation who selected.1 (graph.playerObserve who config) ∧
                who ∉ (graph.playerObserve who other).defaulted :=
          ⟨inputs, config, reach, ready, selectedEq, rfl, inactive⟩
        rw [dite_eq_left found]
        have otherReach := found.choose_spec.choose_spec.1
        have otherReady := found.choose_spec.choose_spec.2.choose
        have otherSelected := found.choose_spec.choose_spec.2.choose_spec.1
        have observed := found.choose_spec.choose_spec.2.choose_spec.2.1
        have observations := assigned_playerObserve_eq_of_prefix reach otherReach relaxed who
          selected.1 ownerEq publication ready otherReady selectedEq otherSelected
          (noBindingDefaults_of_planReachable profile submits (assignedScheduler assignment) inputs
            config reach).defaultOf_private
          (noBindingDefaults_of_planReachable profile submits (assignedScheduler assignment)
            found.choose found.choose_spec.choose otherReach).defaultOf_private observed.symm
        exact policy_congr (profile who) selected.1 ownerEq observations _ _
    · rw [Profile.update_of_ne _ _ same]

/-- A submitting deviation against a prefix-oblivious profile has, under every public scheduler,
a mixture of canonical prefix-deviation laws on the complete order-free final key. -/
theorem RevealRelaxedOrdered.prefix_deviation_mixture (relaxed : graph.RevealRelaxedOrdered)
    (finite : graph.FiniteActions) (profile : graph.BehavioralProfile)
    (submits : graph.SubmitsBindings profile) (oblivious : graph.ObliviousAtPublications profile)
    (who : Player) (policy : graph.BehavioralPolicy who)
    (policySubmits : graph.PolicySubmitsBindings who policy)
    (policyOblivious : graph.PolicyObliviousAtPublications who policy)
    (scheduler : graph.PublicScheduler) (inputs : PMF graph.Inputs)
    (finiteInputs : inputs.support.Finite) :
    ∃ mixture : PMF (graph.ScheduleSite → Option graph.EventId),
      (inputs.bind (graph.runPolicies scheduler
          (Profile.update (sig := graph.gameSignature) (graph.prefixProfile profile) who
            policy))).map runKey =
        mixture.bind fun assignment =>
          (inputs.bind (graph.runPolicies graph.canonicalScheduler
            (graph.prefixProfile (Profile.update (sig := graph.gameSignature) profile who
              (prefixReplayPolicy (Profile.update (sig := graph.gameSignature)
                (graph.prefixProfile profile) who policy) assignment who policy))))).map
            runKey := by
  let deviating := Profile.update (sig := graph.gameSignature) (graph.prefixProfile profile)
    who policy
  have deviatingSubmits : graph.SubmitsBindings deviating :=
    SubmitsBindings.update graph submits.prefix who policy policySubmits
  obtain ⟨mixture, law⟩ := exists_scheduler_mixture deviating
    (finite.profileFiniteSupport deviating) scheduler inputs finiteInputs
  refine ⟨mixture, ?_⟩
  rw [bind_congr_on_support _ fun initial supported => (law initial supported).symm,
    PMF.bind_comm, PMF.map_bind]
  apply bind_congr_on_support _
  intro assignment _
  let replayed := prefixReplayPolicy deviating assignment who policy
  have prefixed : Profile.update (sig := graph.gameSignature) deviating who
        (graph.prefixPolicy who replayed) =
      graph.prefixProfile (Profile.update (sig := graph.gameSignature) profile who replayed) := by
    rw [prefixProfile_update]
    funext owner
    by_cases same : owner = who
    · subst owner
      simp only [deviating, Profile.update_same]
    · simp only [deviating, Profile.update_of_ne _ _ same]
  have replay (initial : graph.Inputs) := runPolicies_prefixReplay relaxed deviating
    deviatingSubmits assignment who (by simpa only [deviating, Profile.update_same] using
      policyOblivious) initial
  simp only [deviating, Profile.update_same] at replay
  rw [PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro initial _
  rw [← replay initial]
  change (graph.runPolicies _ (Profile.update (sig := graph.gameSignature) deviating who
    (graph.prefixPolicy who replayed)) initial).map runKey = _
  rw [prefixed]
  exact relaxed.runPolicies_prefixProfile_map_runKey _
    (oblivious.update policyOblivious.prefixReplay) _ initial

end Vegas.EventGraph
