/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.SchedulerErasure
import GameTheory.Math.Probability.FiniteSampling

/-! # Predrawing a public scheduler

A public scheduler randomizes at each public observation. Along one run the
completion order grows at every step, so no public observation recurs, and
drawing one independent choice for each reachable observation in advance gives
the same execution law. Every randomized public scheduler is therefore a
mixture of deterministic public schedulers, for a fixed profile and a finitely
supported input law. Player policies and chance nodes keep their own
randomization.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- One supported step of a policy plan. -/
def PlanStep (profile : graph.BehavioralProfile) (scheduler : graph.PublicScheduler)
    (before after : graph.Config) : Prop :=
  ∃ (notTerminal : ¬ before.cut.Terminal),
    ∃ selected ∈ (scheduler (graph.publicObserve before) before.cut.enabled
      (enabled_nonempty_of_not_terminal before notTerminal)).support,
      after ∈ (eventStep profile before selected.1
        ((EventOrder.Cut.mem_enabled _ _).mp selected.2)).support

/-- Configurations reachable from one configuration under a policy plan. -/
abbrev PlanReachable (profile : graph.BehavioralProfile) (scheduler : graph.PublicScheduler) :
    graph.Config → graph.Config → Prop :=
  Relation.ReflTransGen (PlanStep profile scheduler)

/-- A supported plan step consumes one unfinished event. -/
theorem PlanStep.remaining {profile : graph.BehavioralProfile}
    {scheduler : graph.PublicScheduler} {before after : graph.Config}
    (step : PlanStep profile scheduler before after) : after.remaining + 1 = before.remaining := by
  obtain ⟨_, selected, _, member⟩ := step
  unfold eventStep at member
  rw [PMF.support_bind] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨action, _, stepped⟩ := member
  exact before.remaining_step _ _ action after stepped

/-- A supported plan step appends exactly one completion. -/
theorem PlanStep.history_length {profile : graph.BehavioralProfile}
    {scheduler : graph.PublicScheduler} {before after : graph.Config}
    (step : PlanStep profile scheduler before after) :
    after.history.length = before.history.length + 1 := by
  obtain ⟨_, selected, _, member⟩ := step
  unfold eventStep at member
  rw [PMF.support_bind] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨action, _, stepped⟩ := member
  rw [Config.step, PMF.support_map] at stepped
  obtain ⟨value, _, rfl⟩ := stepped
  simp

theorem PlanReachable.history_length_le {profile : graph.BehavioralProfile}
    {scheduler : graph.PublicScheduler} {before after : graph.Config}
    (reach : PlanReachable profile scheduler before after) :
    before.history.length ≤ after.history.length := by
  induction reach with
  | refl => exact le_rfl
  | tail _ step ih => rw [step.history_length]; omega

/-- One drawn event's step has finite support when the profile branches finitely. -/
theorem eventStep_support_finite (profile : graph.BehavioralProfile)
    (finiteProfile : graph.ProfileFiniteSupport profile) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event) :
    (eventStep profile config event ready).support.Finite := by
  unfold eventStep
  rw [PMF.support_bind]
  have actions : (actionLaw profile config event).support.Finite := by
    cases ownerEq : (graph.nodes event).actor with
    | none => rw [actionLaw_of_ownerless _ _ ownerEq]; simp
    | some owner =>
        rw [actionLaw_of_actor _ _ ownerEq]
        by_cases inactive : owner ∈ config.defaulted
        · rw [dite_eq_left inactive]; simp
        · rw [dite_eq_right inactive]; exact finiteProfile _ _ _ _ _
  exact actions.biUnion fun action _ => config.step_support_finite event ready action

/-- Finitely branching plans reach finitely many configurations. -/
theorem planReachable_finite (profile : graph.BehavioralProfile)
    (finiteProfile : graph.ProfileFiniteSupport profile) (scheduler : graph.PublicScheduler) :
    ∀ fuel (config : graph.Config), config.remaining = fuel →
      {next | PlanReachable profile scheduler config next}.Finite := by
  intro fuel
  induction fuel with
  | zero =>
      intro config remaining
      apply (Set.finite_singleton config).subset
      intro next reach
      induction reach with
      | refl => rfl
      | tail _ step ih =>
          subst ih
          have := step.remaining
          omega
  | succ fuel ih =>
      intro config remaining
      have oneStep : {next | PlanStep profile scheduler config next}.Finite := by
        by_cases terminal : config.cut.Terminal
        · apply Set.finite_empty.subset
          rintro next ⟨notTerminal, _⟩
          exact notTerminal terminal
        · let laws := scheduler (graph.publicObserve config) config.cut.enabled
            (enabled_nonempty_of_not_terminal config terminal)
          apply ((Set.toFinite laws.support).biUnion fun selected _ =>
            eventStep_support_finite profile finiteProfile config selected.1
              ((EventOrder.Cut.mem_enabled _ _).mp selected.2)).subset
          rintro next ⟨_, selected, chosen, member⟩
          exact Set.mem_biUnion chosen member
      apply ((Set.finite_singleton config).union (oneStep.biUnion fun next step =>
        ih next (by have := PlanStep.remaining step; omega))).subset
      intro last reach
      rcases Relation.ReflTransGen.cases_head reach with same | ⟨next, step, rest⟩
      · exact Or.inl same.symm
      · exact Or.inr (Set.mem_biUnion step rest)

/-- Schedulers that agree at every configuration reachable under the first give the same run. -/
theorem runPlan_congr_scheduler (profile : graph.BehavioralProfile)
    (first second : graph.PublicScheduler) :
    ∀ fuel (config : graph.Config),
      (∀ next, PlanReachable profile first config next → ∀ (notTerminal : ¬ next.cut.Terminal),
        first (graph.publicObserve next) next.cut.enabled
            (enabled_nonempty_of_not_terminal next notTerminal) =
          second (graph.publicObserve next) next.cut.enabled
            (enabled_nonempty_of_not_terminal next notTerminal)) →
      graph.runPlan (graph.policyPlan profile first) fuel config =
        graph.runPlan (graph.policyPlan profile second) fuel config := by
  intro fuel
  induction fuel with
  | zero => intro config _; rfl
  | succ fuel ih =>
      intro config agree
      by_cases terminal : config.cut.Terminal
      · simp only [EventGraph.runPlan, dite_eq_left terminal]
      · rw [runPlan_policyPlan_succ profile first fuel config terminal,
          runPlan_policyPlan_succ profile second fuel config terminal,
          ← agree config Relation.ReflTransGen.refl terminal]
        apply bind_congr_on_support _
        intro selected chosen
        apply bind_congr_on_support _
        intro next member
        exact ih next fun later reach => agree later
          (Relation.ReflTransGen.head ⟨terminal, selected, chosen, member⟩ reach)

/-- Scheduling sites: a public observation together with an enabled set. -/
abbrev ScheduleSite (graph : Vegas.EventGraph Player L) :=
  graph.PublicObservation × Finset graph.EventId

/-- The site at which a configuration is scheduled. -/
def scheduleSite (config : graph.Config) : graph.ScheduleSite :=
  (graph.publicObserve config, config.cut.enabled)

/-- Read a drawn event as a selection from an enabled set, falling back to its least event. -/
def selectAt (enabled : Finset graph.EventId) (nonempty : enabled.Nonempty)
    (drawn : Option graph.EventId) : {event // event ∈ enabled} :=
  match drawn with
  | some event => if member : event ∈ enabled then ⟨event, member⟩
      else ⟨enabled.min' nonempty, Finset.min'_mem _ _⟩
  | none => ⟨enabled.min' nonempty, Finset.min'_mem _ _⟩

/-- The public scheduler drawing its selection from one law per site. -/
def schedulerOf (laws : graph.ScheduleSite → PMF (Option graph.EventId)) :
    graph.PublicScheduler :=
  fun observation enabled nonempty =>
    (laws (observation, enabled)).map (selectAt enabled nonempty)

/-- A scheduler's own laws, one per site. -/
def schedulerLaws (scheduler : graph.PublicScheduler) (site : graph.ScheduleSite) :
    PMF (Option graph.EventId) :=
  if nonempty : site.2.Nonempty then
    (scheduler site.1 site.2 nonempty).map fun selected => some selected.1
  else PMF.pure none

omit [DecidableEq Player] in
theorem schedulerOf_schedulerLaws (scheduler : graph.PublicScheduler) :
    schedulerOf (schedulerLaws scheduler) = scheduler := by
  funext observation enabled nonempty
  simp only [schedulerOf, schedulerLaws, dite_eq_left nonempty, PMF.map_comp]
  conv_rhs => rw [← PMF.map_id (scheduler observation enabled nonempty)]
  congr 1
  funext selected
  simp [selectAt, selected.2]

/-- The deterministic public scheduler of one assignment of drawn events. -/
def assignedScheduler (assignment : graph.ScheduleSite → Option graph.EventId) :
    graph.PublicScheduler :=
  schedulerOf fun site => PMF.pure (assignment site)

omit [DecidableEq Player] in
/-- A later configuration is scheduled at a different site. -/
theorem scheduleSite_ne_of_history_length_lt {earlier later : graph.Config}
    (longer : earlier.history.length < later.history.length) :
    scheduleSite later ≠ scheduleSite earlier := by
  intro same
  have orders := congrArg (fun site : graph.ScheduleSite => site.1.completionOrder.length) same
  simp only [scheduleSite, publicObserve_completionOrder, List.length_map] at orders
  omega

/-- Reachability transfers to a scheduler that agrees along the way. -/
theorem PlanReachable.of_agree {profile : graph.BehavioralProfile}
    {first second : graph.PublicScheduler} {start last : graph.Config}
    (reach : PlanReachable profile first start last)
    (agree : ∀ next, PlanReachable profile first start next →
      ∀ (notTerminal : ¬ next.cut.Terminal),
        first (graph.publicObserve next) next.cut.enabled
            (enabled_nonempty_of_not_terminal next notTerminal) =
          second (graph.publicObserve next) next.cut.enabled
            (enabled_nonempty_of_not_terminal next notTerminal)) :
    PlanReachable profile second start last := by
  induction reach with
  | refl => exact Relation.ReflTransGen.refl
  | tail before step ih =>
      obtain ⟨notTerminal, selected, chosen, member⟩ := step
      refine Relation.ReflTransGen.tail ih ?_
      refine ⟨notTerminal, selected, ?_, member⟩
      rw [← agree _ before notTerminal]
      exact chosen

/-- **Predraw.** Drawing one independent selection per reachable site in advance
gives the run of the randomized scheduler. -/
theorem sampleOn_bind_runPlan (profile : graph.BehavioralProfile)
    [DecidableEq graph.ScheduleSite] (sites : Finset graph.ScheduleSite)
    (fallback : graph.ScheduleSite → Option graph.EventId) :
    ∀ fuel (config : graph.Config) (laws : graph.ScheduleSite → PMF (Option graph.EventId)),
      config.remaining = fuel →
      (∀ next, PlanReachable profile (schedulerOf laws) config next →
        ¬ next.cut.Terminal → scheduleSite next ∈ sites) →
      (FiniteAssignment.sampleOn laws sites fallback).bind (fun assignment =>
          graph.runPlan (graph.policyPlan profile (assignedScheduler assignment)) fuel config) =
        graph.runPlan (graph.policyPlan profile (schedulerOf laws)) fuel config := by
  intro fuel
  induction fuel with
  | zero => intro config laws _ _; exact PMF.bind_const _ _
  | succ fuel ih =>
      intro config laws remaining covered
      by_cases terminal : config.cut.Terminal
      · simp only [EventGraph.runPlan, dite_eq_left terminal]
        exact PMF.bind_const _ _
      let site := scheduleSite config
      have siteMember : site ∈ sites := covered config Relation.ReflTransGen.refl terminal
      let nonempty := enabled_nonempty_of_not_terminal config terminal
      let committed : Option graph.EventId → graph.ScheduleSite → PMF (Option graph.EventId) :=
        fun drawn => Function.update laws site (PMF.pure drawn)
      rw [FiniteAssignment.sampleOn_factor_of_mem laws sites fallback siteMember committed
        (fun drawn => Function.update_self _ _ _)
        (fun drawn other different => Function.update_of_ne different _ _), PMF.bind_bind,
        runPlan_policyPlan_succ profile (schedulerOf laws) fuel config terminal]
      change _ = ((laws site).map (selectAt config.cut.enabled nonempty)).bind _
      rw [PMF.bind_map]
      apply bind_congr_on_support _
      intro drawn drawnSupported
      let selected := selectAt config.cut.enabled nonempty drawn
      have selectedReady : config.cut.Ready selected.1 :=
        (EventOrder.Cut.mem_enabled _ _).mp selected.2
      -- Every assignment in the committed table selects the drawn event here.
      have fixed : ∀ assignment ∈ (FiniteAssignment.sampleOn (committed drawn) sites
          fallback).support, assignment site = drawn := by
        intro assignment supported
        have evaluated := FiniteAssignment.sampleOn_map_eval_of_mem (committed drawn) sites
          fallback siteMember
        have member : assignment site ∈ ((FiniteAssignment.sampleOn (committed drawn) sites
            fallback).map fun assignment => assignment site).support :=
          (PMF.mem_support_map_iff _ _ _).mpr ⟨assignment, supported, rfl⟩
        rw [evaluated] at member
        simpa [committed] using member
      have firstStep : ∀ assignment ∈ (FiniteAssignment.sampleOn (committed drawn) sites
          fallback).support,
          graph.runPlan (graph.policyPlan profile (assignedScheduler assignment)) (fuel + 1)
              config =
            (eventStep profile config selected.1 selectedReady).bind
              (graph.runPlan (graph.policyPlan profile (assignedScheduler assignment)) fuel) := by
        intro assignment supported
        rw [runPlan_policyPlan_succ profile _ fuel config terminal]
        change ((PMF.pure (assignment site)).map (selectAt config.cut.enabled nonempty)).bind _ = _
        rw [PMF.pure_map, PMF.pure_bind, fixed assignment supported]
      rw [bind_congr_on_support _ firstStep, PMF.bind_comm]
      apply bind_congr_on_support _
      intro next nextSupported
      have step : PlanStep profile (schedulerOf laws) config next :=
        ⟨terminal, selected, (PMF.mem_support_map_iff _ _ _).mpr ⟨drawn, drawnSupported, rfl⟩,
          nextSupported⟩
      have longer : config.history.length < next.history.length := by
        rw [step.history_length]; omega
      -- The committed and original laws agree at every site reachable from `next`.
      have agreeFrom : ∀ (scheduler : graph.PublicScheduler), scheduler = schedulerOf laws ∨
          scheduler = schedulerOf (committed drawn) →
          ∀ later, PlanReachable profile scheduler next later →
            ∀ (notTerminal : ¬ later.cut.Terminal),
              schedulerOf (committed drawn) (graph.publicObserve later) later.cut.enabled
                  (enabled_nonempty_of_not_terminal later notTerminal) =
                schedulerOf laws (graph.publicObserve later) later.cut.enabled
                  (enabled_nonempty_of_not_terminal later notTerminal) := by
        intro scheduler _ later reach _
        have different := scheduleSite_ne_of_history_length_lt
          (lt_of_lt_of_le longer reach.history_length_le)
        simp only [schedulerOf, committed]
        rw [Function.update_of_ne (show (graph.publicObserve later, later.cut.enabled) ≠ site
          from different)]
      have nextRemaining : next.remaining = fuel := by have := step.remaining; omega
      rw [ih next (committed drawn) nextRemaining (fun later reach notTerminal =>
        covered later (Relation.ReflTransGen.head step (reach.of_agree fun middle middleReach
          middleNotTerminal => agreeFrom _ (Or.inr rfl) middle middleReach middleNotTerminal))
          notTerminal)]
      exact runPlan_congr_scheduler profile _ _ fuel next fun later reach notTerminal =>
        agreeFrom _ (Or.inr rfl) later reach notTerminal

/-- **Scheduler mixture.** For a finitely branching profile and a finitely
supported input law, every public scheduler is a mixture of deterministic
public schedulers, one mixture serving every supported input. -/
theorem exists_scheduler_mixture (profile : graph.BehavioralProfile)
    (finiteProfile : graph.ProfileFiniteSupport profile) (scheduler : graph.PublicScheduler)
    (inputs : PMF graph.Inputs) (finiteInputs : inputs.support.Finite) :
    ∃ mixture : PMF (graph.ScheduleSite → Option graph.EventId),
      ∀ initial ∈ inputs.support,
        mixture.bind (fun assignment =>
            graph.runPolicies (assignedScheduler assignment) profile initial) =
          graph.runPolicies scheduler profile initial := by
  classical
  have initialRemaining (initial : graph.Inputs) :
      (Config.initial initial : graph.Config).remaining = graph.order.eventCount := by
    simp [Config.remaining, Config.initial, EventOrder.Cut.empty]
  let reached : Set graph.ScheduleSite := ⋃ initial ∈ inputs.support,
    scheduleSite '' {next | PlanReachable profile scheduler (Config.initial initial) next}
  have reachedFinite : reached.Finite :=
    finiteInputs.biUnion fun initial _ =>
      (planReachable_finite profile finiteProfile scheduler _ _ (initialRemaining initial)).image _
  refine ⟨FiniteAssignment.sampleOn (schedulerLaws scheduler) reachedFinite.toFinset
    (fun _ => none), fun initial supported => ?_⟩
  unfold EventGraph.runPolicies EventGraph.run
  have law := sampleOn_bind_runPlan profile reachedFinite.toFinset (fun _ => none)
    _ _ (schedulerLaws scheduler) (initialRemaining initial)
  rw [schedulerOf_schedulerLaws] at law
  exact law fun next reach _ => (Set.Finite.mem_toFinset _).mpr
    (Set.mem_biUnion supported ⟨next, reach, rfl⟩)

end Vegas.EventGraph
