/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.KernelGame
import Vegas.Machine.Trace

/-!
# Machine refinement hooks

Probability-preserving refinement between protocol machines, including event
batch projection, observations, terminal outcomes, and utilities. This module
defines the runtime-general proof surface without choosing a concrete runtime.
-/

namespace Vegas

namespace Machine

variable {Player ImplPlayer SpecPlayer : Type}

/-- Probability-preserving refinement between two machines with the same
player set.

The implementation may have finer states, events, observations, and outcomes.
`projectState` and `projectEvent?` identify the specification behavior visible
at the protocol boundary. Events projecting to `none` are implementation-local
administrative steps and must stutter after state projection.

`projectEventBatch` is intentionally separate from pointwise `filterMap`: a
runtime may execute a concrete schedule whose specification comparison
canonicalizes or quotients independent events at the batch boundary. -/
structure StochasticRefinement
    (Impl Spec : Machine Player) where
  projectState : Impl.State → Spec.State
  projectEvent? : Impl.Event → Option Spec.Event
  projectEventBatch : List Impl.Event → List Spec.Event
  projectPublic : Impl.Public → Spec.Public
  projectObs : (player : Player) → Impl.Obs player → Spec.Obs player
  projectOutcome : Impl.Outcome → Spec.Outcome
  init_project : projectState Impl.init = Spec.init
  available_project :
    ∀ {state event specEvent},
      Impl.EventAvailable state event →
        projectEvent? event = some specEvent →
          Spec.EventAvailable (projectState state) specEvent
  step_project :
    ∀ event source,
      PMF.map projectState (Impl.step event source) =
        match projectEvent? event with
        | some specEvent => Spec.step specEvent (projectState source)
        | none => PMF.pure (projectState source)
  eventBatch_project :
    ∀ events source,
      PMF.map projectState (Impl.runEventsFrom events source) =
        Spec.runEventsFrom (projectEventBatch events) (projectState source)
  publicView_project :
    ∀ state,
      Spec.publicView (projectState state) =
        projectPublic (Impl.publicView state)
  observe_project :
    ∀ player state,
      Spec.observe player (projectState state) =
        projectObs player (Impl.observe player state)
  terminal_project :
    ∀ {state}, Impl.terminal state → Spec.terminal (projectState state)
  terminal_reflect :
    ∀ {state}, Spec.terminal (projectState state) → Impl.terminal state
  outcome_project :
    ∀ state,
      Option.map projectOutcome (Impl.outcome state) =
        Spec.outcome (projectState state)
  utility_project :
    ∀ outcome player,
      Spec.utility (projectOutcome outcome) player =
        Impl.utility outcome player

namespace StochasticRefinement

variable {Impl Spec : Machine Player}

/-- Identity refinement, useful as the baseline runtime relation. -/
def refl (M : Machine Player) : StochasticRefinement M M where
  projectState := id
  projectEvent? := some
  projectEventBatch := id
  projectPublic := id
  projectObs := fun _ => id
  projectOutcome := id
  init_project := rfl
  available_project := by
    intro state event specEvent havailable hlabel
    injection hlabel with heq
    cases heq
    exact havailable
  step_project := by
    intro event source
    rw [PMF.map_id]
    rfl
  eventBatch_project := by
    intro events source
    rw [PMF.map_id]
    rfl
  publicView_project := by
    intro state
    rfl
  observe_project := by
    intro player state
    rfl
  terminal_project := by
    intro state hterminal
    exact hterminal
  terminal_reflect := by
    intro state hterminal
    exact hterminal
  outcome_project := by
    intro state
    change Option.map id (M.outcome state) = M.outcome state
    simp
  utility_project := by
    intro outcome player
    rfl

variable {Low Mid : Machine Player}

/-- Compose two stochastic refinements. The implementation-to-specification
batch projection is the explicit composition of the two batch projections,
not a derived pointwise event projection. -/
def compose
    (R₂ : StochasticRefinement Mid Spec)
    (R₁ : StochasticRefinement Low Mid) :
    StochasticRefinement Low Spec where
  projectState := fun state => R₂.projectState (R₁.projectState state)
  projectEvent? := fun event => (R₁.projectEvent? event).bind R₂.projectEvent?
  projectEventBatch := fun events =>
    R₂.projectEventBatch (R₁.projectEventBatch events)
  projectPublic := fun view => R₂.projectPublic (R₁.projectPublic view)
  projectObs := fun player obs =>
    R₂.projectObs player (R₁.projectObs player obs)
  projectOutcome := fun outcome => R₂.projectOutcome (R₁.projectOutcome outcome)
  init_project := by
    rw [R₁.init_project, R₂.init_project]
  available_project := by
    intro state event specEvent havailable hproject
    cases hmid : R₁.projectEvent? event with
    | none =>
        simp [hmid] at hproject
    | some midEvent =>
        have hmidAvailable :
            Mid.EventAvailable (R₁.projectState state) midEvent :=
          R₁.available_project havailable hmid
        rw [hmid] at hproject
        exact R₂.available_project hmidAvailable hproject
  step_project := by
    intro event source
    change
      PMF.map (R₂.projectState ∘ R₁.projectState)
          (Low.step event source) =
        match Option.bind (R₁.projectEvent? event) R₂.projectEvent? with
        | some specEvent =>
            Spec.step specEvent (R₂.projectState (R₁.projectState source))
        | none =>
            PMF.pure (R₂.projectState (R₁.projectState source))
    rw [← PMF.map_comp]
    rw [R₁.step_project event source]
    cases hmid : R₁.projectEvent? event with
    | none =>
        simp [PMF.pure_map]
    | some midEvent =>
        simpa using R₂.step_project midEvent (R₁.projectState source)
  eventBatch_project := by
    intro events source
    change
      PMF.map (R₂.projectState ∘ R₁.projectState)
          (Low.runEventsFrom events source) =
        Spec.runEventsFrom
          (R₂.projectEventBatch (R₁.projectEventBatch events))
          (R₂.projectState (R₁.projectState source))
    rw [← PMF.map_comp]
    rw [R₁.eventBatch_project events source]
    exact
      R₂.eventBatch_project (R₁.projectEventBatch events)
        (R₁.projectState source)
  publicView_project := by
    intro state
    rw [R₂.publicView_project]
    rw [R₁.publicView_project]
  observe_project := by
    intro player state
    rw [R₂.observe_project]
    rw [R₁.observe_project]
  terminal_project := by
    intro state hterminal
    exact R₂.terminal_project (R₁.terminal_project hterminal)
  terminal_reflect := by
    intro state hterminal
    exact R₁.terminal_reflect (R₂.terminal_reflect hterminal)
  outcome_project := by
    intro state
    change
      Option.map (R₂.projectOutcome ∘ R₁.projectOutcome)
          (Low.outcome state) =
        Spec.outcome (R₂.projectState (R₁.projectState state))
    rw [← Option.map_map]
    rw [R₁.outcome_project state]
    exact R₂.outcome_project (R₁.projectState state)
  utility_project := by
    intro outcome player
    rw [R₂.utility_project, R₁.utility_project]

theorem projected_step_eq_spec_step
    (R : StochasticRefinement Impl Spec)
    {event : Impl.Event} {specEvent : Spec.Event}
    {source : Impl.State}
    (hlabel : R.projectEvent? event = some specEvent) :
    PMF.map R.projectState (Impl.step event source) =
      Spec.step specEvent (R.projectState source) := by
  rw [R.step_project event source, hlabel]

theorem projected_step_eq_pure_of_internal
    (R : StochasticRefinement Impl Spec)
    {event : Impl.Event} {source : Impl.State}
    (hlabel : R.projectEvent? event = none) :
    PMF.map R.projectState (Impl.step event source) =
      PMF.pure (R.projectState source) := by
  rw [R.step_project event source, hlabel]

theorem projected_terminal_iff
    (R : StochasticRefinement Impl Spec)
    {state : Impl.State} :
    Spec.terminal (R.projectState state) ↔ Impl.terminal state :=
  ⟨R.terminal_reflect, R.terminal_project⟩

/-- A projected step preserves the fact that every supported successor is
nonterminal. This is useful for runtime wrappers whose administrative state
must be drained before the wrapped source machine is allowed to terminate. -/
theorem step_support_nonterminal_project
    (R : StochasticRefinement Impl Spec)
    {event : Impl.Event} {specEvent : Spec.Event}
    {source : Impl.State}
    (hlabel : R.projectEvent? event = some specEvent)
    (hnonterminal :
      ∀ target, target ∈ (Impl.step event source).support →
        ¬ Impl.terminal target) :
    ∀ target, target ∈
        (Spec.step specEvent (R.projectState source)).support →
      ¬ Spec.terminal target := by
  intro target htarget hterminal
  have hstep := R.projected_step_eq_spec_step (source := source) hlabel
  rw [← hstep] at htarget
  rcases (PMF.mem_support_map_iff _ _ _).mp htarget with
    ⟨implTarget, himplTarget, hprojectTarget⟩
  have himplTerminal : Impl.terminal implTarget := by
    apply R.terminal_reflect
    simpa [hprojectTarget] using hterminal
  exact hnonterminal implTarget himplTarget himplTerminal

/-- Project an implementation event-batch trace to the corresponding
specification event-batch trace. -/
def projectEventBatchTrace
    (R : StochasticRefinement Impl Spec) :
    Impl.EventBatchTrace → Spec.EventBatchTrace :=
  fun trace => (trace.1.map R.projectEventBatch, R.projectState trace.2)

@[simp] theorem compose_projectEventBatchTrace
    (R₂ : StochasticRefinement Mid Spec)
    (R₁ : StochasticRefinement Low Mid)
    (trace : Low.EventBatchTrace) :
    (R₂.compose R₁).projectEventBatchTrace trace =
      R₂.projectEventBatchTrace (R₁.projectEventBatchTrace trace) := by
  rcases trace with ⟨batches, state⟩
  simp [projectEventBatchTrace, compose, List.map_map, Function.comp_def]

@[simp] theorem projectEventBatchTrace_fst
    (R : StochasticRefinement Impl Spec) (trace : Impl.EventBatchTrace) :
    (R.projectEventBatchTrace trace).1 = trace.1.map R.projectEventBatch :=
  rfl

@[simp] theorem projectEventBatchTrace_snd
    (R : StochasticRefinement Impl Spec) (trace : Impl.EventBatchTrace) :
    (R.projectEventBatchTrace trace).2 = R.projectState trace.2 :=
  rfl

@[simp] theorem projectEventBatchTrace_append_batch
    (R : StochasticRefinement Impl Spec)
    (trace : Impl.EventBatchTrace) (batch : List Impl.Event)
    (state : Impl.State) :
    R.projectEventBatchTrace (trace.1 ++ [batch], state) =
      ((R.projectEventBatchTrace trace).1 ++ [R.projectEventBatch batch],
        R.projectState state) := by
  simp [projectEventBatchTrace]

@[simp] theorem refl_projectEventBatch
    (M : Machine Player) (batch : List M.Event) :
    ((refl M).projectEventBatch batch) = batch :=
  rfl

@[simp] theorem refl_projectEventBatchTrace
    (M : Machine Player) (trace : M.EventBatchTrace) :
    ((refl M).projectEventBatchTrace trace) = trace := by
  cases trace with
  | mk batches state =>
      change (batches.map (refl M).projectEventBatch, state) =
        (batches, state)
      have hfun :
          (refl M).projectEventBatch =
            (id : List M.Event → List M.Event) := by
        funext batch
        rfl
      rw [hfun]
      simp

/-- Projecting a fixed implementation event run gives the same state
distribution as running the externally visible specification batch. -/
theorem runEventsFrom_project_eq
    (R : StochasticRefinement Impl Spec)
    (events : List Impl.Event) (state : Impl.State) :
    PMF.map R.projectState (Impl.runEventsFrom events state) =
      Spec.runEventsFrom (R.projectEventBatch events)
        (R.projectState state) :=
  R.eventBatch_project events state

/-- Projecting a fixed implementation event-batch run gives the same state
distribution as running the projected specification event batches. -/
theorem runEventBatchesFrom_project_eq
    (R : StochasticRefinement Impl Spec)
    (batches : List (List Impl.Event)) (state : Impl.State) :
    PMF.map R.projectState
        (Impl.runEventBatchesFrom batches state) =
      Spec.runEventBatchesFrom (batches.map R.projectEventBatch)
        (R.projectState state) := by
  induction batches generalizing state with
  | nil =>
      change
        PMF.map R.projectState (PMF.pure state) =
          PMF.pure (R.projectState state)
      rw [PMF.pure_map]
  | cons batch batches ih =>
      change
        PMF.map R.projectState
            (Impl.runEventBatchesFrom ([batch] ++ batches) state) =
          Spec.runEventBatchesFrom
            ([R.projectEventBatch batch] ++
              batches.map R.projectEventBatch)
            (R.projectState state)
      rw [Impl.runEventBatchesFrom_append]
      rw [PMF.map_bind]
      simp_rw [ih]
      rw [Impl.runEventBatchesFrom_singleton]
      change
        PMF.bind (Impl.runEventsFrom batch state)
            ((fun specState =>
              Spec.runEventBatchesFrom
                (batches.map R.projectEventBatch) specState) ∘
              R.projectState) =
          Spec.runEventBatchesFrom
            ([R.projectEventBatch batch] ++
              batches.map R.projectEventBatch)
            (R.projectState state)
      rw [← PMF.bind_map
        (p := Impl.runEventsFrom batch state)
        (f := R.projectState)
        (q := fun specState =>
          Spec.runEventBatchesFrom (batches.map R.projectEventBatch)
            specState)]
      rw [R.runEventsFrom_project_eq batch state]
      rw [Spec.runEventBatchesFrom_append]
      simp

/-- Compatibility between an implementation event-batch law and a
specification event-batch law. The comparison boundary is the batch projection,
so an implementation runtime may use a different concrete order for
independent primitive events. -/
def EventBatchLawCompatible
    (R : StochasticRefinement Impl Spec)
    (lawImpl : Impl.EventBatchLaw) (lawSpec : Spec.EventBatchLaw) : Prop :=
  ∀ trace : Impl.EventBatchTrace,
    PMF.map R.projectEventBatch (lawImpl trace) =
      lawSpec (R.projectEventBatchTrace trace)

/-- Compatibility for deterministic event-batch laws reduces to equality of
projected batches. -/
theorem EventBatchLawCompatible.of_pure
    (R : StochasticRefinement Impl Spec)
    (implBatch : Impl.EventBatchTrace → List Impl.Event)
    (specBatch : Spec.EventBatchTrace → List Spec.Event)
    (hproject :
      ∀ trace,
        R.projectEventBatch (implBatch trace) =
          specBatch (R.projectEventBatchTrace trace)) :
    R.EventBatchLawCompatible
      (fun trace => PMF.pure (implBatch trace))
      (fun trace => PMF.pure (specBatch trace)) := by
  intro trace
  rw [PMF.pure_map]
  exact congrArg PMF.pure (hproject trace)

/-- Event-batch-law compatibility is transitive through composed stochastic
refinements. -/
theorem EventBatchLawCompatible.trans
    (R₂ : StochasticRefinement Mid Spec)
    (R₁ : StochasticRefinement Low Mid)
    {lawLow : Low.EventBatchLaw}
    {lawMid : Mid.EventBatchLaw}
    {lawSpec : Spec.EventBatchLaw}
    (h₁ : R₁.EventBatchLawCompatible lawLow lawMid)
    (h₂ : R₂.EventBatchLawCompatible lawMid lawSpec) :
    (R₂.compose R₁).EventBatchLawCompatible lawLow lawSpec := by
  intro trace
  change
    PMF.map (R₂.projectEventBatch ∘ R₁.projectEventBatch)
        (lawLow trace) =
      lawSpec ((R₂.compose R₁).projectEventBatchTrace trace)
  rw [← PMF.map_comp]
  rw [h₁ trace]
  rw [h₂ (R₁.projectEventBatchTrace trace)]
  rw [compose_projectEventBatchTrace]

theorem refl_eventBatchLawCompatible
    (M : Machine Player) (law : M.EventBatchLaw) :
    (refl M).EventBatchLawCompatible law law := by
  intro trace
  rw [refl_projectEventBatchTrace]
  have hmap :
      (refl M).projectEventBatch =
        (id : List M.Event → List M.Event) := by
    funext batch
    rfl
  rw [hmap]
  exact PMF.map_id (law trace)

/-- A strategy/scheduler lift for a fixed specification event-batch law. The
refinement remains machine-to-machine; this structure supplies the extra
implementation scheduling data needed to run a strategic profile on a concrete
runtime. -/
structure EventBatchLawLift
    (R : StochasticRefinement Impl Spec)
    (lawSpec : Spec.EventBatchLaw) where
  lawImpl : Impl.EventBatchLaw
  legalImpl : Impl.IsLegalEventBatchLaw lawImpl
  compatible : R.EventBatchLawCompatible lawImpl lawSpec

/-- Trace-level distribution preservation for compatible history-dependent
event-batch laws. -/
theorem eventBatchTraceDist_project_eq
    (R : StochasticRefinement Impl Spec)
    (lawSpec : Spec.EventBatchLaw) (lawImpl : Impl.EventBatchLaw)
    (compat : R.EventBatchLawCompatible lawImpl lawSpec) :
    ∀ horizon trace,
      PMF.map R.projectEventBatchTrace
          (Impl.eventBatchTraceDistFrom lawImpl horizon trace) =
        Spec.eventBatchTraceDistFrom lawSpec horizon
          (R.projectEventBatchTrace trace)
  | 0, trace => by
      rw [Impl.eventBatchTraceDistFrom_zero]
      rw [Spec.eventBatchTraceDistFrom_zero]
      rw [PMF.pure_map]
  | horizon + 1, trace => by
      by_cases hterm : Impl.terminal trace.2
      · rw [Impl.eventBatchTraceDistFrom_succ_terminal _ _ _ hterm]
        rw [Spec.eventBatchTraceDistFrom_succ_terminal _ _ _
          (R.terminal_project hterm)]
        rw [PMF.pure_map]
      · have hspecTerm :
            ¬ Spec.terminal (R.projectEventBatchTrace trace).2 := by
          intro hterminal
          exact hterm (R.terminal_reflect hterminal)
        rw [Impl.eventBatchTraceDistFrom_succ_nonterminal _ _ _ hterm]
        rw [Spec.eventBatchTraceDistFrom_succ_nonterminal _ _ _
          hspecTerm]
        rw [PMF.map_bind]
        simp_rw [PMF.map_bind]
        simp_rw [eventBatchTraceDist_project_eq R lawSpec lawImpl compat
          horizon]
        conv_lhs =>
          arg 2
          intro batch
          simp only [projectEventBatchTrace, List.map_append, List.map_cons,
            List.map_nil]
          change
            PMF.bind (Impl.runEventBatchesFrom [batch] trace.2)
                ((fun state =>
                    Spec.eventBatchTraceDistFrom lawSpec horizon
                      ((R.projectEventBatchTrace trace).1 ++
                        [R.projectEventBatch batch], state)) ∘
                  R.projectState)
          rw [← PMF.bind_map]
          rw [R.runEventBatchesFrom_project_eq [batch] trace.2]
        simp only [List.map_cons, List.map_nil]
        change
          PMF.bind (lawImpl trace)
              ((fun specBatch =>
                  PMF.bind
                    (Spec.runEventBatchesFrom [specBatch]
                      (R.projectEventBatchTrace trace).2)
                    fun next =>
                      Spec.eventBatchTraceDistFrom lawSpec horizon
                        ((R.projectEventBatchTrace trace).1 ++
                          [specBatch], next)) ∘
                R.projectEventBatch) =
            PMF.bind (lawSpec (R.projectEventBatchTrace trace))
              fun specBatch =>
                PMF.bind
                  (Spec.runEventBatchesFrom [specBatch]
                    (R.projectEventBatchTrace trace).2)
                  fun next =>
                    Spec.eventBatchTraceDistFrom lawSpec horizon
                      ((R.projectEventBatchTrace trace).1 ++
                        [specBatch], next)
        rw [← PMF.bind_map]
        rw [compat trace]

theorem EventBatchLawLift.eventBatchTraceDist_project_eq
    (R : StochasticRefinement Impl Spec)
    (lawSpec : Spec.EventBatchLaw)
    (lift : R.EventBatchLawLift lawSpec)
    (horizon : Nat) (trace : Impl.EventBatchTrace) :
    PMF.map R.projectEventBatchTrace
        (Impl.eventBatchTraceDistFrom lift.lawImpl horizon trace) =
      Spec.eventBatchTraceDistFrom lawSpec horizon
        (R.projectEventBatchTrace trace) :=
  R.eventBatchTraceDist_project_eq lawSpec lift.lawImpl lift.compatible
    horizon trace

/-- Projected implementation event-batch traces induce the same partial outcome
law as the specification event-batch traces. -/
theorem eventBatchOutcomeDist_project_eq
    (R : StochasticRefinement Impl Spec)
    (lawSpec : Spec.EventBatchLaw) (lawImpl : Impl.EventBatchLaw)
    (compat : R.EventBatchLawCompatible lawImpl lawSpec)
    (horizon : Nat) (trace : Impl.EventBatchTrace) :
    PMF.map
        (fun implTrace =>
          Option.map R.projectOutcome (Impl.outcome implTrace.2))
        (Impl.eventBatchTraceDistFrom lawImpl horizon trace) =
      PMF.map
        (fun specTrace => Spec.outcome specTrace.2)
        (Spec.eventBatchTraceDistFrom lawSpec horizon
          (R.projectEventBatchTrace trace)) := by
  have htrace :=
    R.eventBatchTraceDist_project_eq lawSpec lawImpl compat horizon trace
  rw [← htrace, PMF.map_comp]
  congr 1
  funext implTrace
  exact R.outcome_project implTrace.2

theorem EventBatchLawLift.eventBatchOutcomeDist_project_eq
    (R : StochasticRefinement Impl Spec)
    (lawSpec : Spec.EventBatchLaw)
    (lift : R.EventBatchLawLift lawSpec)
    (horizon : Nat) (trace : Impl.EventBatchTrace) :
    PMF.map
        (fun implTrace =>
          Option.map R.projectOutcome (Impl.outcome implTrace.2))
        (Impl.eventBatchTraceDistFrom lift.lawImpl horizon trace) =
      PMF.map
        (fun specTrace => Spec.outcome specTrace.2)
        (Spec.eventBatchTraceDistFrom lawSpec horizon
          (R.projectEventBatchTrace trace)) :=
  R.eventBatchOutcomeDist_project_eq lawSpec lift.lawImpl lift.compatible
    horizon trace

/-- Cutoff-utility evaluation commutes with the outcome projection carried by a
stochastic refinement. -/
theorem optionOutcomeUtility_project
    (R : StochasticRefinement Impl Spec)
    (cutoff : GameTheory.Payoff Player)
    (result : Option Impl.Outcome) :
    RoundView.optionOutcomeUtility Spec cutoff
        (Option.map R.projectOutcome result) =
      RoundView.optionOutcomeUtility Impl cutoff result := by
  cases result with
  | none => rfl
  | some outcome =>
      funext player
      exact R.utility_project outcome player

/-- Compatible event-batch laws preserve the payoff-vector distribution induced
by option-valued machine outcomes and an explicit cutoff policy. -/
theorem eventBatchOptionUtilityDist_project_eq
    (R : StochasticRefinement Impl Spec)
    (lawSpec : Spec.EventBatchLaw) (lawImpl : Impl.EventBatchLaw)
    (compat : R.EventBatchLawCompatible lawImpl lawSpec)
    (cutoff : GameTheory.Payoff Player)
    (horizon : Nat) (trace : Impl.EventBatchTrace) :
    PMF.map
        (fun implTrace =>
          RoundView.optionOutcomeUtility Impl cutoff
            (Impl.outcome implTrace.2))
        (Impl.eventBatchTraceDistFrom lawImpl horizon trace) =
      PMF.map
        (fun specTrace =>
          RoundView.optionOutcomeUtility Spec cutoff
            (Spec.outcome specTrace.2))
        (Spec.eventBatchTraceDistFrom lawSpec horizon
          (R.projectEventBatchTrace trace)) := by
  have houtcome :=
    R.eventBatchOutcomeDist_project_eq lawSpec lawImpl compat horizon trace
  calc
    PMF.map
        (fun implTrace =>
          RoundView.optionOutcomeUtility Impl cutoff
            (Impl.outcome implTrace.2))
        (Impl.eventBatchTraceDistFrom lawImpl horizon trace)
        =
      PMF.map
        (fun implTrace =>
          RoundView.optionOutcomeUtility Spec cutoff
            (Option.map R.projectOutcome (Impl.outcome implTrace.2)))
        (Impl.eventBatchTraceDistFrom lawImpl horizon trace) := by
          congr 1
          funext implTrace
          exact (R.optionOutcomeUtility_project cutoff
            (Impl.outcome implTrace.2)).symm
    _ =
      PMF.map (RoundView.optionOutcomeUtility Spec cutoff)
        (PMF.map
          (fun implTrace =>
            Option.map R.projectOutcome (Impl.outcome implTrace.2))
          (Impl.eventBatchTraceDistFrom lawImpl horizon trace)) := by
          rw [PMF.map_comp]
          rfl
    _ =
      PMF.map (RoundView.optionOutcomeUtility Spec cutoff)
        (PMF.map
          (fun specTrace => Spec.outcome specTrace.2)
          (Spec.eventBatchTraceDistFrom lawSpec horizon
            (R.projectEventBatchTrace trace))) := by
          rw [houtcome]
    _ =
      PMF.map
        (fun specTrace =>
          RoundView.optionOutcomeUtility Spec cutoff
            (Spec.outcome specTrace.2))
        (Spec.eventBatchTraceDistFrom lawSpec horizon
          (R.projectEventBatchTrace trace)) := by
          rw [PMF.map_comp]
          rfl

theorem EventBatchLawLift.eventBatchOptionUtilityDist_project_eq
    (R : StochasticRefinement Impl Spec)
    (lawSpec : Spec.EventBatchLaw)
    (lift : R.EventBatchLawLift lawSpec)
    (cutoff : GameTheory.Payoff Player)
    (horizon : Nat) (trace : Impl.EventBatchTrace) :
    PMF.map
        (fun implTrace =>
          RoundView.optionOutcomeUtility Impl cutoff
            (Impl.outcome implTrace.2))
        (Impl.eventBatchTraceDistFrom lift.lawImpl horizon trace) =
      PMF.map
        (fun specTrace =>
          RoundView.optionOutcomeUtility Spec cutoff
            (Spec.outcome specTrace.2))
        (Spec.eventBatchTraceDistFrom lawSpec horizon
          (R.projectEventBatchTrace trace)) :=
  R.eventBatchOptionUtilityDist_project_eq lawSpec lift.lawImpl
    lift.compatible cutoff horizon trace

end StochasticRefinement

end Machine

end Vegas
