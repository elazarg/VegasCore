import Vegas.Machine.Trace

/-!
# Backend refinement

Backends such as external runtimes are represented by the same
`Protocol.Machine` carrier as protocol specifications. Runtime correctness is
therefore a relation between machines, not a second state-machine semantics.

The refinement below is deliberately weak and one-step: backend events may
project either to a protocol event or to an internal step that leaves the
projected protocol state unchanged. Trace-level, scheduler, liveness, and
strategic preservation theorems should be proved from this relation rather than
encoded as a second machine type.
-/

namespace Vegas

namespace Machine

variable {Player : Type}

/-- Weak one-step refinement from an implementation machine to a specification
machine.

The implementation may carry extra state, observations, outcomes, and events.
The projection fields say exactly which parts are protocol-visible. External
implementation events must simulate a positive-support protocol step; internal
implementation events must preserve the projected protocol state. -/
structure WeakStepRefinement
    (Impl Spec : Machine Player) where
  projectState : Impl.State → Spec.State
  projectEvent : Impl.Event → Option Spec.Event
  projectPublic : Impl.Public → Spec.Public
  projectObs : (player : Player) → Impl.Obs player → Spec.Obs player
  projectOutcome : Impl.Outcome → Spec.Outcome
  init_project : projectState Impl.init = Spec.init
  external_step_sound :
    ∀ {event : Impl.Event} {specEvent : Spec.Event}
      {source target : Impl.State},
      projectEvent event = some specEvent →
        Impl.StepRel event source target →
          Spec.StepRel specEvent
            (projectState source) (projectState target)
  internal_step_projectState_eq :
    ∀ {event : Impl.Event} {source target : Impl.State},
      projectEvent event = none →
        Impl.StepRel event source target →
          projectState target = projectState source
  publicView_project :
    ∀ state,
      Spec.publicView (projectState state) =
        projectPublic (Impl.publicView state)
  observe_project :
    ∀ player state,
      Spec.observe player (projectState state) =
        projectObs player (Impl.observe player state)
  terminal_project :
    ∀ {state : Impl.State}, Impl.terminal state →
      Spec.terminal (projectState state)
  terminal_outcome_projected :
    ∀ {state : Impl.State},
      Impl.terminal state →
        projectOutcome (Impl.outcome state) =
          Spec.outcome (projectState state)

/-- Probability-preserving one-step refinement from an implementation machine
to a specification machine.

This is the relation needed for runtime soundness statements that preserve
outcome distributions. External implementation events project to a
specification event and must have the same projected next-state PMF.
Internal implementation events project to `none` and must be stuttering after
state projection. `projectEventBatch` is the trace-level projection actually
used by batch laws; it may normalize an implementation schedule, for example by
canonicalizing independent frontier events before comparing with the
specification batch. The usual non-canonicalizing projection is
`events.filterMap projectEvent`, with `eventBatch_project` proved by induction
from `step_project`. The relation is still machine-to-machine; it does not add a
second runtime semantics. -/
structure StochasticStepRefinement
    (Impl Spec : Machine Player) where
  projectState : Impl.State → Spec.State
  projectEvent : Impl.Event → Option Spec.Event
  projectEventBatch : List Impl.Event → List Spec.Event
  projectPublic : Impl.Public → Spec.Public
  projectObs : (player : Player) → Impl.Obs player → Spec.Obs player
  projectOutcome : Impl.Outcome → Spec.Outcome
  init_project : projectState Impl.init = Spec.init
  step_project :
    ∀ (event : Impl.Event) (source : Impl.State),
      (Impl.step event source).map projectState =
        match projectEvent event with
        | some specEvent => Spec.step specEvent (projectState source)
        | none => PMF.pure (projectState source)
  eventBatch_project :
    ∀ (events : List Impl.Event) (source : Impl.State),
      (Impl.runEventsFrom events source).map projectState =
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
    ∀ {state : Impl.State}, Impl.terminal state →
      Spec.terminal (projectState state)
  terminal_reflect :
    ∀ {state : Impl.State}, Spec.terminal (projectState state) →
      Impl.terminal state
  terminal_outcome_projected :
    ∀ {state : Impl.State},
      Impl.terminal state →
        projectOutcome (Impl.outcome state) =
          Spec.outcome (projectState state)

namespace WeakStepRefinement

variable {Impl Spec : Machine Player}

theorem protocol_step_of_external_step
    (R : WeakStepRefinement Impl Spec)
    {event : Impl.Event} {specEvent : Spec.Event}
    {source target : Impl.State}
    (hlabel : R.projectEvent event = some specEvent)
    (hstep : Impl.StepRel event source target) :
    Spec.StepRel specEvent
      (R.projectState source) (R.projectState target) :=
  R.external_step_sound hlabel hstep

theorem projected_state_eq_of_internal_step
    (R : WeakStepRefinement Impl Spec)
    {event : Impl.Event} {source target : Impl.State}
    (hlabel : R.projectEvent event = none)
    (hstep : Impl.StepRel event source target) :
    R.projectState target = R.projectState source :=
  R.internal_step_projectState_eq hlabel hstep

theorem protocol_terminal_of_impl_terminal
    (R : WeakStepRefinement Impl Spec)
    {state : Impl.State} (hterminal : Impl.terminal state) :
    Spec.terminal (R.projectState state) :=
  R.terminal_project hterminal

theorem projected_outcome_of_terminal
    (R : WeakStepRefinement Impl Spec)
    {state : Impl.State} (hterminal : Impl.terminal state) :
    R.projectOutcome (Impl.outcome state) =
      Spec.outcome (R.projectState state) :=
  R.terminal_outcome_projected hterminal

end WeakStepRefinement

namespace StochasticStepRefinement

variable {Impl Spec : Machine Player}

/-- Every machine refines itself by the identity projection. Useful as a
baseline backend and as a smoke test for trace-projection theorems. -/
def refl (M : Machine Player) : StochasticStepRefinement M M where
  projectState := id
  projectEvent := some
  projectEventBatch := id
  projectPublic := id
  projectObs := fun _ => id
  projectOutcome := id
  init_project := rfl
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
    intro state h
    exact h
  terminal_reflect := by
    intro state h
    exact h
  terminal_outcome_projected := by
    intro state h
    rfl

/-- Probability-preserving machine refinement implies the older support-level
weak refinement. This keeps `WeakStepRefinement` as a convenience view rather
than a competing runtime-correctness notion. -/
def toWeakStepRefinement
    (R : StochasticStepRefinement Impl Spec) :
    WeakStepRefinement Impl Spec where
  projectState := R.projectState
  projectEvent := R.projectEvent
  projectPublic := R.projectPublic
  projectObs := R.projectObs
  projectOutcome := R.projectOutcome
  init_project := R.init_project
  external_step_sound := by
    intro event specEvent source target hlabel hstep
    have hmemImpl :
        target ∈ (Impl.step event source).support := by
      exact (PMF.mem_support_iff _ _).2 hstep
    have hmemMap :
        R.projectState target ∈
          ((Impl.step event source).map R.projectState).support := by
      exact (PMF.mem_support_map_iff _ _ _).2
        ⟨target, hmemImpl, rfl⟩
    rw [R.step_project event source, hlabel] at hmemMap
    exact (PMF.mem_support_iff _ _).1 hmemMap
  internal_step_projectState_eq := by
    intro event source target hlabel hstep
    have hmemImpl :
        target ∈ (Impl.step event source).support := by
      exact (PMF.mem_support_iff _ _).2 hstep
    have hmemMap :
        R.projectState target ∈
          ((Impl.step event source).map R.projectState).support := by
      exact (PMF.mem_support_map_iff _ _ _).2
        ⟨target, hmemImpl, rfl⟩
    rw [R.step_project event source, hlabel] at hmemMap
    simpa using hmemMap
  publicView_project := R.publicView_project
  observe_project := R.observe_project
  terminal_project := R.terminal_project
  terminal_outcome_projected := R.terminal_outcome_projected

@[simp] theorem toWeakStepRefinement_projectState
    (R : StochasticStepRefinement Impl Spec) :
    R.toWeakStepRefinement.projectState = R.projectState := rfl

@[simp] theorem toWeakStepRefinement_projectEvent
    (R : StochasticStepRefinement Impl Spec) :
    R.toWeakStepRefinement.projectEvent = R.projectEvent := rfl

theorem projected_step_eq_spec_step
    (R : StochasticStepRefinement Impl Spec)
    {event : Impl.Event} {specEvent : Spec.Event}
    {source : Impl.State}
    (hlabel : R.projectEvent event = some specEvent) :
    (Impl.step event source).map R.projectState =
      Spec.step specEvent (R.projectState source) := by
  rw [R.step_project event source, hlabel]

theorem projected_step_eq_pure_of_internal
    (R : StochasticStepRefinement Impl Spec)
    {event : Impl.Event} {source : Impl.State}
    (hlabel : R.projectEvent event = none) :
    (Impl.step event source).map R.projectState =
      PMF.pure (R.projectState source) := by
  rw [R.step_project event source, hlabel]

theorem projected_terminal_iff
    (R : StochasticStepRefinement Impl Spec)
    {state : Impl.State} :
    Spec.terminal (R.projectState state) ↔ Impl.terminal state :=
  ⟨R.terminal_reflect, R.terminal_project⟩

theorem projected_outcome_of_terminal
    (R : StochasticStepRefinement Impl Spec)
    {state : Impl.State} (hterminal : Impl.terminal state) :
    R.projectOutcome (Impl.outcome state) =
      Spec.outcome (R.projectState state) :=
  R.terminal_outcome_projected hterminal

/-- Project an implementation event-batch trace to the corresponding
specification event-batch trace. -/
def projectEventBatchTrace
    (R : StochasticStepRefinement Impl Spec) :
    Impl.EventBatchTrace → Spec.EventBatchTrace :=
  fun trace => (trace.1.map R.projectEventBatch, R.projectState trace.2)

@[simp] theorem projectEventBatchTrace_fst
    (R : StochasticStepRefinement Impl Spec) (trace : Impl.EventBatchTrace) :
    (R.projectEventBatchTrace trace).1 = trace.1.map R.projectEventBatch := rfl

@[simp] theorem projectEventBatchTrace_snd
    (R : StochasticStepRefinement Impl Spec) (trace : Impl.EventBatchTrace) :
    (R.projectEventBatchTrace trace).2 = R.projectState trace.2 := rfl

@[simp] theorem projectEventBatchTrace_append_batch
    (R : StochasticStepRefinement Impl Spec)
    (trace : Impl.EventBatchTrace) (batch : List Impl.Event)
    (state : Impl.State) :
    R.projectEventBatchTrace (trace.1 ++ [batch], state) =
      ((R.projectEventBatchTrace trace).1 ++ [R.projectEventBatch batch],
        R.projectState state) := by
  simp [projectEventBatchTrace]

@[simp] theorem refl_projectEventBatch
    (M : Machine Player) (batch : List M.Event) :
    ((refl M).projectEventBatch batch) = batch := by
  simp [refl]

@[simp] theorem refl_projectEventBatchTrace
    (M : Machine Player) (trace : M.EventBatchTrace) :
    ((refl M).projectEventBatchTrace trace) = trace := by
  cases trace with
  | mk batches state =>
      change (batches.map (refl M).projectEventBatch, state) =
        (batches, state)
      congr
      induction batches with
      | nil => simp
      | cons batch batches ih =>
          simp [ih]

/-- Projecting a fixed implementation event run gives the same state
distribution as running the externally visible specification events. -/
theorem runEventsFrom_project_eq
    (R : StochasticStepRefinement Impl Spec)
    (events : List Impl.Event) (state : Impl.State) :
    (Impl.runEventsFrom events state).map R.projectState =
      Spec.runEventsFrom (R.projectEventBatch events)
        (R.projectState state) :=
  R.eventBatch_project events state

/-- Projecting a fixed implementation event-batch run gives the same state
distribution as running the projected specification event batches. -/
theorem runEventBatchesFrom_project_eq
    (R : StochasticStepRefinement Impl Spec)
    (batches : List (List Impl.Event)) (state : Impl.State) :
    (Impl.runEventBatchesFrom batches state).map R.projectState =
      Spec.runEventBatchesFrom (batches.map R.projectEventBatch)
        (R.projectState state) := by
  induction batches generalizing state with
  | nil =>
      simp [PMF.pure_map]
  | cons batch batches ih =>
      change
        PMF.map R.projectState
          (Impl.runEventBatchesFrom ([batch] ++ batches) state) =
        Spec.runEventBatchesFrom
          ([R.projectEventBatch batch] ++ batches.map R.projectEventBatch)
          (R.projectState state)
      rw [Impl.runEventBatchesFrom_append]
      rw [PMF.map_bind]
      simp_rw [ih]
      rw [Impl.runEventBatchesFrom_singleton]
      change
        (Impl.runEventsFrom batch state).bind
            ((fun specState =>
              Spec.runEventBatchesFrom (batches.map R.projectEventBatch)
                specState) ∘ R.projectState) =
          Spec.runEventBatchesFrom
            ([R.projectEventBatch batch] ++ batches.map R.projectEventBatch)
            (R.projectState state)
      rw [← PMF.bind_map
        (p := Impl.runEventsFrom batch state)
        (f := R.projectState)
        (q := fun specState =>
          Spec.runEventBatchesFrom (batches.map R.projectEventBatch)
            specState)]
      rw [R.runEventsFrom_project_eq batch state]
      rw [Spec.runEventBatchesFrom_append]
      simp [Spec.runEventBatchesFrom_singleton]

/-- Compatibility between a backend event-batch law and a specification
event-batch law: sampling a backend event batch and applying the refinement's
batch projection must give the same distribution as sampling the specification
event batch from the projected trace. The batch projection, not the pointwise
event projection, is the comparison boundary for runtimes that use a different
schedule for independent primitive events. -/
def EventBatchLawCompatible
    (R : StochasticStepRefinement Impl Spec)
    (lawImpl : Impl.EventBatchLaw) (lawSpec : Spec.EventBatchLaw) : Prop :=
  ∀ trace : Impl.EventBatchTrace,
    PMF.map R.projectEventBatch (lawImpl trace) =
      lawSpec (R.projectEventBatchTrace trace)

theorem refl_eventBatchLawCompatible
    (M : Machine Player) (law : M.EventBatchLaw) :
    (refl M).EventBatchLawCompatible law law := by
  intro trace
  rw [refl_projectEventBatchTrace]
  have hbatch :
      (fun batch : List M.Event => (refl M).projectEventBatch batch) = id := by
    funext batch
    exact refl_projectEventBatch M batch
  change PMF.map
      (fun batch : List M.Event => (refl M).projectEventBatch batch)
      (law trace) = law trace
  rw [hbatch]
  exact PMF.map_id (law trace)

/-- A strategy/scheduler lift for a fixed specification event-batch law. The
refinement remains machine-to-machine; this structure supplies the extra
backend scheduling data needed to run a strategic profile on an implementation. -/
structure RefinementEventBatchLawLift
    (R : StochasticStepRefinement Impl Spec)
    (lawSpec : Spec.EventBatchLaw) where
  lawImpl : Impl.EventBatchLaw
  legalImpl : Impl.IsLegalEventBatchLaw lawImpl
  compatible : R.EventBatchLawCompatible lawImpl lawSpec

/-- Trace-level outcome preservation for compatible history-dependent
event-batch laws. Projecting the backend event-batch trace distribution gives exactly the
specification event-batch trace distribution. -/
theorem eventBatchTraceDist_project_eq
    (R : StochasticStepRefinement Impl Spec)
    (lawSpec : Spec.EventBatchLaw) (lawImpl : Impl.EventBatchLaw)
    (compat : R.EventBatchLawCompatible lawImpl lawSpec) :
    ∀ (horizon : Nat) (trace : Impl.EventBatchTrace),
      PMF.map R.projectEventBatchTrace
          (Impl.eventBatchTraceDistFrom lawImpl horizon trace) =
        Spec.eventBatchTraceDistFrom lawSpec horizon (R.projectEventBatchTrace trace)
  | 0, trace => by
      rw [Impl.eventBatchTraceDistFrom_zero]
      rw [Spec.eventBatchTraceDistFrom_zero]
      rw [PMF.pure_map]
  | horizon + 1, trace => by
      by_cases hterm : Impl.terminal trace.2
      · rw [Impl.eventBatchTraceDistFrom_succ_terminal _ _ _ hterm]
        rw [Spec.eventBatchTraceDistFrom_succ_terminal _ _ _ (R.terminal_project hterm)]
        rw [PMF.pure_map]
      · have hspecTerm :
            ¬ Spec.terminal (R.projectEventBatchTrace trace).2 := by
          intro h
          exact hterm (R.terminal_reflect h)
        rw [Impl.eventBatchTraceDistFrom_succ_nonterminal _ _ _ hterm]
        rw [Spec.eventBatchTraceDistFrom_succ_nonterminal _ _ _ hspecTerm]
        rw [PMF.map_bind]
        simp_rw [PMF.map_bind]
        simp_rw [eventBatchTraceDist_project_eq R lawSpec lawImpl compat horizon]
        conv_lhs =>
          arg 2
          intro batch
          simp only [projectEventBatchTrace, List.map_append, List.map_cons,
            List.map_nil]
          change
            (Impl.runEventBatchesFrom [batch] trace.2).bind
                ((fun state =>
                    Spec.eventBatchTraceDistFrom lawSpec horizon
                      ((R.projectEventBatchTrace trace).1 ++
                        [R.projectEventBatch batch], state)) ∘
                  R.projectState)
          rw [← PMF.bind_map]
          rw [R.runEventBatchesFrom_project_eq [batch] trace.2]
        simp only [List.map_cons, List.map_nil]
        change
          (lawImpl trace).bind
              ((fun specBatch =>
                  (Spec.runEventBatchesFrom [specBatch]
                      (R.projectEventBatchTrace trace).2).bind fun next =>
                    Spec.eventBatchTraceDistFrom lawSpec horizon
                      ((R.projectEventBatchTrace trace).1 ++ [specBatch],
                        next)) ∘
                R.projectEventBatch) =
            (lawSpec (R.projectEventBatchTrace trace)).bind fun specBatch =>
              (Spec.runEventBatchesFrom [specBatch]
                  (R.projectEventBatchTrace trace).2).bind fun next =>
                Spec.eventBatchTraceDistFrom lawSpec horizon
                  ((R.projectEventBatchTrace trace).1 ++ [specBatch], next)
        rw [← PMF.bind_map]
        rw [compat trace]

theorem RefinementEventBatchLawLift.eventBatchTraceDist_project_eq
    (R : StochasticStepRefinement Impl Spec)
    (lawSpec : Spec.EventBatchLaw) (lift : R.RefinementEventBatchLawLift lawSpec)
    (horizon : Nat) (trace : Impl.EventBatchTrace) :
    PMF.map R.projectEventBatchTrace
        (Impl.eventBatchTraceDistFrom lift.lawImpl horizon trace) =
      Spec.eventBatchTraceDistFrom lawSpec horizon (R.projectEventBatchTrace trace) :=
  R.eventBatchTraceDist_project_eq lawSpec lift.lawImpl lift.compatible
    horizon trace

end StochasticStepRefinement

end Machine

end Vegas
