import Vegas.Protocol.Machine

/-!
# Backend refinement

Backends such as blockchain runtimes are represented by the same
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
state projection. The relation is still machine-to-machine; it does not add a
second runtime semantics. -/
structure StochasticStepRefinement
    (Impl Spec : Machine Player) where
  projectState : Impl.State → Spec.State
  projectEvent : Impl.Event → Option Spec.Event
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

end StochasticStepRefinement

end Machine

end Vegas
