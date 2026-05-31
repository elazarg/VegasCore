/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.RefinementKernelGame

/-!
# Audited machines

`Machine.audited` is a small non-identity runtime wrapper. It adds an audit
counter and an administrative `tick` internal event to any machine, while
projecting back to the original machine by erasing ticks and forgetting the
counter.

The wrapper is intentionally runtime-general: it models bookkeeping,
instrumentation, logs, gas counters, or other implementation-local work without
choosing a concrete backend.
-/

namespace Vegas

namespace Machine

variable {Player : Type}

/-- Internal events of the audited wrapper: either an original internal event
or an implementation-local audit tick. -/
inductive AuditedInternal (M : Machine Player) where
  | spec (event : M.Internal)
  | tick

/-- Add administrative audit state and audit ticks to a machine. -/
noncomputable def audited (M : Machine Player) : Machine Player where
  State := M.State × Nat
  Action := M.Action
  Internal := AuditedInternal M
  Public := M.Public × Nat
  Obs := fun player => M.Obs player × Nat
  Outcome := M.Outcome
  init := (M.init, 0)
  available := fun state player => M.available state.1 player
  availableInternal := fun state event =>
    match event with
    | .spec specEvent => specEvent ∈ M.availableInternal state.1
    | .tick => True
  stepPlay := fun player action state =>
    PMF.map (fun dst => (dst, state.2)) (M.stepPlay player action state.1)
  stepInternal := fun event state =>
    match event with
    | .spec specEvent =>
        PMF.map (fun dst => (dst, state.2))
          (M.stepInternal specEvent state.1)
    | .tick => PMF.pure (state.1, state.2 + 1)
  terminal := fun state => M.terminal state.1
  publicView := fun state => (M.publicView state.1, state.2)
  observe := fun player state => (M.observe player state.1, state.2)
  outcome := fun state => M.outcome state.1
  utility := M.utility

namespace audited

variable (M : Machine Player)

@[simp] theorem init_fst : (audited M).init.1 = M.init := rfl

@[simp] theorem init_snd : (audited M).init.2 = 0 := rfl

@[simp] theorem terminal_iff (state : (audited M).State) :
    (audited M).terminal state ↔ M.terminal state.1 := Iff.rfl

/-- Lift an original primitive event to the audited machine. -/
def liftEvent : M.Event → (audited M).Event
  | .play player action => .play player action
  | .internal event => .internal (.spec event)

/-- Project audited primitive events, dropping audit ticks. -/
def projectEvent? : (audited M).Event → Option M.Event
  | .play player action => some (.play player action)
  | .internal (.spec event) => some (.internal event)
  | .internal .tick => none

/-- Project an audited batch by erasing audit ticks. -/
def projectEventBatch (batch : List (audited M).Event) : List M.Event :=
  batch.filterMap (projectEvent? M)

/-- Insert one administrative audit tick before a specification batch. -/
def liftEventBatch (batch : List M.Event) : List (audited M).Event :=
  .internal .tick :: batch.map (liftEvent M)

@[simp] theorem projectEvent?_liftEvent (event : M.Event) :
    projectEvent? M (liftEvent M event) = some event := by
  cases event <;> rfl

@[simp] theorem projectEventBatch_map_liftEvent (batch : List M.Event) :
    projectEventBatch M (batch.map (liftEvent M)) = batch := by
  rw [projectEventBatch, List.filterMap_map]
  simp

@[simp] theorem projectEventBatch_liftEventBatch (batch : List M.Event) :
    projectEventBatch M (liftEventBatch M batch) = batch := by
  rw [liftEventBatch, projectEventBatch]
  rw [List.filterMap_cons_none]
  · exact projectEventBatch_map_liftEvent M batch
  · rfl

private theorem liftEvent_available
    {state : M.State × Nat} {event : M.Event}
    (havailable : M.EventAvailable state.1 event) :
    (audited M).EventAvailable state (liftEvent M event) := by
  cases event with
  | play player action => exact havailable
  | internal event => exact havailable

private theorem liftEvent_support
    {state : M.State × Nat} {event : M.Event} {dst : M.State}
    (hsupport : dst ∈ (M.step event state.1).support) :
    (dst, state.2) ∈
      ((audited M).step (liftEvent M event) state).support := by
  cases event with
  | play player action =>
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨dst, hsupport, rfl⟩
  | internal event =>
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨dst, hsupport, rfl⟩

/-- Lift any available original run to the audited wrapper without changing
the audit counter. -/
theorem liftAvailableRunFrom
    {source target : M.State} {events : List M.Event} (audit : Nat)
    (hrun : M.AvailableRunFrom source events target) :
    (audited M).AvailableRunFrom (source, audit)
      (events.map (liftEvent M)) (target, audit) := by
  induction hrun with
  | nil state =>
      exact Machine.AvailableRunFrom.nil _
  | cons havailable hsupport tail ih =>
      rename_i source mid target event events
      exact Machine.AvailableRunFrom.cons
        (liftEvent_available (M := M) (state := (source, audit)) havailable)
        (liftEvent_support (M := M) (state := (source, audit)) hsupport)
        ih

/-- A single audit tick is always an available administrative run. -/
theorem auditTickAvailableRunFrom (state : (audited M).State) :
    (audited M).AvailableRunFrom state [.internal .tick]
      (state.1, state.2 + 1) := by
  refine Machine.AvailableRunFrom.cons ?_ ?_ (Machine.AvailableRunFrom.nil _)
  · trivial
  · change (state.1, state.2 + 1) ∈
      (PMF.pure (state.1, state.2 + 1)).support
    rw [PMF.support_pure]
    exact Set.mem_singleton _

/-- Prefixing a lifted specification batch with one audit tick gives an
available audited run whenever the original batch was available. -/
theorem liftEventBatchAvailableRunFrom
    {source target : M.State} {events : List M.Event} (audit : Nat)
    (hrun : M.AvailableRunFrom source events target) :
    (audited M).AvailableRunFrom (source, audit)
      (liftEventBatch M events) (target, audit + 1) := by
  simpa [liftEventBatch] using
    (auditTickAvailableRunFrom M (source, audit)).append
      (liftAvailableRunFrom M (audit + 1) hrun)

/-- Running audited events and then projecting state is the same as erasing
audit ticks and running the original events. -/
theorem runEventsFrom_project
    (events : List (audited M).Event) (source : (audited M).State) :
    PMF.map Prod.fst ((audited M).runEventsFrom events source) =
      M.runEventsFrom (projectEventBatch M events) source.1 := by
  induction events generalizing source with
  | nil =>
      change PMF.map Prod.fst (PMF.pure source) = PMF.pure source.1
      rw [PMF.pure_map]
  | cons event events ih =>
      rcases source with ⟨source, audit⟩
      cases event with
      | play player action =>
          rw [Machine.runEventsFrom_cons_bind]
          change PMF.map Prod.fst
              ((PMF.map (fun dst => (dst, audit))
                (M.stepPlay player action source)).bind fun current =>
                  (audited M).runEventsFrom events current) =
            M.runEventsFrom
              (Machine.Event.play player action :: projectEventBatch M events)
              source
          rw [Machine.runEventsFrom_cons_bind]
          rw [PMF.map_bind]
          simp_rw [ih]
          rw [PMF.bind_map]
          rfl
      | internal event =>
          cases event with
          | spec event =>
              rw [Machine.runEventsFrom_cons_bind]
              change PMF.map Prod.fst
                  ((PMF.map (fun dst => (dst, audit))
                    (M.stepInternal event source)).bind fun current =>
                      (audited M).runEventsFrom events current) =
                M.runEventsFrom
                  (Machine.Event.internal event :: projectEventBatch M events)
                  source
              rw [Machine.runEventsFrom_cons_bind]
              rw [PMF.map_bind]
              simp_rw [ih]
              rw [PMF.bind_map]
              rfl
          | tick =>
              rw [Machine.runEventsFrom_cons_bind]
              change PMF.map Prod.fst
                  ((PMF.pure (source, audit + 1)).bind fun current =>
                      (audited M).runEventsFrom events current) =
                M.runEventsFrom (projectEventBatch M events) source
              rw [PMF.pure_bind]
              exact ih (source, audit + 1)

/-- The audited wrapper refines the original machine by erasing audit ticks
and forgetting the audit counter. -/
noncomputable def refinement :
    StochasticRefinement (audited M) M where
  projectState := Prod.fst
  projectEvent? := projectEvent? M
  projectEventBatch := projectEventBatch M
  projectPublic := Prod.fst
  projectObs := fun _ => Prod.fst
  projectOutcome := id
  init_project := rfl
  available_project := by
    intro state event specEvent havailable hproject
    cases event with
    | play player action =>
        cases hproject
        exact havailable
    | internal event =>
        cases event with
        | spec event =>
            cases hproject
            exact havailable
        | tick =>
            simp [projectEvent?] at hproject
  step_project := by
    intro event source
    rcases source with ⟨source, audit⟩
    cases event with
    | play player action =>
        change PMF.map Prod.fst
            (PMF.map (fun dst => (dst, audit))
              (M.stepPlay player action source)) =
          M.stepPlay player action source
        rw [PMF.map_comp]
        exact PMF.map_id _
    | internal event =>
        cases event with
        | spec event =>
            change PMF.map Prod.fst
                (PMF.map (fun dst => (dst, audit))
                  (M.stepInternal event source)) =
              M.stepInternal event source
            rw [PMF.map_comp]
            exact PMF.map_id _
        | tick =>
            change PMF.map Prod.fst (PMF.pure (source, audit + 1)) =
              PMF.pure source
            rw [PMF.pure_map]
  eventBatch_project := by
    intro events source
    exact runEventsFrom_project M events source
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
    change Option.map id (M.outcome state.1) = M.outcome state.1
    simp
  utility_project := by
    intro outcome player
    rfl

/-- Lift a specification event-batch law to the audited machine by prefixing
each sampled batch with one audit tick. -/
noncomputable def liftEventBatchLaw (law : M.EventBatchLaw) :
    (audited M).EventBatchLaw :=
  fun trace =>
    PMF.map (liftEventBatch M)
      (law ((refinement M).projectEventBatchTrace trace))

/-- Lifted audited event-batch laws are legal whenever the original law is
legal. -/
theorem liftEventBatchLaw_legal {law : M.EventBatchLaw}
    (hlegal : M.IsLegalEventBatchLaw law) :
    (audited M).IsLegalEventBatchLaw (liftEventBatchLaw M law) := by
  intro trace hnonterminal batch hbatch
  rcases (PMF.mem_support_map_iff _ _ _).mp hbatch with
    ⟨specBatch, hspecBatch, hbatchEq⟩
  subst hbatchEq
  have hspecNonterminal :
      ¬ M.terminal ((refinement M).projectEventBatchTrace trace).2 := by
    exact hnonterminal
  rcases hlegal ((refinement M).projectEventBatchTrace trace)
      hspecNonterminal hspecBatch with
    ⟨dst, hrun⟩
  exact
    ⟨(dst, trace.2.2 + 1),
      liftEventBatchAvailableRunFrom M trace.2.2 hrun⟩

/-- The lifted law is compatible with the original law under the audited
refinement. -/
theorem liftEventBatchLaw_compatible (law : M.EventBatchLaw) :
    (refinement M).EventBatchLawCompatible
      (liftEventBatchLaw M law) law := by
  intro trace
  unfold liftEventBatchLaw
  rw [PMF.map_comp]
  change PMF.map (fun batch => projectEventBatch M (liftEventBatch M batch))
      (law ((refinement M).projectEventBatchTrace trace)) =
    law ((refinement M).projectEventBatchTrace trace)
  simp only [projectEventBatch_liftEventBatch]
  change PMF.map id (law ((refinement M).projectEventBatchTrace trace)) =
    law ((refinement M).projectEventBatchTrace trace)
  rw [PMF.map_id]

/-- Lift a whole strategy-indexed event-batch law family through the audited
refinement. -/
noncomputable def liftEventBatchLawFamily {Strategy : Player → Type}
    (family : M.EventBatchLawFamily Strategy) :
    (refinement M).EventBatchLawFamilyLift Strategy family where
  impl :=
    { law := fun profile => liftEventBatchLaw M (family.law profile)
      legal := fun profile => liftEventBatchLaw_legal M (family.legal profile) }
  compatible := fun profile =>
    liftEventBatchLaw_compatible M (family.law profile)

end audited

end Machine

end Vegas
