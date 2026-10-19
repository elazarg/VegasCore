/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowMask
import Vegas.Pending.PhaseCompletion
import Vegas.Pending.PhaseResolution

/-! # Logical shadows through actual automatic recovery

A mask chosen at the restored checkpoint has no override at any producer
subsequently completed by automatic exclusion. The actual bounded drain
therefore commutes with that SAME mask throughout its existing recursion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- A frontier-supported shadow is unchanged by masking that frontier. -/
theorem restrictCompleted_eq_of_completedAt (memory : BindingShadow graph)
    (config : graph.Config) (supported : memory.CompletedAt config) :
    memory.restrictCompleted config.cut.completed = memory := by
  classical
  have values : (memory.restrictCompleted config.cut.completed).values = memory.values := by
    funext field
    cases field with
    | inl input => rfl
    | inr event =>
        by_cases present : event ∈ config.cut.completed
        · simp only [restrictCompleted, present, ite_true]
        · have absent : memory.values (.inr event) = none := by
            cases stored : memory.values (.inr event) with
            | none => rfl
            | some value =>
                exact (present (supported event (Or.inr (by rw [stored]; rfl)))).elim
          simp only [restrictCompleted, present, ite_false, absent]
  have actions : (memory.restrictCompleted config.cut.completed).actions = memory.actions := by
    funext event
    by_cases present : event ∈ config.cut.completed
    · simp only [restrictCompleted, present, ite_true]
    · have absent : memory.actions event = none := by
        cases stored : memory.actions event with
        | none => rfl
        | some action =>
            exact (present (supported event (Or.inl (by rw [stored]; rfl)))).elim
      simp only [restrictCompleted, present, ite_false, absent]
  cases memory
  exact congrArg₂ (fun values actions => BindingShadow.mk values actions _) values actions

omit [DecidableEq Player] in
/-- Mask support is inherited by every later actual completed frontier. -/
theorem restrictCompleted_completedAt (memory : BindingShadow graph)
    (completed : Finset graph.EventId) (config : graph.Config)
    (retained : completed ⊆ config.cut.completed) :
    (memory.restrictCompleted completed).CompletedAt config := by
  classical
  intro event present
  by_cases kept : event ∈ completed
  · exact retained kept
  · have absent := restrictCompleted_pending memory completed event kept
    rcases present with action | value
    · rw [absent.2] at action
      cases action
    · rw [absent.1] at value
      cases value

/-- Automatic service preserves support of already remembered completions. -/
theorem CompletedAt.phase_drain {memory : BindingShadow graph} {config : RecoveryState graph}
    (supported : memory.CompletedAt config.native.config) (phase : RuntimePhase graph) :
    memory.CompletedAt (phase.drain config).native.config := by
  intro event present
  exact phase.drain_completed config (supported event present)

omit [DecidableEq Player] in
/-- A single real automatic completion only enlarges the completed frontier. -/
private theorem automatic_completed_subset (state : RecoveryState graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    state.native.config.cut.completed ⊆
      (state.completeAutomatic event eligible).native.config.cut.completed := by
  obtain ⟨action, supported⟩ := state.completeAutomatic_step event eligible
  rw [state.native.config.step_cut event eligible.1 action _ supported]
  exact state.native.config.cut.completed_subset_complete event eligible.1

/-- Entire actual automatic drain, with the logical mask selected BEFORE
draining. Exclusions and old-generation physical catalogues are unrestricted. -/
theorem restrictCompleted_drainFuel (memory : BindingShadow graph) (owner : Player)
    (completed : Finset graph.EventId) (phase : RuntimePhase graph) (fuel : Nat)
    (state : RecoveryState graph) (retained : completed ⊆ state.native.config.cut.completed) :
    (memory.restrictCompleted completed).recovery owner (phase.drainFuel fuel state) =
      phase.drainFuel fuel ((memory.restrictCompleted completed).recovery owner state) := by
  classical
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      let masked := memory.restrictCompleted completed
      by_cases pending : ∃ event, event ∈ phase.events ∧ state.AutomaticReady event
      · have transformed : ∃ event, event ∈ phase.events ∧
            (masked.recovery owner state).AutomaticReady event := pending
        rw [RuntimePhase.drainFuel, dite_eq_left pending, RuntimePhase.drainFuel,
          dite_eq_left transformed]
        let event := Classical.choose pending
        have eligible : state.AutomaticReady event := (Classical.choose_spec pending).2
        change masked.recovery owner (phase.drainFuel fuel (state.completeAutomatic event
            eligible)) = phase.drainFuel fuel ((masked.recovery owner state).completeAutomatic
              event eligible)
        rw [← restrictCompleted_completeAutomatic memory owner completed state event eligible
          retained]
        exact ih _ (retained.trans (automatic_completed_subset state event eligible))
      · have clear : ¬ ∃ event, event ∈ phase.events ∧
            (masked.recovery owner state).AutomaticReady event := pending
        rw [RuntimePhase.drainFuel, dite_eq_right pending, RuntimePhase.drainFuel,
          dite_eq_right clear]

/-- Derived whole-drain equation at the real native remaining-work bound. -/
theorem restrictCompleted_drain (memory : BindingShadow graph) (owner : Player)
    (completed : Finset graph.EventId) (phase : RuntimePhase graph)
    (state : RecoveryState graph) (retained : completed ⊆ state.native.config.cut.completed) :
    (memory.restrictCompleted completed).recovery owner (phase.drain state) =
      phase.drain ((memory.restrictCompleted completed).recovery owner state) := by
  exact restrictCompleted_drainFuel memory owner completed phase state.native.config.remaining
    state retained

/-- A current supported shadow commutes with the complete actual phase drain. -/
theorem completedAt_drain (memory : BindingShadow graph) (owner : Player)
    (phase : RuntimePhase graph) (state : RecoveryState graph)
    (supported : memory.CompletedAt state.native.config) :
    memory.recovery owner (phase.drain state) = phase.drain (memory.recovery owner state) := by
  have same := restrictCompleted_eq_of_completedAt memory state.native.config supported
  have drained := restrictCompleted_drain memory owner state.native.config.cut.completed
    phase state (fun _ member => member)
  rwa [same] at drained

/-- The actual retry restoration followed by rebuilt automatic service.
Candidate overrides stay physical while canceled logical overrides disappear. -/
theorem restrictCompleted_restore_drain (memory : BindingShadow graph) (owner : Player)
    (phase : RuntimePhase graph) (entry current : RecoveryState graph) :
    let masked := memory.restrictCompleted entry.native.config.cut.completed
    masked.recovery owner (phase.drain (PhaseRuntimeState.restore entry current)) =
      phase.drain (PhaseRuntimeState.restore (memory.recovery owner entry)
        (memory.recovery owner current)) := by
  dsimp only
  rw [restrictCompleted_drain memory owner entry.native.config.cut.completed phase
    (PhaseRuntimeState.restore entry current) (fun _ member => member),
    restrictCompleted_restore memory owner entry current]

end Vegas.EventGraphRuntime.BindingShadow
