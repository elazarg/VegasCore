/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowDrain
import Vegas.Pending.PhaseBindingRepairObservation

/-! # Actual normalization under a current-generation binding shadow

Logical overrides are masked at each real retry. Permanent candidate overrides
are retained, and old retired states are compared only by their public records.
The proof follows the existing normalizer; it defines no alternative runner.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Saved and live semantics use the current logical mask. Retired private
snapshots retain their own meanings; their complete public records coincide. -/
structure PhaseStateFrame (memory : BindingShadow graph) (owner : Player)
    (original repaired : PhaseRuntimeState graph) : Prop where
  phases : original.phases = repaired.phases
  generation : original.generation = repaired.generation
  entry : original.entry = memory.recovery owner repaired.entry
  current : original.current = memory.recovery owner repaired.current
  retired : original.retired.map (fun prior => (prior.attempt, prior.state.publicView)) =
    repaired.retired.map (fun prior => (prior.attempt, prior.state.publicView))

/-- Public projections survive masks without rewriting retired private states. -/
theorem PhaseStateFrame.publicView {memory : BindingShadow graph} {owner : Player}
    {original repaired : PhaseRuntimeState graph} (frame : PhaseStateFrame memory owner
      original repaired) (owned : memory.OwnBindings owner) :
    original.publicView = repaired.publicView := by
  simp only [PhaseRuntimeState.publicView, PhaseRuntimeState.attempt, frame.phases,
    frame.generation, frame.current, recovery, native_publicView owned, frame.retired]

/-- Every different owner retains its complete application projection. -/
theorem PhaseStateFrame.playerView_other {memory : BindingShadow graph} {owner : Player}
    {original repaired : PhaseRuntimeState graph} (frame : PhaseStateFrame memory owner
      original repaired) (owned : memory.OwnBindings owner) (observer : Player)
    (different : observer ≠ owner) :
    original.playerView observer = repaired.playerView observer := by
  change (original.current.native.playerView observer, original.publicView) =
    (repaired.current.native.playerView observer, repaired.publicView)
  rw [frame.publicView owned, frame.current]
  exact congrArg (fun observed => (observed, repaired.publicView))
    (native_playerView_other owned repaired.current.native observer different)

/-- The existing normalizer supplies its own dynamic output mask. No
clear-attempt or empty-archive restriction is imposed. -/
theorem settle_phaseStateFrame (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner)
    (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph)
    (originalRetired repairedRetired : List (RetiredCommitAttempt graph))
    (archives : originalRetired.map (fun prior => (prior.attempt, prior.state.publicView)) =
      repairedRetired.map (fun prior => (prior.attempt, prior.state.publicView)))
    (supported : memory.CompletedAt current.native.config) :
    ∃ next : BindingShadow graph,
      next.OwnBindings owner ∧ next.candidates = memory.candidates ∧
      PhaseStateFrame next owner
        (PhaseRuntimeState.settle phases generation (memory.recovery owner entry)
          (memory.recovery owner current) originalRetired)
        (PhaseRuntimeState.settle phases generation entry current repairedRetired) ∧
      next.CompletedAt (PhaseRuntimeState.settle phases generation entry current
        repairedRetired).current.native.config := by
  classical
  induction phases generalizing memory generation entry current originalRetired repairedRetired with
  | nil =>
      exact ⟨memory, owned, rfl, ⟨rfl, rfl, rfl, rfl, archives⟩, supported⟩
  | cons phase remaining ih =>
      let drained := phase.drain current
      have drainedEq : memory.recovery owner drained =
          phase.drain (memory.recovery owner current) :=
        completedAt_drain memory owner phase current supported
      have drainedSupport : memory.CompletedAt drained.native.config :=
        supported.phase_drain phase
      simp only [PhaseRuntimeState.settle, ← drainedEq, phased_finished]
      by_cases finished : phase.Finished drained
      · have finishedActual : phase.Finished (phase.drain current) := finished
        simp only [finished, finishedActual, ite_true]
        by_cases failed : phase.kind = .commitment ∧
            ((drained.excluded \ entry.excluded) ∩ phase.owners).Nonempty
        · have failedOriginal : phase.kind = .commitment ∧
              (((memory.recovery owner drained).excluded \
                (memory.recovery owner entry).excluded) ∩ phase.owners).Nonempty := failed
          rw [ite_eq_left failedOriginal, ite_eq_left failed]
          let masked := memory.restrictCompleted entry.native.config.cut.completed
          let checkpoint := PhaseRuntimeState.restore entry drained
          let rebuilt := phase.drain checkpoint
          have maskedOwned : masked.OwnBindings owner := owned.restrictCompleted _
          have checkpointEq : masked.recovery owner checkpoint =
              PhaseRuntimeState.restore (memory.recovery owner entry)
                (memory.recovery owner drained) :=
            restrictCompleted_restore memory owner entry drained
          have rebuiltEq : masked.recovery owner rebuilt =
              phase.drain (PhaseRuntimeState.restore (memory.recovery owner entry)
                (memory.recovery owner drained)) :=
            restrictCompleted_restore_drain memory owner phase entry drained
          have rebuiltSupport : masked.CompletedAt rebuilt.native.config :=
            (restrictCompleted_completedAt memory entry.native.config.cut.completed
              checkpoint.native.config (fun _ member => member)).phase_drain phase
          have appended : (originalRetired ++
                [(⟨⟨phase.low, generation⟩, (memory.recovery owner drained).native⟩ :
                  RetiredCommitAttempt graph)]).map
                (fun prior : RetiredCommitAttempt graph =>
                  (prior.attempt, prior.state.publicView)) =
              (repairedRetired ++ [(⟨⟨phase.low, generation⟩, drained.native⟩ :
                RetiredCommitAttempt graph)]).map
                (fun prior : RetiredCommitAttempt graph =>
                  (prior.attempt, prior.state.publicView)) := by
            simp only [List.map_append, List.map_cons, List.map_nil, recovery,
              native_publicView owned, archives]
          by_cases survives : (phase.owners \ drained.excluded).Nonempty
          · have survivesOriginal :
                (phase.owners \ (memory.recovery owner drained).excluded).Nonempty := survives
            rw [ite_eq_left survivesOriginal, ite_eq_left survives]
            exact ⟨masked, maskedOwned, rfl,
              ⟨rfl, rfl, checkpointEq.symm, rebuiltEq.symm, appended⟩, rebuiltSupport⟩
          · have noSurvivorOriginal :
                ¬ (phase.owners \ (memory.recovery owner drained).excluded).Nonempty := survives
            rw [ite_eq_right noSurvivorOriginal, ite_eq_right survives]
            rw [← rebuiltEq]
            obtain ⟨next, nextOwned, candidates, frame, nextSupport⟩ :=
              ih masked maskedOwned generation rebuilt rebuilt _ _ appended rebuiltSupport
            exact ⟨next, nextOwned, candidates, frame, nextSupport⟩
        · have failedOriginal : ¬ (phase.kind = .commitment ∧
              (((memory.recovery owner drained).excluded \
                (memory.recovery owner entry).excluded) ∩ phase.owners).Nonempty) := failed
          rw [ite_eq_right failedOriginal, ite_eq_right failed]
          exact ih memory owned generation drained drained originalRetired repairedRetired archives
            drainedSupport
      · have notFinished : ¬ phase.Finished (phase.drain current) := finished
        simp only [finished, notFinished, ite_false]
        exact ⟨memory, owned, rfl, ⟨rfl, rfl, rfl, rfl, archives⟩, drainedSupport⟩

/-- Apply the actual normalizer to a live paired phase frame. The returned
mask retains physical candidates and discards only canceled logical producers. -/
theorem PhaseStateFrame.normalize {memory : BindingShadow graph} {owner : Player}
    {original repaired : PhaseRuntimeState graph} (frame : PhaseStateFrame memory owner
      original repaired) (owned : memory.OwnBindings owner)
    (supported : memory.CompletedAt repaired.current.native.config) :
    ∃ next : BindingShadow graph, next.OwnBindings owner ∧
      next.candidates = memory.candidates ∧ PhaseStateFrame next owner
        original.normalize repaired.normalize ∧
      next.CompletedAt repaired.normalize.current.native.config := by
  unfold PhaseRuntimeState.normalize
  rw [frame.phases, frame.generation, frame.entry, frame.current]
  exact settle_phaseStateFrame memory owner owned repaired.phases repaired.generation
    repaired.entry repaired.current original.retired repaired.retired frame.retired supported

end Vegas.EventGraphRuntime.BindingShadow
