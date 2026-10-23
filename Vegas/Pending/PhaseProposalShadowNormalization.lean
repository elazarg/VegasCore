/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalShadowRefinement

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
        repairedRetired).current.native.config ∧
      ((memory.native owner entry.native).config.store.BindingRefines entry.native.config.store →
        (memory.native owner current.native).config.store.BindingRefines
          current.native.config.store →
        let first := PhaseRuntimeState.settle phases generation (memory.recovery owner entry)
          (memory.recovery owner current) originalRetired
        let second := PhaseRuntimeState.settle phases generation entry current repairedRetired
        first.entry.native.config.store.BindingRefines second.entry.native.config.store ∧
          first.current.native.config.store.BindingRefines second.current.native.config.store) := by
  classical
  induction phases generalizing memory generation entry current originalRetired repairedRetired with
  | nil =>
      exact ⟨memory, owned, rfl, ⟨rfl, rfl, rfl, rfl, archives⟩, supported,
        fun entryRef currentRef => ⟨entryRef, currentRef⟩⟩
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
          have checkpointRef
              (entryRef : (memory.native owner entry.native).config.store.BindingRefines
                entry.native.config.store) :
              (masked.native owner checkpoint.native).config.store.BindingRefines
                checkpoint.native.config.store := by
            have stored := congrArg (fun state : RecoveryState graph => state.native.config.store)
              checkpointEq
            change (masked.native owner checkpoint.native).config.store =
              (memory.native owner entry.native).config.store at stored
            change (masked.native owner checkpoint.native).config.store.BindingRefines
              entry.native.config.store
            rw [stored]
            exact entryRef
          have rebuiltRef (entryRef : (memory.native owner entry.native).config.store.BindingRefines
              entry.native.config.store) :
              (masked.native owner rebuilt.native).config.store.BindingRefines
                rebuilt.native.config.store :=
            (restrictCompleted_completedAt memory entry.native.config.cut.completed
              checkpoint.native.config (fun _ member => member)).phase_drain_refinement owner
                (checkpointRef entryRef) phase
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
              ⟨rfl, rfl, checkpointEq.symm, rebuiltEq.symm, appended⟩, rebuiltSupport, by
                intro entryRef _currentRef
                change (PhaseRuntimeState.restore (memory.recovery owner entry)
                    (memory.recovery owner drained)).native.config.store.BindingRefines
                    checkpoint.native.config.store ∧
                  (phase.drain (PhaseRuntimeState.restore (memory.recovery owner entry)
                    (memory.recovery owner drained))).native.config.store.BindingRefines
                    rebuilt.native.config.store
                constructor
                · rw [← checkpointEq]
                  exact checkpointRef entryRef
                · rw [← rebuiltEq]
                  exact rebuiltRef entryRef⟩
          · have noSurvivorOriginal :
                ¬ (phase.owners \ (memory.recovery owner drained).excluded).Nonempty := survives
            rw [ite_eq_right noSurvivorOriginal, ite_eq_right survives]
            rw [← rebuiltEq]
            obtain ⟨next, nextOwned, candidates, frame, nextSupport, nextRef⟩ :=
              ih masked maskedOwned generation rebuilt rebuilt _ _ appended rebuiltSupport
            exact ⟨next, nextOwned, candidates, frame, nextSupport,
              fun entryRef _currentRef => nextRef (rebuiltRef entryRef) (rebuiltRef entryRef)⟩
        · have failedOriginal : ¬ (phase.kind = .commitment ∧
              (((memory.recovery owner drained).excluded \
                (memory.recovery owner entry).excluded) ∩ phase.owners).Nonempty) := failed
          rw [ite_eq_right failedOriginal, ite_eq_right failed]
          obtain ⟨next, nextOwned, candidates, frame, nextSupport, nextRef⟩ :=
            ih memory owned generation drained drained originalRetired repairedRetired archives
              drainedSupport
          exact ⟨next, nextOwned, candidates, frame, nextSupport, fun _entryRef currentRef =>
            let refined := supported.phase_drain_refinement owner currentRef phase
            nextRef refined refined⟩
      · have notFinished : ¬ phase.Finished (phase.drain current) := finished
        simp only [finished, notFinished, ite_false]
        exact ⟨memory, owned, rfl, ⟨rfl, rfl, rfl, rfl, archives⟩, drainedSupport,
          fun entryRef currentRef =>
            ⟨entryRef, supported.phase_drain_refinement owner currentRef phase⟩⟩

/-- Apply the actual normalizer to a live paired phase frame. The returned
mask retains physical candidates and discards only canceled logical producers. -/
theorem PhaseStateFrame.normalize {memory : BindingShadow graph} {owner : Player}
    {original repaired : PhaseRuntimeState graph} (frame : PhaseStateFrame memory owner
      original repaired) (owned : memory.OwnBindings owner)
    (supported : memory.CompletedAt repaired.current.native.config) :
    ∃ next : BindingShadow graph, next.OwnBindings owner ∧
      next.candidates = memory.candidates ∧ PhaseStateFrame next owner
        original.normalize repaired.normalize ∧
      next.CompletedAt repaired.normalize.current.native.config ∧
      (original.entry.native.config.store.BindingRefines repaired.entry.native.config.store →
        original.current.native.config.store.BindingRefines repaired.current.native.config.store →
        original.normalize.entry.native.config.store.BindingRefines
          repaired.normalize.entry.native.config.store ∧
        original.normalize.current.native.config.store.BindingRefines
          repaired.normalize.current.native.config.store) := by
  unfold PhaseRuntimeState.normalize
  rw [frame.phases, frame.generation, frame.entry, frame.current]
  exact settle_phaseStateFrame memory owner owned repaired.phases repaired.generation
    repaired.entry repaired.current original.retired repaired.retired frame.retired supported

end Vegas.EventGraphRuntime.BindingShadow
