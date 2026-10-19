/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryCheckpointNormalization
import Vegas.Pending.PhaseClearSettlement

/-! # Intended source checkpoints through actual clear normalization -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- At a clear physical frontier, the actual chosen normalized checkpoint
retains whole source intendedness. Commitment admission is required only for
the current residual commitment phase and its actual raw completed fields. -/
theorem RecoverySourceCheckpoint.normalized_intended
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode))
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    {inputs : ((toEventGraph setup.program).withMode mode).Inputs}
    (native : state.Invariant inputs) (binding : state.BindingRecord)
    (receipts : state.ReceiptRecord) (stored : state.StoredCheckpoint)
    (remembered : state.HistoryCheckpoint) (order : state.PublicFailureOrder)
    (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (clear : state.current.excluded = ∅)
    (intended : ProtocolState.Intended setup.program (checkpoint.residual.lift
      (ProtocolState.entry checkpoint.residual.tail checkpoint.source)))
    (admitted : ∀ phase remaining, state.phases = phase :: remaining →
      phase.Finished state.current →
      ProtocolState.atCommit checkpoint.residual.tail
        (ProtocolState.entry checkpoint.residual.tail checkpoint.source) = true →
          checkpoint.commitAdmitted state.current) :
    ∃ next : RecoverySourceCheckpoint setup mode state.normalize,
      ProtocolState.Intended setup.program (next.residual.lift
        (ProtocolState.entry next.residual.tail next.source)) := by
  classical
  rcases state with ⟨phases, generation, entry, current, retired⟩
  change current.excluded = ∅ at clear
  cases phases with
  | nil => exact ⟨checkpoint, intended⟩
  | cons phase remaining =>
      let state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode) :=
        ⟨phase :: remaining, generation, entry, current, retired⟩
      have drained : phase.drain current = current := phase.drain_of_no_exclusions current clear
      by_cases finished : phase.Finished current
      · have normalized := state.normalize_of_clear_finished phase remaining rfl
          receipts.exclusion.frontier clear finished
        change ∃ next : RecoverySourceCheckpoint setup mode state.normalize, _
        rw [normalized]
        have finishedDrain : phase.Finished (phase.drain current) := by
          rw [drained]
          exact finished
        cases kind : phase.kind with
        | commitment =>
            have committing := checkpoint.compiled.atCommit_of_bindingPhase setup.program mode
              checkpoint.residual.tail checkpoint.refs checkpoint.source.revelations
              checkpoint.registry checkpoint.embedding checkpoint.before state.attempt.phase
              phase kind rfl checkpoint.source
            have clean : ¬ (((phase.drain current).excluded \ entry.excluded) ∩
                phase.owners).Nonempty := by
              simp only [drained, clear, Finset.empty_sdiff, Finset.empty_inter,
                Finset.not_nonempty_empty, not_false_eq_true]
            have result := checkpoint.after_commit_clean
              committing phase remaining rfl maximal
              binding receipts stored remembered native order.coverage finishedDrain clean
            rw [drained] at result
            obtain ⟨⟨next, _point, _sourcePrefix, _history, nextIntended⟩, _normalized⟩ := result
            exact ⟨next, nextIntended clear intended
              (admitted phase remaining rfl finished committing)⟩
        | reveal =>
            have member : phase ∈ state.phases.head? := by
              exact Option.mem_some_iff.mpr rfl
            have graphOrder := (toEventGraph setup.program).withMode_revealRelaxedOrdered
              (toEventGraph_barrierOrdered setup.program) mode
            have imageOrder := phase.orderedPublicFailures_drain phase.low entry.excluded current
              (order.publicationOrder phase member) order.coverage.active order.coverage.inherited
                graphOrder
            have result := checkpoint.after_reveal
              phase remaining rfl kind receipts.exclusion
              stored remembered (phase.drain_invariant current native.active).reachable imageOrder
                finishedDrain
            rw [drained] at result
            obtain ⟨next, _sourcePrefix, _publicSteps, _publicAddresses, _history,
              nextIntended, _replay⟩ := result
            exact ⟨next, nextIntended clear intended⟩
        | sample =>
            have result := checkpoint.after_sample_history
              phase remaining rfl kind receipts.exclusion
              stored remembered (phase.drain_invariant current native.active).reachable
                finishedDrain
            rw [drained] at result
            obtain ⟨next, _sourcePrefix, _publicSteps, _publicAddresses, _history,
              nextIntended, _replay, _sameExcluded, _sampled⟩ := result
            exact ⟨next, nextIntended clear intended⟩
      · have unchanged : state.normalize = state := by
          change PhaseRuntimeState.settle (phase :: remaining) generation entry current retired =
            state
          simp only [PhaseRuntimeState.settle, drained, finished, ↓reduceIte]
          rfl
        change ∃ next : RecoverySourceCheckpoint setup mode state.normalize,
          ProtocolState.Intended setup.program (next.residual.lift
            (ProtocolState.entry next.residual.tail next.source))
        rw [unchanged]
        exact ⟨checkpoint, intended⟩

end Vegas
