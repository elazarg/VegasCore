/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryCommitUnique

/-! # The literal entry history of a genuine current commitment attempt

The entry is recovered from the original initialized source trace. Its saved
source point, entry exclusions and generation are the actual current fields;
no independently selected checkpoint or history is supplied.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem attempt_entry_of_trace
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    ∀ (current : CommitRecoveryState setup.program), state = some current →
      ProtocolState.atCommit setup.program current.point = true →
      ∃ entry : setup.commitRecoveryProtocol.History,
        entry.state = some
          (CommitRecoveryState.atPoint current.saved current.entryExcluded current.generation) ∧
        TracePrefix entry.trace trace ∧
          trace.length + ProtocolState.remaining setup.program current.point =
            entry.trace.length + ProtocolState.remaining setup.program current.saved := by
  induction trace with
  | start => intro current impossible; cases impossible
  | @extend before after prior joint legal supported ih =>
      intro current equal committing
      subst after
      cases before with
      | none =>
          obtain ⟨input, _member, result⟩ := (PMF.mem_support_map_iff
            (fun input => some (CommitRecoveryState.atPoint
              (ProtocolState.entry setup.program (setup.initialConfig input)) ∅ 0))
            setup.initialLaw _).mp supported
          cases Option.some.inj result
          exact ⟨⟨_, prior.extend joint legal supported⟩, rfl, .refl, rfl⟩
      | some previous =>
          change _ ∈ ((previous.step joint).map some).support at supported
          obtain ⟨next, nextMember, nextEq⟩ :=
            (PMF.mem_support_map_iff some (previous.step joint) _).mp supported
          cases Option.some.inj nextEq
          let law := ProtocolState.recoveryStep setup.program previous.point previous.excluded joint
          let monotone := fun result (member : result ∈ law.support) =>
            ProtocolState.recoveryStep_excluded_monotone setup.program previous.point
              previous.excluded joint result member
          obtain ⟨result, member, imageEq⟩ := (PMF.mem_support_map_iff
            (fun result : {result : SourceProgram.ProtocolState setup.program × Finset Player //
                previous.excluded ⊆ result.2} => (previous.install result.1 result.2).close)
            (pmfToSubtype law monotone) current).mp nextMember
          have raw : result.1 ∈ (ProtocolState.recoveryStep setup.program previous.point
              previous.excluded joint).support := by
            rw [← map_val_pmfToSubtype
              (ProtocolState.recoveryStep setup.program previous.point previous.excluded joint)
              (fun result supported => ProtocolState.recoveryStep_excluded_monotone setup.program
                previous.point previous.excluded joint result supported)]
            exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
          subst current
          let installed := previous.install result.1 result.2
          have atCheckpoint (closed : ∃ point excluded generation,
              installed.close = CommitRecoveryState.atPoint point excluded generation) :
              ∃ entry : setup.commitRecoveryProtocol.History,
                entry.state = some (CommitRecoveryState.atPoint installed.close.saved
                  installed.close.entryExcluded installed.close.generation) ∧
                TracePrefix entry.trace (prior.extend joint legal supported) ∧
                (prior.extend joint legal supported).length +
                    ProtocolState.remaining setup.program installed.close.point =
                  entry.trace.length +
                    ProtocolState.remaining setup.program installed.close.saved := by
            refine ⟨⟨_, prior.extend joint legal supported⟩, ?_, .refl, ?_⟩
            · obtain ⟨point, excluded, generation, closed⟩ := closed
              change some installed.close = some _
              rw [closed]
              rfl
            · obtain ⟨point, excluded, generation, closed⟩ := closed
              change prior.length + 1 +
                  ProtocolState.remaining setup.program installed.close.point =
                prior.length + 1 + ProtocolState.remaining setup.program installed.close.saved
              rw [closed]
              rfl
          by_cases finished : installed.Finished
          · by_cases failed : installed.NewFailure
            · by_cases survives : installed.Survives
              · exact atCheckpoint ⟨_, _, _, installed.close_of_retry finished failed survives⟩
              · exact atCheckpoint ⟨_, _, _, installed.close_of_exhausted finished failed survives⟩
            · apply atCheckpoint
              refine ⟨installed.point, installed.excluded, installed.generation, ?_⟩
              simp only [CommitRecoveryState.close, finished, failed, ↓reduceIte]
          · by_cases savedCommit : ProtocolState.atCommit setup.program installed.saved = true
            · have unchanged : installed.close = installed := by
                simp only [CommitRecoveryState.close, finished, savedCommit, ↓reduceIte]
              have previousCommit : ProtocolState.atCommit setup.program previous.point = true := by
                rcases setup.commitRecovery_blockFrontier prior with
                  ⟨_saved, live, _end⟩ | same
                · exact live
                · rw [← same]
                  exact savedCommit
              obtain ⟨entry, entryState, retained, rank⟩ := ih previous rfl previousCommit
              have consumed := ProtocolState.recoveryStep_remaining setup.program previous.point
                previous.excluded joint result.1 legal.1 raw
              refine ⟨entry, ?_, .extend retained joint legal supported, ?_⟩
              · change entry.state = some (CommitRecoveryState.atPoint installed.close.saved
                  installed.close.entryExcluded installed.close.generation)
                rw [unchanged]
                exact entryState
              · change (prior.extend joint legal supported).length +
                    ProtocolState.remaining setup.program installed.close.point =
                  entry.trace.length + ProtocolState.remaining setup.program installed.close.saved
                simp only [Trace.length]
                rw [unchanged]
                change prior.length + 1 + ProtocolState.remaining setup.program result.1.1 =
                  entry.trace.length + ProtocolState.remaining setup.program previous.saved
                omega
            · apply atCheckpoint
              refine ⟨installed.point, installed.excluded, installed.generation, ?_⟩
              simp only [CommitRecoveryState.close, finished, savedCommit, Bool.false_eq_true,
                ↓reduceIte]

/-- A genuine current commitment history retains its exact literal saved-entry
history, with one source transition for every consumed commitment instruction. -/
theorem commitRecovery_attempt_entry
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true) :
    ∃ entryTrace : setup.commitRecoveryProtocol.Trace
        (some (CommitRecoveryState.atPoint current.saved current.entryExcluded current.generation)),
      TracePrefix entryTrace trace ∧
        trace.length + ProtocolState.remaining setup.program current.point =
          entryTrace.length + ProtocolState.remaining setup.program current.saved :=
  by
  obtain ⟨⟨entryState, entryTrace⟩, sameState, retained, rank⟩ :=
    setup.attempt_entry_of_trace trace current rfl committing
  cases sameState
  exact ⟨entryTrace, retained, rank⟩

end Vegas.SourceProgram.Setup
