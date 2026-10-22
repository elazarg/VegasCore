/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoverySavedObservation
import Vegas.Source.CommitRecoveryOwnHistory
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Saved source frontiers never move backwards along surviving play -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

theorem close_saved_remaining_le
    {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}
    (state : CommitRecoveryState program)
    (within : ProtocolState.remaining program state.point ≤
      ProtocolState.remaining program state.saved) :
    ProtocolState.remaining program state.close.saved ≤
      ProtocolState.remaining program state.saved := by
  classical
  unfold CommitRecoveryState.close
  split
  · split
    · split
      · simp only [CommitRecoveryState.retry, CommitRecoveryState.atPoint,
          CommitRecoveryState.restored, ProtocolState.remaining_withHistory, le_refl]
      · simp only [CommitRecoveryState.exhausted, CommitRecoveryState.atPoint,
          ProtocolState.automaticCommitBlock_remaining, CommitRecoveryState.restored,
          ProtocolState.commitEnd_withHistory]
        exact ProtocolState.commitEnd_le_remaining program state.saved
    · exact within
  · split
    · exact le_rfl
    · exact within

private theorem saved_remaining_step
    (setup : Setup (Player := Player) (L := L)) (who : Player)
    {before after : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace before)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal before joint)
    (supported : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support)
    (survives : who ∉ (setup.commitRecoveryPublic after).1) :
    after.elim (instructionCount setup.program)
        (fun current => ProtocolState.remaining setup.program current.saved) ≤
      before.elim (instructionCount setup.program)
        (fun current => ProtocolState.remaining setup.program current.saved) := by
  cases before with
  | none =>
      obtain ⟨draw, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      simp only [Option.elim_some, Option.elim_none, CommitRecoveryState.atPoint,
        ProtocolState.remaining_entry, le_refl]
  | some previous =>
      obtain ⟨next, nextMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      have active : who ∉ previous.excluded := fun excluded =>
        survives (previous.step_excluded_monotone joint next nextMember excluded)
      have readback := setup.commitRecovery_saved_rank who trace active
      have atRank := ProtocolView.atRank_le_position who setup.program _ _ _ readback
      have position := ProtocolView.position_add_remaining who setup.program previous.point
      have bounded := ProtocolState.remaining_le_instructionCount setup.program previous.saved
      have within : ProtocolState.remaining setup.program previous.point ≤
          ProtocolState.remaining setup.program previous.saved := by omega
      obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp nextMember
      have raw : result.1 ∈ (ProtocolState.recoveryStep setup.program previous.point
          previous.excluded joint).support := by
          rw [← map_val_pmfToSubtype
            (ProtocolState.recoveryStep setup.program previous.point previous.excluded joint)
            (fun result supported => ProtocolState.recoveryStep_excluded_monotone setup.program
              previous.point previous.excluded joint result supported)]
          exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
      have consumed := ProtocolState.recoveryStep_remaining setup.program previous.point
        previous.excluded joint result.1 legal.1 raw
      exact close_saved_remaining_le (previous.install result.1 result.2) (by
        change ProtocolState.remaining setup.program result.1.1 ≤
          ProtocolState.remaining setup.program previous.saved
        omega)

namespace Setup

/-- A surviving owner's actual source extension cannot return to an earlier
saved instruction frontier, even through retries and exhausted reconstruction. -/
theorem commitRecovery_saved_remaining_le_of_prefix
    (setup : Setup (Player := Player) (L := L)) (who : Player)
    {first last : setup.commitRecoveryProtocol.State}
    (firstTrace : setup.commitRecoveryProtocol.Trace first)
    (lastTrace : setup.commitRecoveryProtocol.Trace last)
    (retained : TracePrefix firstTrace lastTrace)
    (survives : who ∉ (setup.commitRecoveryPublic last).1) :
    last.elim (instructionCount setup.program)
        (fun current => ProtocolState.remaining setup.program current.saved) ≤
      first.elim (instructionCount setup.program)
        (fun current => ProtocolState.remaining setup.program current.saved) := by
  induction retained with
  | refl => exact le_rfl
  | @extend before after prior earlier joint legal supported ih =>
      have active : who ∉ (setup.commitRecoveryPublic before).1 := fun excluded =>
        survives (setup.commitRecovery_step_excluded_subset joint legal supported excluded)
      exact (saved_remaining_step setup who prior joint legal supported survives).trans (ih active)

end Setup
end Vegas.SourceProgram
