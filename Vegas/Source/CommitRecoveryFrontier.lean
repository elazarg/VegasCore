/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryDebt

/-! # Actual source recovery checkpoints follow maximal commitment boundaries -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

theorem commitEnd_le_remaining : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program),
    commitEnd program point ≤ remaining program point
  | _, _, .ret _, _ => le_rfl
  | _, _, .sample _ _ _ next, point => by
      cases point with
      | inl _ => exact le_rfl
      | inr point => exact commitEnd_le_remaining next point
  | _, _, .commit name owner _ _ next, point => by
      cases point with
      | inl config =>
          have bound := commitEnd_le_remaining next
            (entry next (automaticCommit name owner _ config))
          simp only [commitEnd_entry, remaining_entry] at bound
          change instructionCount (commitPhase next).suffix ≤ instructionCount next + 1
          omega
      | inr point => exact commitEnd_le_remaining next point
  | _, _, .reveal _ _ _ _ _ _ next, point => by
      cases point with
      | inl _ => exact le_rfl
      | inr point => exact commitEnd_le_remaining next point

/-- A point inside a commitment block has not yet reached that block's end. -/
theorem commitEnd_lt_remaining : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program),
    atCommit program point = true → commitEnd program point < remaining program point
  | _, _, .ret _, _, committing => by cases committing
  | _, _, .sample _ _ _ next, point, committing => by
      cases point with
      | inl _ => cases committing
      | inr point => exact commitEnd_lt_remaining next point committing
  | _, _, .commit name owner _ _ next, point, committing => by
      cases point with
      | inl config =>
          have bound := commitEnd_le_remaining next
            (entry next (automaticCommit name owner _ config))
          simp only [commitEnd_entry, remaining_entry] at bound
          change instructionCount (commitPhase next).suffix < instructionCount next + 1
          omega
      | inr point => exact commitEnd_lt_remaining next point committing
  | _, _, .reveal _ _ _ _ _ _ next, point, committing => by
      cases point with
      | inl _ => cases committing
      | inr point => exact commitEnd_lt_remaining next point committing

/-- The entry of any residual syntax either begins another commit or is the
boundary where the preceding contiguous commitment block ends. -/
theorem entry_commit_cursor : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ),
    (atCommit program (entry program config) = true ∧
      commitEnd program (entry program config) = instructionCount (commitPhase program).suffix) ∨
    (atCommit program (entry program config) = false ∧
      remaining program (entry program config) = instructionCount (commitPhase program).suffix)
  | _, _, .ret _, _ => Or.inr ⟨rfl, rfl⟩
  | _, _, .sample _ _ _ _, _ => Or.inr ⟨rfl, rfl⟩
  | _, _, .commit _ _ _ _ _, _ => Or.inl ⟨rfl, rfl⟩
  | _, _, .reveal _ _ _ _ _ _ _, _ => Or.inr ⟨rfl, rfl⟩

/-- An actual commit instruction either stays in the same maximal block or
lands at its exact end. Automatic excluded slots and bad values behave alike. -/
theorem recoveryStep_commit_cursor : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState program × Finset Player),
    atCommit program point = true →
    result ∈ (recoveryStep program point excluded joint).support →
    (atCommit program result.1 = true ∧ commitEnd program result.1 = commitEnd program point) ∨
      (atCommit program result.1 = false ∧ remaining program result.1 = commitEnd program point)
  | _, _, .ret _, _, _, _, _, committing, _ => by cases committing
  | _, _, .sample _ _ _ next, point, excluded, joint, result, committing, reached => by
      cases point with
      | inl _ => cases committing
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact recoveryStep_commit_cursor next point excluded joint after committing supported
  | _, _, .commit _ _ _ _ next, point, excluded, joint, result, committing, reached => by
      cases point with
      | inl config =>
          simp only [recoveryStep, Sum.elim_inl] at reached
          split at reached <;> rw [PMF.mem_support_pure_iff] at reached <;> cases reached
          all_goals exact entry_commit_cursor next _
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact recoveryStep_commit_cursor next point excluded joint after committing supported
  | _, _, .reveal _ _ _ _ _ _ next, point, excluded, joint, result, committing, reached => by
      cases point with
      | inl _ => cases committing
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact recoveryStep_commit_cursor next point excluded joint after committing supported

end ProtocolState

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId}
  {program : SourceProgram Player L Γ O}

/-- Saved and live points are equal except while the same commitment block is
being filled. Its syntactic endpoint remains fixed throughout that attempt. -/
def BlockFrontier (state : CommitRecoveryState program) : Prop :=
  (ProtocolState.atCommit program state.saved = true ∧
    ProtocolState.atCommit program state.point = true ∧
    ProtocolState.commitEnd program state.point = ProtocolState.commitEnd program state.saved) ∨
      state.saved = state.point

theorem atPoint_blockFrontier (point : ProtocolState program) (excluded : Finset Player)
    (generation : Nat) : (atPoint point excluded generation).BlockFrontier := Or.inr rfl

/-- At a noncommit point the current semantic state has already been saved. -/
theorem BlockFrontier.saved_eq_point_of_not_atCommit {state : CommitRecoveryState program}
    (valid : state.BlockFrontier) (notCommit : ProtocolState.atCommit program state.point = false) :
    state.saved = state.point := by
  rcases valid with ⟨_saved, live, _end⟩ | same
  · exact (Bool.false_ne_true (notCommit.symm.trans live)).elim
  · exact same

/-- One actual source instruction and its real closure preserve the saved
maximal-block frontier; no intendedness or clear-exclusion hypothesis is used. -/
theorem step_blockFrontier (state : CommitRecoveryState program) (valid : state.BlockFrontier)
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (supported : next ∈ (state.step joint).support) : next.BlockFrontier := by
  obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have raw : result.1 ∈
      (ProtocolState.recoveryStep program state.point state.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program state.point state.excluded joint)
      (fun result supported => ProtocolState.recoveryStep_excluded_monotone program state.point
        state.excluded joint result supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  let image := state.install result.1 result.2
  by_cases savedCommit : ProtocolState.atCommit program state.saved = true
  · have liveCommit : ProtocolState.atCommit program state.point = true := by
      rcases valid with ⟨_saved, live, _end⟩ | same
      · exact live
      · rwa [← same]
    have endpoint : ProtocolState.commitEnd program state.point =
        ProtocolState.commitEnd program state.saved := by
      rcases valid with ⟨_saved, _live, endpoint⟩ | same
      · exact endpoint
      · rw [same]
    rcases ProtocolState.recoveryStep_commit_cursor program state.point state.excluded joint
      result.1 liveCommit raw with ⟨committing, sameEnd⟩ | ⟨_notCommit, reachedEnd⟩
    · have atEnd : ProtocolState.commitEnd program result.1.1 =
          ProtocolState.commitEnd program state.saved := sameEnd.trans endpoint
      have unfinished : ¬ image.Finished := by
        intro completed
        have below := ProtocolState.commitEnd_lt_remaining program result.1.1 committing
        rw [atEnd] at below
        have equal : ProtocolState.remaining program result.1.1 =
            ProtocolState.commitEnd program state.saved := completed.2
        omega
      have imageCommit : ProtocolState.atCommit program image.saved = true := savedCommit
      have unchanged : image.close = image := by
        unfold close
        rw [ite_eq_right unfinished, ite_eq_left imageCommit]
      rw [unchanged]
      exact Or.inl ⟨savedCommit, committing, atEnd⟩
    · have completed : image.Finished := ⟨savedCommit, reachedEnd.trans endpoint⟩
      change image.close.BlockFrontier
      unfold close
      rw [ite_eq_left completed]
      split
      · split <;> exact Or.inr rfl
      · exact Or.inr rfl
  · have unfinished : ¬ image.Finished := fun completed => savedCommit completed.1
    have imageCommit : ¬ ProtocolState.atCommit program image.saved = true := savedCommit
    change image.close.BlockFrontier
    unfold close
    rw [ite_eq_right unfinished, ite_eq_right imageCommit]
    exact Or.inr rfl

end CommitRecoveryState

namespace Setup

/-- Every actual initialized source recovery history has the saved/live
maximal-block frontier, including all legal histories with zero policy weight. -/
theorem commitRecovery_blockFrontier (setup : Setup (Player := Player) (L := L))
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    state.elim True (fun current => current.BlockFrontier) := by
  induction trace with
  | start => trivial
  | @extend before after prior joint _ supported ih =>
      cases before with
      | none =>
          obtain ⟨inputs, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact Or.inr rfl
      | some previous =>
          obtain ⟨next, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact previous.step_blockFrontier ih joint next member

end Setup
end Vegas.SourceProgram
