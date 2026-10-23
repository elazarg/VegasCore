/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryRanks

/-! # Recovering genuine saved source views from surviving observations -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolView

/-- A successful earlier-rank observation cannot lie beyond the current source position. -/
theorem atRank_le_position (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (rank : Nat)
      (view result : ProtocolView who program),
      atRank who program rank view = some result → rank ≤ position who program view
  | _, _, .ret _, rank, view, result, same => by
      cases rank with
      | zero => exact Nat.zero_le _
      | succ rank =>
          simp only [atRank] at same
          cases same
  | _, _, .sample _ _ _ next, rank, view, result, same => by
      cases rank with
      | zero => exact Nat.zero_le _
      | succ rank =>
          cases view with
          | inl _ =>
              simp only [atRank, Sum.elim_inl] at same
              cases same
          | inr later =>
              cases read : atRank who next rank later with
              | none =>
                  simp only [atRank, Sum.elim_inr, read, Option.map_none] at same
                  cases same
              | some earlier =>
                  exact Nat.add_le_add_right
                    (atRank_le_position who next rank later earlier read) 1
  | _, _, .commit _ _ _ _ next, rank, view, result, same => by
      cases rank with
      | zero => exact Nat.zero_le _
      | succ rank =>
          cases view with
          | inl _ =>
              simp only [atRank, Sum.elim_inl] at same
              cases same
          | inr later =>
              cases read : atRank who next rank later with
              | none =>
                  simp only [atRank, Sum.elim_inr, read, Option.map_none] at same
                  cases same
              | some earlier =>
                  exact Nat.add_le_add_right
                    (atRank_le_position who next rank later earlier read) 1
  | _, _, .reveal _ _ _ _ _ _ next, rank, view, result, same => by
      cases rank with
      | zero => exact Nat.zero_le _
      | succ rank =>
          cases view with
          | inl _ =>
              simp only [atRank, Sum.elim_inl] at same
              cases same
          | inr later =>
              cases read : atRank who next rank later with
              | none =>
                  simp only [atRank, Sum.elim_inr, read, Option.map_none] at same
                  cases same
              | some earlier =>
                  exact Nat.add_le_add_right
                    (atRank_le_position who next rank later earlier read) 1

end ProtocolView

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId}
  {program : SourceProgram Player L Γ O}

private theorem atPoint_saved_rank (who : Player) (point : ProtocolState program)
    (excluded : Finset Player) (generation : Nat) :
    let state := atPoint point excluded generation
    ProtocolView.atRank who program
        (instructionCount program - ProtocolState.remaining program state.saved)
        (ProtocolState.observe who program state.point) =
      some (ProtocolState.observe who program state.saved) := by
  have position := ProtocolView.position_add_remaining who program point
  have rank : instructionCount program - ProtocolState.remaining program point =
      ProtocolView.position who program (ProtocolState.observe who program point) := by omega
  change ProtocolView.atRank who program
    (instructionCount program - ProtocolState.remaining program point)
    (ProtocolState.observe who program point) = some (ProtocolState.observe who program point)
  rw [rank, ProtocolView.atRank_position]

/-- Actual phase closure preserves the saved-view readback or saves the reached
point itself, including retry and exhausted automatic reconstruction. -/
theorem close_saved_rank (state : CommitRecoveryState program) (who : Player)
    (readback : ProtocolView.atRank who program
      (instructionCount program - ProtocolState.remaining program state.saved)
      (ProtocolState.observe who program state.point) =
        some (ProtocolState.observe who program state.saved)) :
    ProtocolView.atRank who program
        (instructionCount program - ProtocolState.remaining program state.close.saved)
        (ProtocolState.observe who program state.close.point) =
      some (ProtocolState.observe who program state.close.saved) := by
  unfold close
  split
  · split
    · split
      · exact atPoint_saved_rank who state.restored state.excluded (state.generation + 1)
      · exact atPoint_saved_rank who
          (ProtocolState.automaticCommitBlock program state.restored)
          state.excluded state.generation
    · exact atPoint_saved_rank who state.point state.excluded state.generation
  · split
    · exact readback
    · exact atPoint_saved_rank who state.point state.excluded state.generation

/-- A genuine supported recovery instruction retains the saved observation of
an owner who survives it; no intendedness or equality of physical exclusions is used. -/
theorem step_saved_rank (state : CommitRecoveryState program) (who : Player)
    (readback : ProtocolView.atRank who program
      (instructionCount program - ProtocolState.remaining program state.saved)
      (ProtocolState.observe who program state.point) =
        some (ProtocolState.observe who program state.saved))
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (supported : next ∈ (state.step joint).support) (survives : who ∉ next.excluded) :
    ProtocolView.atRank who program
        (instructionCount program - ProtocolState.remaining program next.saved)
        (ProtocolState.observe who program next.point) =
      some (ProtocolState.observe who program next.saved) := by
  obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have raw : result.1 ∈
      (ProtocolState.recoveryStep program state.point state.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program state.point state.excluded joint)
      (fun result supported => ProtocolState.recoveryStep_excluded_monotone program state.point
        state.excluded joint result supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  have live : who ∉ result.1.2 := by
    simpa only [close_excluded, install] using survives
  have previous : who ∉ state.excluded := fun excluded => live (result.2 excluded)
  have within := ProtocolView.atRank_le_position who program _ _ _ readback
  have retained := ProtocolView.atRank_recoveryStep who program state.point state.excluded joint
    result.1 raw previous _ within
  apply close_saved_rank
  exact retained.trans readback

end CommitRecoveryState

namespace Setup

/-- Every genuine initialized recovery source history reveals the surviving
owner's exact saved view at its saved instruction rank. Retired attempts and
processed omission flags remain in the original source trace. -/
theorem commitRecovery_saved_rank (setup : Setup (Player := Player) (L := L))
    (who : Player) {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    state.elim True (fun current => who ∉ current.excluded →
      ProtocolView.atRank who setup.program
          (instructionCount setup.program - ProtocolState.remaining setup.program current.saved)
          (ProtocolState.observe who setup.program current.point) =
        some (ProtocolState.observe who setup.program current.saved)) := by
  induction trace with
  | start => trivial
  | @extend before after prior joint _ supported ih =>
      cases before with
      | none =>
          obtain ⟨inputs, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          intro _survives
          exact CommitRecoveryState.atPoint_saved_rank who _ _ _
      | some previous =>
          obtain ⟨next, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          intro survives
          have before : who ∉ previous.excluded := fun excluded =>
            survives (previous.step_excluded_monotone joint next member excluded)
          exact previous.step_saved_rank who (ih before) joint next member survives

end Setup
end Vegas.SourceProgram
