/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryLift
import Vegas.Source.SetupProtocolRecall

/-! # Observable control of clear source recovery steps -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- The instruction shape and commitment-block endpoint depend only on the
program counter, never on the contents of the source store. -/
theorem commitControl_eq_of_remaining :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
      remaining program first = remaining program second →
        atCommit program first = atCommit program second ∧
          commitEnd program first = commitEnd program second
  | _, _, .ret _, _, _, _ => ⟨rfl, rfl⟩
  | _, _, .sample _ _ _ next, first, second, same => by
      cases first with
      | inl _ =>
          cases second with
          | inl _ => exact ⟨rfl, rfl⟩
          | inr second =>
              have bound := remaining_le_instructionCount next second
              simp only [remaining, Sum.elim_inl, Sum.elim_inr] at same
              omega
      | inr first =>
          cases second with
          | inl _ =>
              have bound := remaining_le_instructionCount next first
              simp only [remaining, Sum.elim_inl, Sum.elim_inr] at same
              omega
          | inr second => exact commitControl_eq_of_remaining next first second same
  | _, _, .commit _ _ _ _ next, first, second, same => by
      cases first with
      | inl _ =>
          cases second with
          | inl _ => exact ⟨rfl, rfl⟩
          | inr second =>
              have bound := remaining_le_instructionCount next second
              simp only [remaining, Sum.elim_inl, Sum.elim_inr] at same
              omega
      | inr first =>
          cases second with
          | inl _ =>
              have bound := remaining_le_instructionCount next first
              simp only [remaining, Sum.elim_inl, Sum.elim_inr] at same
              omega
          | inr second => exact commitControl_eq_of_remaining next first second same
  | _, _, .reveal _ _ _ _ _ _ next, first, second, same => by
      cases first with
      | inl _ =>
          cases second with
          | inl _ => exact ⟨rfl, rfl⟩
          | inr second =>
              have bound := remaining_le_instructionCount next second
              simp only [remaining, Sum.elim_inl, Sum.elim_inr] at same
              omega
      | inr first =>
          cases second with
          | inl _ =>
              have bound := remaining_le_instructionCount next first
              simp only [remaining, Sum.elim_inl, Sum.elim_inr] at same
              omega
          | inr second => exact commitControl_eq_of_remaining next first second same

end ProtocolState

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

theorem advanceClear_saved_remaining (state : CommitRecoveryState program)
    (clear : state.excluded = ∅) (point : ProtocolState program) :
    ProtocolState.remaining program (state.advanceClear clear point).saved =
      if ProtocolState.atCommit program state.saved = true ∧
          ProtocolState.remaining program point = ProtocolState.commitEnd program state.saved then
        ProtocolState.remaining program point
      else if ProtocolState.atCommit program state.saved then
        ProtocolState.remaining program state.saved else ProtocolState.remaining program point := by
  simp only [advanceClear, close, Finished, NewFailure, install, Finset.empty_sdiff,
    Finset.not_nonempty_empty, ↓reduceIte]
  split
  · rfl
  · split <;> rfl

theorem advanceClear_saved_remaining_eq (first second : CommitRecoveryState program)
    (firstClear : first.excluded = ∅) (secondClear : second.excluded = ∅)
    (firstPoint secondPoint : ProtocolState program)
    (saved : ProtocolState.remaining program first.saved =
      ProtocolState.remaining program second.saved)
    (point : ProtocolState.remaining program firstPoint =
      ProtocolState.remaining program secondPoint) :
    ProtocolState.remaining program (first.advanceClear firstClear firstPoint).saved =
      ProtocolState.remaining program (second.advanceClear secondClear secondPoint).saved := by
  obtain ⟨kind, endpoint⟩ := ProtocolState.commitControl_eq_of_remaining program
    first.saved second.saved saved
  rw [advanceClear_saved_remaining, advanceClear_saved_remaining, kind, endpoint, saved, point]

end CommitRecoveryState

namespace Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable (setup : Setup (Player := Player) (L := L))

theorem protocolRemaining_eq_of_observe (who : Player) (first second : setup.ProtocolState)
    (same : setup.protocolObserve who first = setup.protocolObserve who second) :
    setup.protocolRemaining first = setup.protocolRemaining second := by
  cases first with
  | none => cases second with
    | none => rfl
    | some _ => cases same
  | some first => cases second with
    | none => cases same
    | some second =>
        have views := Option.some.inj same
        have left := ProtocolView.position_add_remaining who setup.program first
        have right := ProtocolView.position_add_remaining who setup.program second
        rw [views] at left
        change ProtocolState.remaining setup.program first =
          ProtocolState.remaining setup.program second
        omega

theorem commitRecoveryPrivate_source (who : Player) (state : setup.commitRecoveryProtocol.State) :
    setup.commitRecoveryPrivate who state =
      setup.protocolObserve who (setup.commitRecoverySourceState state) := by
  cases state <;> rfl

/-- Clear phase closure carries no new source information: its public saved
rank is determined by the prior public rank and the next source observation. -/
theorem commitRecoveryLiftSuccessor_public (who : Player)
    (first second : setup.commitRecoveryProtocol.State)
    (firstClear : setup.CommitRecoveryClear first) (secondClear : setup.CommitRecoveryClear second)
    (privateView : setup.commitRecoveryPrivate who first = setup.commitRecoveryPrivate who second)
    (publicView : setup.commitRecoveryPublic first = setup.commitRecoveryPublic second)
    (firstPoint secondPoint : setup.ProtocolState)
    (nextView : setup.protocolObserve who firstPoint = setup.protocolObserve who secondPoint) :
    setup.commitRecoveryPublic (setup.commitRecoveryLiftSuccessor first firstClear firstPoint) =
      setup.commitRecoveryPublic
        (setup.commitRecoveryLiftSuccessor second secondClear secondPoint) := by
  have point := setup.protocolRemaining_eq_of_observe who firstPoint secondPoint nextView
  cases firstPoint with
  | none =>
      cases secondPoint with
      | none => cases first <;> cases second <;> rfl
      | some _ => cases nextView
  | some firstPoint =>
      cases secondPoint with
      | none => cases nextView
      | some secondPoint =>
          change ProtocolState.remaining setup.program firstPoint =
            ProtocolState.remaining setup.program secondPoint at point
          cases first with
          | none =>
              cases second with
              | none =>
                  change (∅, 0, _) = (∅, 0, _)
                  simp only [CommitRecoveryState.atPoint, point]
              | some _ => cases privateView
          | some first =>
              cases second with
              | none => cases privateView
              | some second =>
                  have gen := congrArg (fun info => info.2.1) publicView
                  change first.generation = second.generation at gen
                  have rank := congrArg (fun info => info.2.2) publicView
                  have firstBound := ProtocolState.remaining_le_instructionCount
                    setup.program first.saved
                  have secondBound := ProtocolState.remaining_le_instructionCount
                    setup.program second.saved
                  change instructionCount setup.program -
                    ProtocolState.remaining setup.program first.saved =
                    instructionCount setup.program -
                      ProtocolState.remaining setup.program second.saved at rank
                  have saved : ProtocolState.remaining setup.program first.saved =
                      ProtocolState.remaining setup.program second.saved := by omega
                  have afterSaved := CommitRecoveryState.advanceClear_saved_remaining_eq
                    first second firstClear secondClear firstPoint secondPoint saved point
                  simp only [commitRecoveryLiftSuccessor, commitRecoveryPublic,
                    CommitRecoveryState.advanceClear_excluded,
                    CommitRecoveryState.advanceClear_generation, gen, afterSaved]

end Setup
end Vegas.SourceProgram
