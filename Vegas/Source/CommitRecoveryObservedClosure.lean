/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryOwnHistory
import Vegas.Source.CommitRecoveryObservation
import Vegas.Source.CommitBlockInformation

/-! # Full owner observations across actual source phase closure -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

omit [IExpr.ResultTypes L] in
/-- Automatic excluded bindings preserve equality of the observer's existing
view and add the same unavailable cell without recording an original own action. -/
theorem view_automaticCommit_congr {Γ : SourceCtx Player L} (who owner : Player)
    (name : VarId) (payload : L.Ty) (first second : Config Player L Γ)
    (before : first.view who = second.view who) :
    (automaticCommit name owner payload first).view who =
      (automaticCommit name owner payload second).view who := by
  apply Prod.ext
  · apply congrArg SourceObservation.mk
    funext readName readCell member
    cases member with
    | here => rfl
    | there member =>
        have previous := congrArg
          (fun view : DecisionView who Γ => view.1.cells readName readCell member) before
        cases readCell <;> exact previous
  · change first.history who = second.history who
    exact congrArg Prod.snd before

end Config

namespace ProtocolState

/-- Changing private action records preserves observation equality whenever
the actual observer's replacement word is the same. -/
theorem observe_withHistory_congr (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolState program)
      (left right : History Player L),
      observe who program first = observe who program second → left who = right who →
      observe who program (withHistory program first left) =
        observe who program (withHistory program second right)
  | _, _, .ret _, first, second, left, right, same, word => by
      have fields := congrArg Prod.fst same
      exact Prod.ext fields word
  | _, _, .sample _ _ _ next, first, second, left, right, same, word => by
      cases first <;> cases second
      · have old := Sum.inl.inj same
        have fields := congrArg Prod.fst old
        exact congrArg Sum.inl (Prod.ext fields word)
      · cases same
      · cases same
      · exact congrArg Sum.inr (observe_withHistory_congr who next _ _ left right
          (Sum.inr.inj same) word)
  | _, _, .commit _ _ _ _ next, first, second, left, right, same, word => by
      cases first <;> cases second
      · have old := Sum.inl.inj same
        have fields := congrArg Prod.fst old
        exact congrArg Sum.inl (Prod.ext fields word)
      · cases same
      · cases same
      · exact congrArg Sum.inr (observe_withHistory_congr who next _ _ left right
          (Sum.inr.inj same) word)
  | _, _, .reveal _ _ _ _ _ _ next, first, second, left, right, same, word => by
      cases first <;> cases second
      · have old := Sum.inl.inj same
        have fields := congrArg Prod.fst old
        exact congrArg Sum.inl (Prod.ext fields word)
      · cases same
      · cases same
      · exact congrArg Sum.inr (observe_withHistory_congr who next _ _ left right
          (Sum.inr.inj same) word)

/-- Equal actual entry configurations give equal source entry observations. -/
theorem observe_entry_congr {Γ : SourceCtx Player L} {O : Finset VarId}
    (who : Player) (program : SourceProgram Player L Γ O) (first second : Config Player L Γ)
    (same : first.view who = second.view who) :
    observe who program (entry program first) = observe who program (entry program second) := by
  cases program with
  | ret => exact same
  | sample => exact congrArg Sum.inl same
  | commit => exact congrArg Sum.inl same
  | reveal => exact congrArg Sum.inl same

/-- An automatic exhausted block is observed solely through its original
entry observation; hidden foreign records need not agree. -/
theorem automaticCommitBlock_observe_congr (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
      observe who program first = observe who program second →
      observe who program (automaticCommitBlock program first) =
        observe who program (automaticCommitBlock program second)
  | _, _, .ret _, _, _, same => same
  | _, _, .sample _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact same
      · cases same
      · cases same
      · exact congrArg Sum.inr (automaticCommitBlock_observe_congr who next _ _
          (Sum.inr.inj same))
  | _, _, .commit name owner fresh guard next, first, second, same => by
      cases first with
      | inl first =>
          cases second with
          | inl second =>
              exact congrArg Sum.inr (automaticCommitBlock_observe_congr who next _ _
                (observe_entry_congr who next _ _
                  (Config.view_automaticCommit_congr who owner name _ first second
                    (Sum.inl.inj same))))
          | inr second => cases same
      | inr first =>
          cases second with
          | inl second => cases same
          | inr second =>
              exact congrArg Sum.inr
                (automaticCommitBlock_observe_congr who next first second (Sum.inr.inj same))
  | _, _, .reveal _ _ _ _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact same
      · cases same
      · cases same
      · exact congrArg Sum.inr (automaticCommitBlock_observe_congr who next _ _
          (Sum.inr.inj same))

/-- The source commitment owner set is static at each observed program point. -/
theorem commitOwners_eq_of_observe (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
      observe who program first = observe who program second →
      commitOwners program first = commitOwners program second
  | _, _, .ret _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, first, second, same => by
      cases first <;> cases second
      · rfl
      · cases same
      · cases same
      · exact commitOwners_eq_of_observe who next _ _ (Sum.inr.inj same)
  | _, _, .commit _ _ _ _ next, first, second, same => by
      cases first <;> cases second
      · rfl
      · cases same
      · cases same
      · exact commitOwners_eq_of_observe who next _ _ (Sum.inr.inj same)
  | _, _, .reveal _ _ _ _ _ _ next, first, second, same => by
      cases first <;> cases second
      · rfl
      · cases same
      · cases same
      · exact commitOwners_eq_of_observe who next _ _ (Sum.inr.inj same)

end ProtocolState

namespace CommitRecoveryState

/-- Actual closure, retry and exhausted automatic rebuilding preserve the
same full observed source state when their genuine entry and live views agree. -/
theorem close_observed_congr {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} (who : Player)
    (first second : CommitRecoveryState program)
    (point : ProtocolState.observe who program first.point =
      ProtocolState.observe who program second.point)
    (saved : ProtocolState.observe who program first.saved =
      ProtocolState.observe who program second.saved)
    (excluded : first.excluded = second.excluded)
    (entryExcluded : first.entryExcluded = second.entryExcluded)
    (generation : first.generation = second.generation) :
    (ProtocolState.observe who program first.close.point,
        ProtocolState.observe who program first.close.saved, first.close.excluded,
        first.close.entryExcluded, first.close.generation) =
      (ProtocolState.observe who program second.close.point,
        ProtocolState.observe who program second.close.saved, second.close.excluded,
        second.close.entryExcluded, second.close.generation) := by
  have pointRank : ProtocolState.remaining program first.point =
      ProtocolState.remaining program second.point := by
    have left := ProtocolView.position_add_remaining who program first.point
    have right := ProtocolView.position_add_remaining who program second.point
    rw [point] at left
    omega
  have savedRank : ProtocolState.remaining program first.saved =
      ProtocolState.remaining program second.saved := by
    have left := ProtocolView.position_add_remaining who program first.saved
    have right := ProtocolView.position_add_remaining who program second.saved
    rw [saved] at left
    omega
  obtain ⟨committing, endpoint⟩ := ProtocolState.commitControl_eq_of_remaining program
    first.saved second.saved savedRank
  have finished : first.Finished = second.Finished := by
    unfold Finished
    rw [committing, pointRank, endpoint]
  have failed : first.NewFailure = second.NewFailure := by
    unfold NewFailure
    rw [excluded, entryExcluded]
  have survivors : first.Survives = second.Survives := by
    unfold Survives
    rw [ProtocolState.commitOwners_eq_of_observe who program first.saved second.saved saved,
      excluded]
  have restoredView : ProtocolState.observe who program first.restored =
      ProtocolState.observe who program second.restored :=
    ProtocolState.observe_withHistory_congr who program first.saved second.saved _ _ saved
      (ProtocolState.history_eq_of_observe who program first.point second.point point)
  have rebuilt := ProtocolState.automaticCommitBlock_observe_congr who program _ _ restoredView
  simp only [close, finished, failed, survivors, committing]
  split_ifs <;>
    simp_all [retry, exhausted, atPoint]

end CommitRecoveryState

end Vegas.SourceProgram
