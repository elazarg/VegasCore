/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoverySavedObservation
import Vegas.Game.CommitRecoveryAncillaryBelief

/-! # Semantic saved states of actual source-history exchanges

A surviving owner's saved typed view is read from its current view at the
actual public saved rank. Erasing private recall commutes with that readback.
This identifies both semantic cursors of the original supported exchange.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolView

private theorem entryView_erase (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (view : ProtocolView who program),
      entryView who program (eraseHistory who program view) =
        ((entryView who program view).1, [])
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, view => by
      cases view with
      | inl current => rfl
      | inr later =>
          simp only [entryView, eraseHistory, Sum.elim_inr, entryView_erase who next,
            DecisionView.back, List.dropLast_nil, ite_self]
  | _, _, .commit _ owner _ _ next, view => by
      cases view with
      | inl current => rfl
      | inr later =>
          simp only [entryView, eraseHistory, Sum.elim_inr, entryView_erase who next,
            DecisionView.back, List.dropLast_nil, ite_self]
  | _, _, .reveal _ owner _ _ _ _ next, view => by
      cases view with
      | inl current => rfl
      | inr later =>
          simp only [entryView, eraseHistory, Sum.elim_inr, entryView_erase who next,
            DecisionView.back, List.dropLast_nil, ite_self]

/-- Reading the actual earlier source rank and erasing private recall commute. -/
theorem atRank_eraseHistory (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (rank : Nat) (view : ProtocolView who program),
      atRank who program rank (eraseHistory who program view) =
        (atRank who program rank view).map (eraseHistory who program)
  | _, _, .ret _, rank, view => by cases rank <;> rfl
  | _, _, .sample _ _ _ next, rank, view => by
      cases rank with
      | zero =>
          simp only [atRank, Option.map_some]
          rw [entryView_erase]
          rfl
      | succ rank =>
          cases view with
          | inl current => rfl
          | inr later =>
              simp only [atRank, eraseHistory, Sum.elim_inr, atRank_eraseHistory who next,
                Option.map_map, Function.comp_def]
  | _, _, .commit _ _ _ _ next, rank, view => by
      cases rank with
      | zero =>
          simp only [atRank, Option.map_some]
          rw [entryView_erase]
          rfl
      | succ rank =>
          cases view with
          | inl current => rfl
          | inr later =>
              simp only [atRank, eraseHistory, Sum.elim_inr, atRank_eraseHistory who next,
                Option.map_map, Function.comp_def]
  | _, _, .reveal _ _ _ _ _ _ next, rank, view => by
      cases rank with
      | zero =>
          simp only [atRank, Option.map_some]
          rw [entryView_erase]
          rfl
      | succ rank =>
          cases view with
          | inl current => rfl
          | inr later =>
              simp only [atRank, eraseHistory, Sum.elim_inr, atRank_eraseHistory who next,
                Option.map_map, Function.comp_def]

end ProtocolView

namespace ProtocolState

omit [IExpr.ResultTypes L] in
private theorem config_splice_erase {Γ : SourceCtx Player L} (who : Player)
    (mine others : Config Player L Γ)
    (same : sourceObserve who mine.state = sourceObserve who others.state) :
    { Config.splice who mine others with history := fun _ => [] } =
      { others with history := fun _ => [] } := by
  have cells := splice_of_hiddenAgree (hiddenAgree_of_sourceObserve_eq who _ _ same)
  change Config.mk (SourceProgram.splice who mine.state others.state)
      others.registry others.revelations (fun _ => []) =
    Config.mk others.state others.registry others.revelations (fun _ => [])
  rw [cells]

/-- Replacing one owner's live typed cells by the same observed cells changes
only private recall, even when the original configurations have other hidden values. -/
theorem splice_eraseHistory_of_observe_eq (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (mine others : ProtocolState program),
      ProtocolView.eraseHistory who program (observe who program mine) =
          ProtocolView.eraseHistory who program (observe who program others) →
      withHistory program (splice who program mine others) (fun _ => []) =
        withHistory program others (fun _ => [])
  | _, _, .ret _, mine, others, same =>
      config_splice_erase who mine others (congrArg Prod.fst same)
  | _, _, .sample _ _ _ next, mine, others, same => by
      cases mine <;> cases others
      · exact congrArg Sum.inl (config_splice_erase who _ _
          (congrArg Prod.fst (Sum.inl.inj same)))
      · cases same
      · cases same
      · exact congrArg Sum.inr (splice_eraseHistory_of_observe_eq who next _ _ (Sum.inr.inj same))
  | _, _, .commit _ _ _ _ next, mine, others, same => by
      cases mine <;> cases others
      · exact congrArg Sum.inl (config_splice_erase who _ _
          (congrArg Prod.fst (Sum.inl.inj same)))
      · cases same
      · cases same
      · exact congrArg Sum.inr (splice_eraseHistory_of_observe_eq who next _ _ (Sum.inr.inj same))
  | _, _, .reveal _ _ _ _ _ _ next, mine, others, same => by
      cases mine <;> cases others
      · exact congrArg Sum.inl (config_splice_erase who _ _
          (congrArg Prod.fst (Sum.inl.inj same)))
      · cases same
      · cases same
      · exact congrArg Sum.inr (splice_eraseHistory_of_observe_eq who next _ _ (Sum.inr.inj same))

end ProtocolState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

private theorem current_view (who : Player) {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.commitRecoveryModel.infoOf who trace).1.1.1 = setup.commitRecoveryPrivate who state := by
  change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who trace).1.1.1 = _
  rw [InfoSignals.withOwnPlayRecall_infoOf]
  exact congrArg Prod.fst (setup.commitRecoverySignals_current who trace)

/-- The actual supported owner substitution preserves BOTH erased semantic
cursors. The saved-state equality is derived from genuine saved-rank readback,
not assumed as a continuation-coupling premise. -/
theorem commitRecovery_splice_erased_state_eq (who : Player)
    (mine others : CommitRecoveryState setup.program)
    (mineTrace : setup.commitRecoveryProtocol.Trace (some mine))
    (othersTrace : setup.commitRecoveryProtocol.Trace (some others))
    (mineSurvives : who ∉ mine.excluded) (othersSurvives : who ∉ others.excluded)
    (same : setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who mineTrace) =
      setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who othersTrace)) :
    (CommitRecoveryState.splice who mine others).eraseHistory = others.eraseHistory := by
  have views := congrArg (fun info => info.1.1.1) same
  change ((setup.commitRecoveryModel.infoOf who mineTrace).1.1.1.map
      (ProtocolView.eraseHistory who setup.program)) =
    ((setup.commitRecoveryModel.infoOf who othersTrace).1.1.1.map
      (ProtocolView.eraseHistory who setup.program)) at views
  rw [setup.current_view, setup.current_view] at views
  have current := Option.some.inj views
  have publicWord := setup.commitRecovery_publicRecall_eq_of_erasedInformation_eq who
    mineTrace othersTrace same
  have metadata := setup.commitRecovery_metadata_of_publicRecall who
    mineTrace othersTrace publicWord
  have savedRank := congrArg (fun remaining => instructionCount setup.program - remaining)
    (ProtocolState.MetadataEq.controls setup.program _ _ metadata.2.1).1
  have leftRead := congrArg (Option.map (ProtocolView.eraseHistory who setup.program))
    (setup.commitRecovery_saved_rank who mineTrace mineSurvives)
  have rightRead := congrArg (Option.map (ProtocolView.eraseHistory who setup.program))
    (setup.commitRecovery_saved_rank who othersTrace othersSurvives)
  rw [← ProtocolView.atRank_eraseHistory, savedRank, current] at leftRead
  rw [← ProtocolView.atRank_eraseHistory] at rightRead
  have saved := Option.some.inj (leftRead.symm.trans rightRead)
  have currentEq := ProtocolState.splice_eraseHistory_of_observe_eq who setup.program
    mine.point others.point current
  have savedEq := ProtocolState.splice_eraseHistory_of_observe_eq who setup.program
    mine.saved others.saved saved
  simp only [CommitRecoveryState.splice, CommitRecoveryState.eraseHistory,
    currentEq, savedEq]

end Setup
end Vegas.SourceProgram
