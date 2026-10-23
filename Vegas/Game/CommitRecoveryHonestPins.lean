/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.IntendedErasedRecall
import Vegas.Game.CommitRecoverySpliceErasure
import Vegas.Game.CommitRecoveryInformationEmbedding

/-! # Honest information is retained by the normalized source pool key

The original honest view is reconstructed from current typed cells rather
than supplied as a pool-coherence premise. Thus arbitrary honest laws cannot
conflict when the actual normalized completion shares their query.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolView

private theorem entry_cells_erased (who : Player) {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) (view : ProtocolView who program) :
    (entryView who program (eraseHistory who program view)).1 =
      (entryView who program view).1 := by
  have prior := atRank_eraseHistory who program 0 view
  cases program with
  | ret => rfl
  | sample name fresh law next =>
      simp only [atRank, Option.map_some, eraseHistory] at prior
      have read := Sum.inl.inj (Option.some.inj prior)
      exact congrArg (fun view => view.1) read
  | commit name owner fresh guard next =>
      simp only [atRank, Option.map_some, eraseHistory] at prior
      have read := Sum.inl.inj (Option.some.inj prior)
      exact congrArg (fun view => view.1) read
  | reveal published owner name fresh source unresolved next =>
      simp only [atRank, Option.map_some, eraseHistory] at prior
      have read := Sum.inl.inj (Option.some.inj prior)
      exact congrArg (fun view => view.1) read

/-- Erasing remembered actions does not change their honest typed readback. -/
theorem intendedWord_eraseHistory (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (view : ProtocolView who program),
      intendedWord who program (eraseHistory who program view) = intendedWord who program view
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, view => by
      cases view <;> simp only [intendedWord, eraseHistory, Sum.elim_inl, Sum.elim_inr,
        intendedWord_eraseHistory who next]
  | _, _, .commit _ _ _ _ next, view => by
      cases view <;> simp only [intendedWord, eraseHistory, Sum.elim_inl, Sum.elim_inr,
        entry_cells_erased, intendedWord_eraseHistory who next]
  | _, _, .reveal _ _ _ _ _ _ next, view => by
      cases view <;> simp only [intendedWord, eraseHistory, Sum.elim_inl, Sum.elim_inr,
        intendedWord_eraseHistory who next]

private theorem observe_eq_of_erased_of_history (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
      eraseHistory who program (ProtocolState.observe who program first) =
        eraseHistory who program (ProtocolState.observe who program second) →
      ProtocolState.history program first who = ProtocolState.history program second who →
      ProtocolState.observe who program first = ProtocolState.observe who program second
  | _, _, .ret _, first, second, cells, memory => by
      apply Prod.ext
      · change ((first.view who).1, []) = ((second.view who).1, []) at cells
        exact congrArg (fun view => view.1) cells
      · exact memory
  | _, _, .sample _ _ _ next, first, second, cells, memory => by
      cases first <;> cases second
      · simp only [eraseHistory, ProtocolState.observe, Sum.elim_inl, Sum.inl.injEq] at cells
        exact congrArg Sum.inl (Prod.ext (congrArg (fun view => view.1) cells) memory)
      · cases cells
      · cases cells
      · exact congrArg Sum.inr (observe_eq_of_erased_of_history who next _ _
          (Sum.inr.inj cells) memory)
  | _, _, .commit _ _ _ _ next, first, second, cells, memory => by
      cases first <;> cases second
      · simp only [eraseHistory, ProtocolState.observe, Sum.elim_inl, Sum.inl.injEq] at cells
        exact congrArg Sum.inl (Prod.ext (congrArg (fun view => view.1) cells) memory)
      · cases cells
      · cases cells
      · exact congrArg Sum.inr (observe_eq_of_erased_of_history who next _ _
          (Sum.inr.inj cells) memory)
  | _, _, .reveal _ _ _ _ _ _ next, first, second, cells, memory => by
      cases first <;> cases second
      · simp only [eraseHistory, ProtocolState.observe, Sum.elim_inl, Sum.inl.injEq] at cells
        exact congrArg Sum.inl (Prod.ext (congrArg (fun view => view.1) cells) memory)
      · cases cells
      · cases cells
      · exact congrArg Sum.inr (observe_eq_of_erased_of_history who next _ _
          (Sum.inr.inj cells) memory)

end ProtocolView

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- Equal typed views with remembered lists erased determine the SAME original
honest full information, for two genuine original intended histories. -/
theorem intended_observe_eq_of_erased (who : Player)
    (first second : setup.intendedProtocol.History)
    (same : (setup.protocolObserve who first.state).map
        (ProtocolView.eraseHistory who setup.program) =
      (setup.protocolObserve who second.state).map (ProtocolView.eraseHistory who setup.program)) :
    setup.protocolObserve who first.state = setup.protocolObserve who second.state := by
  cases left : first.state with
  | none =>
      cases right : second.state with
      | none => rfl
      | some point => simp [left, right, protocolObserve] at same
  | some mine =>
      cases right : second.state with
      | none => simp [left, right, protocolObserve] at same
      | some others =>
          simp only [protocolObserve, left, right, Option.map_some] at same
          have cells := Option.some.inj same
          have memories : ProtocolState.history setup.program mine who =
              ProtocolState.history setup.program others who := by
            rw [setup.intended_history_of_typed_view who first.trace mine left,
              setup.intended_history_of_typed_view who second.trace others right]
            exact (ProtocolView.intendedWord_eraseHistory who setup.program _).symm.trans
              ((congrArg (ProtocolView.intendedWord who setup.program) cells).trans
                (ProtocolView.intendedWord_eraseHistory who setup.program _))
          exact congrArg some (ProtocolView.observe_eq_of_erased_of_history who
            setup.program mine others cells memories)

private theorem normalized_current (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    (setup.commitRecoveryNoMissInformation who information).1.1.1 = information.1.1.1 := by
  unfold commitRecoveryNoMissInformation
  split
  · exact (setup.commitRecoveryWithAttemptExclusions_controls who _ _ information).1
  · rfl

/-- Actual normalized pool-key equality of two intended-image queries forces
equality of their original honest information states. Arbitrary copied honest
laws therefore give one well-defined prescription on each such pool. -/
theorem commitRecovery_honest_information_eq_of_query_eq
    (wellFormed : setup.WellFormed) (who : Player)
    (first second : setup.intendedProtocol.History)
    (same : setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who
          (setup.commitRecoveryInformation wellFormed who
            (setup.intendedModel.infoOf who first.trace))) =
      setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who
          (setup.commitRecoveryInformation wellFormed who
            (setup.intendedModel.infoOf who second.trace)))) :
    setup.intendedModel.infoOf who first.trace = setup.intendedModel.infoOf who second.trace := by
  have current := congrArg (fun info : setup.commitRecoveryModel.InfoState who => info.1.1.1) same
  change ((setup.commitRecoveryNoMissInformation who
      (setup.commitRecoveryInformation wellFormed who
        (setup.intendedModel.infoOf who first.trace))).1.1.1.map
          (ProtocolView.eraseHistory who setup.program)) =
    ((setup.commitRecoveryNoMissInformation who
      (setup.commitRecoveryInformation wellFormed who
        (setup.intendedModel.infoOf who second.trace))).1.1.1.map
          (ProtocolView.eraseHistory who setup.program)) at current
  rw [setup.normalized_current, setup.normalized_current] at current
  change ((setup.commitRecoveryRetainedInfo wellFormed who
      (setup.intendedModel.infoOf who first.trace)).1.1.map _) =
    ((setup.commitRecoveryRetainedInfo wellFormed who
      (setup.intendedModel.infoOf who second.trace)).1.1.map _) at current
  rw [setup.commitRecoveryRetainedInfo_current, setup.commitRecoveryRetainedInfo_current] at current
  have firstObserved : setup.intendedModel.infoOf who first.trace =
      setup.protocolObserve who first.state := by
    exact (InformationModel.restrictMenu_infoOf _ _ _ who first.trace).trans
      (setup.protocol_info (CommitmentInterface.values setup.program) who
        (restrictAvailable.trace first.trace))
  have secondObserved : setup.intendedModel.infoOf who second.trace =
      setup.protocolObserve who second.state := by
    exact (InformationModel.restrictMenu_infoOf _ _ _ who second.trace).trans
      (setup.protocol_info (CommitmentInterface.values setup.program) who
        (restrictAvailable.trace second.trace))
  rw [firstObserved, secondObserved] at current ⊢
  exact setup.intended_observe_eq_of_erased who first second current

end Setup
end Vegas.SourceProgram
