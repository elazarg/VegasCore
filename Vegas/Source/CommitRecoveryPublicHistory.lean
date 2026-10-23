/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryPublicRanks

/-! # Retrospective public source signals without retired private words -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Dropping a source cell commutes with discarding all private fields and words. -/
theorem DecisionView.back_publicOnly {who : Player} {Γ : SourceCtx Player L}
    {name : VarId} {cell : CellTy Player L} (owned : Bool)
    (view : DecisionView who ((name, cell) :: Γ)) :
    DecisionView.back owned ((view.1.publicOnly, []) : DecisionView who ((name, cell) :: Γ)) =
      ((view.back owned).1.publicOnly, []) := by
  apply Prod.ext
  · apply congrArg SourceObservation.mk
    funext readName readCell selected
    cases readCell <;> rfl
  · cases owned <;> rfl

namespace ProtocolView

/-- Earlier entry observations can be projected publicly before or after
retrospective reading; no remembered private word is supplied to either side. -/
theorem entryView_publicOnly (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (view : ProtocolView who program),
      entryView who program (publicOnly who program view) =
        ((entryView who program view).1.publicOnly, []) := by
  intro Γ O program
  induction program with
  | ret => intro view; rfl
  | sample name fresh law next ih =>
      intro view
      cases view with
      | inl => rfl
      | inr view =>
          exact (congrArg (DecisionView.back false) (ih view)).trans
            (DecisionView.back_publicOnly false _)
  | commit name owner fresh guard next ih =>
      intro view
      cases view with
      | inl => rfl
      | inr view =>
          exact (congrArg (DecisionView.back (decide (owner = who))) (ih view)).trans
            (DecisionView.back_publicOnly (decide (owner = who)) _)
  | reveal published owner name fresh selected unresolved next ih =>
      intro view
      cases view with
      | inl => rfl
      | inr view =>
          exact (congrArg (DecisionView.back (decide (owner = who))) (ih view)).trans
            (DecisionView.back_publicOnly (decide (owner = who)) _)

/-- Public rank readback does not consult the retired private coordinates. -/
theorem atRank_publicOnly (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (rank : Nat) (view : ProtocolView who program),
      atRank who program rank (publicOnly who program view) =
        (atRank who program rank view).map (publicOnly who program) := by
  intro Γ O program
  induction program with
  | ret => intro rank view; cases rank <;> rfl
  | sample name fresh law next ih =>
      intro rank view
      cases rank with
      | zero =>
          exact congrArg (fun current => some (Sum.inl current)) (entryView_publicOnly who _ view)
      | succ rank =>
          cases view with
          | inl => rfl
          | inr view =>
              simpa only [atRank, publicOnly, Sum.elim_inr, Option.map_map, Function.comp_def]
                using congrArg (Option.map Sum.inr) (ih rank view)
  | commit name owner fresh guard next ih =>
      intro rank view
      cases rank with
      | zero =>
          exact congrArg (fun current => some (Sum.inl current)) (entryView_publicOnly who _ view)
      | succ rank =>
          cases view with
          | inl => rfl
          | inr view =>
              simpa only [atRank, publicOnly, Sum.elim_inr, Option.map_map, Function.comp_def]
                using congrArg (Option.map Sum.inr) (ih rank view)
  | reveal published owner name fresh selected unresolved next ih =>
      intro rank view
      cases rank with
      | zero =>
          exact congrArg (fun current => some (Sum.inl current)) (entryView_publicOnly who _ view)
      | succ rank =>
          cases view with
          | inl => rfl
          | inr view =>
              simpa only [atRank, publicOnly, Sum.elim_inr, Option.map_map, Function.comp_def]
                using congrArg (Option.map Sum.inr) (ih rank view)

end ProtocolView

namespace ProtocolState

/-- Reading the entry's public cells is unchanged by padding the current
commitment interval automatically, including the observer's own slots. -/
theorem entryView_automaticCommitBlock_public (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (point : ProtocolState program),
      (ProtocolView.entryView who program
          (observe who program (automaticCommitBlock program point))).1.publicOnly =
        (ProtocolView.entryView who program (observe who program point)).1.publicOnly := by
  intro Γ O program
  induction program with
  | ret => intro point; rfl
  | sample name fresh law next ih =>
      intro point
      cases point with
      | inl => rfl
      | inr point =>
          apply congrArg SourceObservation.mk
          funext readName cell selected
          have previous := congrArg (fun observation =>
            observation.cells readName cell (.there selected)) (ih point)
          cases cell <;> exact previous
  | commit name owner fresh guard next ih =>
      intro point
      cases point with
      | inl config =>
          have later := ih (entry next (automaticCommit name owner _ config))
          rw [ProtocolView.entryView_observe_entry] at later
          apply congrArg SourceObservation.mk
          funext readName cell selected
          have previous := congrArg (fun observation =>
            observation.cells readName cell (.there selected)) later
          cases cell <;> exact previous
      | inr point =>
          apply congrArg SourceObservation.mk
          funext readName cell selected
          have previous := congrArg (fun observation =>
            observation.cells readName cell (.there selected)) (ih point)
          cases cell <;> exact previous
  | reveal published owner name fresh selected unresolved next ih =>
      intro point
      cases point with
      | inl => rfl
      | inr point =>
          apply congrArg SourceObservation.mk
          funext readName cell member
          have previous := congrArg (fun observation =>
            observation.cells readName cell (.there member)) (ih point)
          cases cell <;> exact previous

/-- Padding an unfinished private-only block does not change any earlier
public source signal. This includes a voided own slot at its original rank. -/
theorem atRank_automaticCommitBlock_public (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (point : ProtocolState program) (rank : Nat),
      rank ≤ ProtocolView.position who program (observe who program point) →
      (ProtocolView.atRank who program rank
          (observe who program (automaticCommitBlock program point))).map
            (ProtocolView.publicOnly who program) =
        (ProtocolView.atRank who program rank (observe who program point)).map
          (ProtocolView.publicOnly who program) := by
  intro Γ O program
  induction program with
  | ret => intro point rank bounded; rfl
  | sample name fresh law next ih =>
      intro point rank bounded
      cases point with
      | inl => rfl
      | inr point =>
          cases rank with
          | zero =>
              exact congrArg (fun observation => some (Sum.inl (observation, [])))
                (entryView_automaticCommitBlock_public who _ _)
          | succ rank =>
              have earlier : rank ≤ ProtocolView.position who next (observe who next point) := by
                simpa only [observe, ProtocolView.position, Sum.elim_inr,
                  Nat.add_le_add_iff_right] using bounded
              simpa only [ProtocolView.atRank, automaticCommitBlock, observe, Sum.elim_inr,
                ProtocolView.publicOnly, Option.map_map, Function.comp_def] using
                congrArg (Option.map Sum.inr) (ih point rank earlier)
  | commit name owner fresh guard next ih =>
      intro point rank bounded
      cases rank with
      | zero =>
          exact congrArg (fun observation => some (Sum.inl (observation, [])))
            (entryView_automaticCommitBlock_public who _ _)
      | succ rank =>
          cases point with
          | inl => simp only [observe, ProtocolView.position, Sum.elim_inl] at bounded; omega
          | inr point =>
              have earlier : rank ≤ ProtocolView.position who next (observe who next point) := by
                simpa only [observe, ProtocolView.position, Sum.elim_inr,
                  Nat.add_le_add_iff_right] using bounded
              simpa only [ProtocolView.atRank, automaticCommitBlock, observe, Sum.elim_inr,
                ProtocolView.publicOnly, Option.map_map, Function.comp_def] using
                congrArg (Option.map Sum.inr) (ih point rank earlier)
  | reveal published owner name fresh selected unresolved next ih =>
      intro point rank bounded
      cases point with
      | inl => rfl
      | inr point =>
          cases rank with
          | zero =>
              exact congrArg (fun observation => some (Sum.inl (observation, [])))
                (entryView_automaticCommitBlock_public who _ _)
          | succ rank =>
              have earlier : rank ≤ ProtocolView.position who next (observe who next point) := by
                simpa only [observe, ProtocolView.position, Sum.elim_inr,
                  Nat.add_le_add_iff_right] using bounded
              simpa only [ProtocolView.atRank, automaticCommitBlock, observe, Sum.elim_inr,
                ProtocolView.publicOnly, Option.map_map, Function.comp_def] using
                congrArg (Option.map Sum.inr) (ih point rank earlier)

end ProtocolState

end Vegas.SourceProgram
