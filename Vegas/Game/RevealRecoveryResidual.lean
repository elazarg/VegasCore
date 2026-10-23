/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ServiceRevealTail
import Vegas.Source.ProtocolSuffix

/-! # Recovery control and readout through the existing disclosure residual -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Removing leading disclosures preserves the exact typed terminal context. -/
theorem revealTail_terminalCtx : ∀ (count : Nat) {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (prefixed : RevealPrefix program count),
    (revealTail count program prefixed).tail.terminalCtx = program.terminalCtx := by
  intro count
  induction count with
  | zero => intro Γ O program prefixed; rfl
  | succ count ih =>
      intro Γ O program prefixed
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ next => exact ih next prefixed

/-- The existing disclosure residual is an actual syntactic suffix,
retaining its exact source-point lift. -/
theorem revealTail_protocolSuffix : ∀ (count : Nat) {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (prefixed : RevealPrefix program count),
    ProtocolSuffix program (revealTail count program prefixed).tail
      (revealTail count program prefixed).lift := by
  intro count
  induction count with
  | zero => intro Γ O program prefixed; exact .initial
  | succ count ih =>
      intro Γ O program prefixed
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal published owner name fresh selected unresolved next =>
          exact (ProtocolSuffix.revealTail fresh selected unresolved next
            ProtocolSuffix.initial).compose (ih next prefixed)

/-- The actual disclosure residual commutes with recovery control, retained
typed action history, available menus, raw steps and complete terminal readout.
No new execution carrier or assumed source correspondence is needed. -/
theorem revealTail_recovery : ∀ (count : Nat) {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (prefixed : RevealPrefix program count),
    let residual := revealTail count program prefixed
    (∀ point, ProtocolState.remaining program (residual.lift point) =
      ProtocolState.remaining residual.tail point) ∧
    (∀ point, ProtocolState.actor program (residual.lift point) =
      ProtocolState.actor residual.tail point) ∧
    (∀ point, ProtocolState.atCommit program (residual.lift point) =
      ProtocolState.atCommit residual.tail point) ∧
    (∀ point, ProtocolState.commitOwners program (residual.lift point) =
      ProtocolState.commitOwners residual.tail point) ∧
    (∀ point, ProtocolState.commitEnd program (residual.lift point) =
      ProtocolState.commitEnd residual.tail point) ∧
    (∀ point, residual.lift (ProtocolState.automaticCommitBlock residual.tail point) =
      ProtocolState.automaticCommitBlock program (residual.lift point)) ∧
    (∀ point, ProtocolState.history program (residual.lift point) =
      ProtocolState.history residual.tail point) ∧
    (∀ point past, residual.lift (ProtocolState.withHistory residual.tail point past) =
      ProtocolState.withHistory program (residual.lift point) past) ∧
    (∀ point excluded joint,
      ProtocolState.recoveryStep program (residual.lift point) excluded joint =
        (ProtocolState.recoveryStep residual.tail point excluded joint).map
          (fun result => (residual.lift result.1, result.2))) ∧
    (∀ who point, ProtocolView.recoveryAvailable who program
      (ProtocolState.observe who program (residual.lift point)) =
      ProtocolView.recoveryAvailable who residual.tail
        (ProtocolState.observe who residual.tail point)) ∧
    (∀ point, ProtocolState.readout program (residual.lift point) =
      (ProtocolState.readout residual.tail point).map
        (cast (congrArg (State L) (revealTail_terminalCtx count program prefixed)))) := by
  intro count
  induction count with
  | zero =>
      intro Γ O program prefixed
      refine ⟨(fun _ => rfl), (fun _ => rfl), (fun _ => rfl), (fun _ => rfl),
        (fun _ => rfl), (fun _ => rfl), (fun _ => rfl), (fun _ _ => rfl), ?_,
        (fun _ _ => rfl), ?_⟩
      · intro point excluded joint
        exact (PMF.map_id _).symm
      · intro point
        change _ = Option.map id _
        simp only [Option.map_id, id_eq]
        rfl
  | succ count ih =>
      intro Γ O program prefixed
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal published owner name fresh selected unresolved next =>
          obtain ⟨remaining, actor, commit, owners, endpoint, automatic, history,
            memory, step, menus, readout⟩ := ih next prefixed
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro point
            exact remaining point
          · intro point
            exact actor point
          · intro point
            exact commit point
          · intro point
            exact owners point
          · intro point
            exact endpoint point
          · intro point
            exact congrArg Sum.inr (automatic point)
          · intro point
            exact history point
          · intro point past
            exact congrArg Sum.inr (memory point past)
          · intro point excluded joint
            change ((ProtocolState.recoveryStep next
              ((revealTail count next prefixed).lift point) excluded joint).map
                (fun result => (Sum.inr result.1, result.2))) = _
            rw [step]
            simp only [PMF.map_comp, Function.comp_def]
            rfl
          · intro who point
            exact menus who point
          · intro point
            exact readout point

end Vegas
