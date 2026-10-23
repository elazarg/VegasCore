/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryContinuingMenu
import Vegas.Source.ProtocolSuffix
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Domain-valued source recovery moves with separate failure trembles

An accepted failed binding and a missing binding are different legal source
actions. Ordinary source value components use actual payloads and true
openings. Their full-support perturbations retain both failure atoms with
separate probabilities; neither atom is silently removed by conditioning.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- Ordinary source moves use domain values and open, with no omission.
Unlike `CommitRecoveryContinuingChoice`, this excludes accepted failed
bindings from the value component. -/
def CommitRecoveryValueChoice (who : Player) (info : setup.commitRecoveryModel.InfoState who) :=
  {choice : setup.commitRecoveryModel.Choice who info //
    ∀ move, choice.1 = some move → move.missing = false ∧ ¬ move.action.IsFailure}

theorem commitRecoveryValueChoice_nonempty (who : Player)
    (info : setup.commitRecoveryModel.InfoState who) :
    Nonempty (setup.CommitRecoveryValueChoice who info) := by
  classical
  by_cases active : setup.commitRecoveryActive who info.1.1
  · cases current : info.1.1.1 with
    | none => simp only [commitRecoveryActive, current, Option.elim_none] at active
    | some view =>
        have acting := active
        simp only [commitRecoveryActive, current, Option.elim_some] at acting
        obtain ⟨choice, legal, moves⟩ := ProtocolView.exists_move_menu who setup.program
          (CommitmentInterface.forfeiture setup.program) view
        cases choice with
        | none => exact (legal acting.1).elim
        | some action =>
            have offered : some (⟨action, false⟩ : CommitRecoveryMove Player L) ∈
                setup.commitRecoveryModel.menu who info := by
              refine ⟨active, ?_⟩
              simp only [current, Option.elim_some]
              exact ⟨legal.2, by simp only [Bool.false_eq_true, false_implies, ite_self]⟩
            refine ⟨⟨⟨some ⟨action, false⟩, offered⟩, ?_⟩⟩
            intro move selected
            cases Option.some.inj selected
            exact ⟨rfl, moves action rfl⟩
  · refine ⟨⟨⟨none, active⟩, ?_⟩⟩
    intro move impossible
    cases impossible

theorem commitRecoveryValueChoice_finite (finite : setup.program.FiniteBindingTypes)
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    Finite (setup.CommitRecoveryValueChoice who info) := by
  let := setup.commitRecovery_finite_choice finite who info
  exact Finite.of_injective Subtype.val Subtype.val_injective

end Setup

namespace CommitRecoveryMove

/-- A binding has one atom for each payload and two distinct failed atoms:
accepted failure (`false`) and omission (`true`). -/
def bindingAtom (owner : Player) (name : VarId) (payload : L.Ty) :
    L.Val payload ⊕ Bool → CommitRecoveryMove Player L
  | .inl value => ⟨.commit owner name payload (.success value), false⟩
  | .inr omitted => ⟨.commit owner name payload .failure, omitted⟩

/-- Every binding atom belongs to the actual full recovery source menu. -/
theorem bindingAtom_available {Γ : SourceCtx Player L} {O : Finset VarId}
    (owner : Player) (name : VarId) (payload : L.Ty) (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (view : DecisionView owner Γ) (atom : L.Val payload ⊕ Bool) :
    bindingAtom owner name payload atom ∈ ProtocolView.recoveryAvailable owner
      (.commit name owner fresh guard next) (.inl view) := by
  cases atom with
  | inl value =>
      refine ⟨⟨.success value, trivial, rfl⟩, ?_⟩
      intro impossible
      cases impossible
  | inr omitted => exact ⟨⟨.failure, rfl, rfl⟩, fun _ => rfl⟩

/-- The three binding classes exhaust the actual recovery menu. This keeps
accepted failure separate from both ordinary values and omissions. -/
theorem exists_bindingAtom_of_available {Γ : SourceCtx Player L} {O : Finset VarId}
    (owner : Player) (name : VarId) (payload : L.Ty) (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (view : DecisionView owner Γ) (move : CommitRecoveryMove Player L)
    (offered : move ∈ ProtocolView.recoveryAvailable owner
      (.commit name owner fresh guard next) (.inl view)) :
    ∃ atom, bindingAtom owner name payload atom = move := by
  obtain ⟨⟨result, _admitted, action⟩, missing⟩ := offered
  cases result with
  | failure =>
      refine ⟨.inr move.missing, ?_⟩
      exact congrArg (fun action => (⟨action, move.missing⟩ : CommitRecoveryMove Player L))
        action.symm
  | success value =>
      have noMiss : move.missing = false := by
        cases flag : move.missing with
        | false => rfl
        | true =>
            have failed := missing flag
            rw [action] at failed
            cases failed
      refine ⟨.inl value, ?_⟩
      exact congrArg₂ CommitRecoveryMove.mk action.symm noMiss.symm

end CommitRecoveryMove

namespace ProtocolSuffix

/-- A genuine syntactic suffix preserves the actual full recovery menu. -/
theorem recoveryAvailable {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (who : Player) :
    ∀ point, ProtocolView.recoveryAvailable who whole
        (ProtocolState.observe who whole (lift point)) =
      ProtocolView.recoveryAvailable who program (ProtocolState.observe who program point) := by
  induction origin with
  | initial => intro point; rfl
  | sampleTail _ _ _ _ ih => intro point; exact ih (.inr point)
  | commitTail _ _ _ _ ih => intro point; exact ih (.inr point)
  | revealTail _ _ _ _ _ ih => intro point; exact ih (.inr point)

/-- The actor of a genuine syntactic suffix is the original source actor. -/
theorem actor_lift {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) :
    ∀ point, ProtocolState.actor whole (lift point) = ProtocolState.actor program point := by
  induction origin with
  | initial => intro point; rfl
  | sampleTail _ _ _ _ ih => intro point; exact ih (.inr point)
  | commitTail _ _ _ _ ih => intro point; exact ih (.inr point)
  | revealTail _ _ _ _ _ ih => intro point; exact ih (.inr point)

end ProtocolSuffix
end Vegas.SourceProgram
