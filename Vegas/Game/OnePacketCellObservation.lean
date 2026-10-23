/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CellSwapDebt
import Vegas.Game.OnePacketForced

/-! # Debts read only the observed cells

A player's view of a program point holds its observation of the cells and its
own action history. Debts read only the former: two points at the same
position whose current cells a player observes alike
(`Vegas.SourceProgram.ProtocolState.ObservedAlike`) agree on whether that player
owes a failure (`Vegas.SourceProgram.ProtocolState.owesFailure_iff_of_observedAlike`)
or is excluded (`Vegas.SourceProgram.ProtocolState.excluded_iff_of_observedAlike`),
once both carry the registry and publication status of their program point, and
on every player's failed reveals, which are publications
(`Vegas.SourceProgram.ProtocolState.revealFailed_iff_of_observedAlike`).

In a program with distinct names, points at the same position finding the same
values in every cell a player sees are observed alike
(`Vegas.SourceProgram.ProtocolState.observedAlike_of_cell?`).
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [IExpr.ResultTypes L] in
/-- **Cells found alike are observed alike.** In a context with distinct names,
two states finding the same values in every cell a player sees give that player
the same observation. -/
theorem State.sourceObserve_eq_of_cell? [DecidableEq (CellTy Player L)] {who : Player}
    {Γ : SourceCtx Player L} (distinct : (Γ.map Prod.fst).Nodup) {left right : State L Γ}
    (agree : ∀ name kind, (cellField kind).VisibleTo who →
      State.cell? left name kind = State.cell? right name kind) :
    sourceObserve who left = sourceObserve who right := by
  have get : ∀ {name kind} (cell : HasVar Γ name kind), (cellField kind).VisibleTo who →
      left name kind cell = right name kind cell := fun cell visible => Option.some.inj
    ((State.cell?_eq_of_hasVar cell distinct left).symm.trans
      ((agree _ _ visible).trans (State.cell?_eq_of_hasVar cell distinct right)))
  apply congrArg SourceObservation.mk
  funext name kind cell
  cases kind with
  | publicData => exact get cell trivial
  | publication => exact get cell trivial
  | commitment owner payload =>
      change (if owner = who then some _ else none) = (if owner = who then some _ else none)
      split_ifs with mine
      · exact congrArg some (get cell mine)
      · rfl
  | privateInput owner payload =>
      change (if owner = who then some _ else none) = (if owner = who then some _ else none)
      split_ifs with mine
      · exact congrArg some (get cell mine)
      · rfl

namespace ProtocolState

/-- **Points a player observes alike in their cells**: at the same position,
with current configurations whose cells the player observes alike. -/
def ObservedAlike (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → ProtocolState program →
      Prop
  | _, _, .ret _ => fun left right => sourceObserve who left.state = sourceObserve who right.state
  | _, _, .sample _ _ _ next => fun left right =>
      match left, right with
      | .inl first, .inl second => sourceObserve who first.state = sourceObserve who second.state
      | .inr first, .inr second => ObservedAlike who next first second
      | _, _ => False
  | _, _, .commit _ _ _ _ next => fun left right =>
      match left, right with
      | .inl first, .inl second => sourceObserve who first.state = sourceObserve who second.state
      | .inr first, .inr second => ObservedAlike who next first second
      | _, _ => False
  | _, _, .reveal _ _ _ _ _ _ next => fun left right =>
      match left, right with
      | .inl first, .inl second => sourceObserve who first.state = sourceObserve who second.state
      | .inr first, .inr second => ObservedAlike who next first second
      | _, _ => False

/-- Points observed alike in their cells give the same observation of the cells
of the program point's entry context. -/
theorem sourceObserve_base_eq_of_observedAlike (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (left right : ProtocolState program) →
    ObservedAlike who program left right →
      sourceObserve who (base program left) = sourceObserve who (base program right)
  | _, _, .ret _, _, _, same => same
  | _, _, .sample _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact same
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second =>
              exact sourceObserve_tail_eq
                (sourceObserve_base_eq_of_observedAlike who next first second same)
  | _, _, .commit _ _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact same
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second =>
              exact sourceObserve_tail_eq
                (sourceObserve_base_eq_of_observedAlike who next first second same)
  | _, _, .reveal _ _ _ _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact same
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second =>
              exact sourceObserve_tail_eq
                (sourceObserve_base_eq_of_observedAlike who next first second same)

omit [IExpr.ResultTypes L] in
private theorem config_indebted_iff_of_sourceObserve {who : Player} {Γ : SourceCtx Player L}
    {unresolved : Finset VarId} {registry : Registry Γ} {revelations : Revelations Γ}
    {left right : Config Player L Γ}
    (leftStatic : left.registry = registry ∧ @left.revelations = @revelations)
    (rightStatic : right.registry = registry ∧ @right.revelations = @revelations)
    (same : sourceObserve who left.state = sourceObserve who right.state) :
    left.Indebted who unresolved ↔ right.Indebted who unresolved :=
  ⟨Config.Indebted.of_sourceObserve_eq (leftStatic.1.trans rightStatic.1.symm)
      (leftStatic.2.trans rightStatic.2.symm) same,
    Config.Indebted.of_sourceObserve_eq (rightStatic.1.trans leftStatic.1.symm)
      (rightStatic.2.trans leftStatic.2.symm) same.symm⟩

/-- **A debt to a guard reads only observed cells.** -/
theorem indebted_iff_of_observedAlike (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (registry : Registry Γ) →
    (revelations : Revelations Γ) → (left right : ProtocolState program) →
    StaticAt program registry revelations left → StaticAt program registry revelations right →
    ObservedAlike who program left right →
      (Indebted who program left ↔ Indebted who program right)
  | _, _, .ret _, _, _, _, _, leftStatic, rightStatic, same =>
      config_indebted_iff_of_sourceObserve leftStatic rightStatic same
  | _, _, .sample _ _ _ next, _, _, left, right, leftStatic, rightStatic, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_indebted_iff_of_sourceObserve leftStatic rightStatic same
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second =>
              exact indebted_iff_of_observedAlike who next _ _ first second leftStatic
                rightStatic same
  | _, _, .commit _ _ _ _ next, _, _, left, right, leftStatic, rightStatic, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_indebted_iff_of_sourceObserve leftStatic rightStatic same
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second =>
              exact indebted_iff_of_observedAlike who next _ _ first second leftStatic
                rightStatic same
  | _, _, .reveal _ _ _ _ _ _ next, _, _, left, right, leftStatic, rightStatic, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_indebted_iff_of_sourceObserve leftStatic rightStatic same
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second =>
              have published := sourceObserve_publication_eq
                (sourceObserve_base_eq_of_observedAlike who next first second same) .here
              change (_ ∧ _ = _) ∨ _ ↔ (_ ∧ _ = _) ∨ _
              rw [published, indebted_iff_of_observedAlike who next _ _ first second leftStatic
                rightStatic same]

/-- **A failed binding reads only observed cells.** -/
theorem failedBinding_iff_of_observedAlike (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (left right : ProtocolState program) →
    ObservedAlike who program left right →
      (FailedBinding who program left ↔ FailedBinding who program right)
  | _, _, .ret _, _, _, same =>
      ⟨Config.FailedBinding.of_sourceObserve_eq same,
        Config.FailedBinding.of_sourceObserve_eq same.symm⟩
  | _, _, .sample _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second =>
              exact ⟨Config.FailedBinding.of_sourceObserve_eq same,
                Config.FailedBinding.of_sourceObserve_eq same.symm⟩
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second => exact failedBinding_iff_of_observedAlike who next first second same
  | _, _, .commit _ _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second =>
              exact ⟨Config.FailedBinding.of_sourceObserve_eq same,
                Config.FailedBinding.of_sourceObserve_eq same.symm⟩
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second => exact failedBinding_iff_of_observedAlike who next first second same
  | _, _, .reveal _ _ _ _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second =>
              exact ⟨Config.FailedBinding.of_sourceObserve_eq same,
                Config.FailedBinding.of_sourceObserve_eq same.symm⟩
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second =>
              have published := sourceObserve_publication_eq
                (sourceObserve_base_eq_of_observedAlike who next first second same) .here
              change (_ ∧ _ = _) ∨ _ ↔ (_ ∧ _ = _) ∨ _
              rw [published, failedBinding_iff_of_observedAlike who next first second same]

/-- **Owing a failure reads only observed cells**, among points carrying the
registry and publication status of their program point. -/
theorem owesFailure_iff_of_observedAlike (who : Player) {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) (registry : Registry Γ)
    (revelations : Revelations Γ) (left right : ProtocolState program)
    (leftStatic : StaticAt program registry revelations left)
    (rightStatic : StaticAt program registry revelations right)
    (same : ObservedAlike who program left right) :
    OwesFailure who program left ↔ OwesFailure who program right :=
  or_congr (indebted_iff_of_observedAlike who program registry revelations left right leftStatic
    rightStatic same) (failedBinding_iff_of_observedAlike who program left right same)

/-- **Exclusion reads only observed cells.** -/
theorem excluded_iff_of_observedAlike (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (left right : ProtocolState program) →
    ObservedAlike who program left right →
      (Excluded who program left ↔ Excluded who program right)
  | _, _, .ret _, _, _, same => failedCommitment_iff_of_sourceObserve_eq same
  | _, _, .sample _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact failedCommitment_iff_of_sourceObserve_eq same
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second => exact excluded_iff_of_observedAlike who next first second same
  | _, _, .commit _ _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact failedCommitment_iff_of_sourceObserve_eq same
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second => exact excluded_iff_of_observedAlike who next first second same
  | _, _, .reveal _ _ _ _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact failedCommitment_iff_of_sourceObserve_eq same
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second =>
              have published := sourceObserve_publication_eq
                (sourceObserve_base_eq_of_observedAlike who next first second same) .here
              change (_ ∧ _ = _) ∨ _ ↔ (_ ∧ _ = _) ∨ _
              rw [published, excluded_iff_of_observedAlike who next first second same]

/-- **Failed reveals read only observed cells**: they are publications, so any
player `observer` observing two points alike in their cells sees them alike. -/
theorem revealFailed_iff_of_observedAlike (who observer : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (left right : ProtocolState program) →
    ObservedAlike observer program left right →
      (RevealFailed who program left ↔ RevealFailed who program right)
  | _, _, .ret _, _, _, _ => Iff.rfl
  | _, _, .sample _ _ _ next, left, right, same => by
      cases left with
      | inl _ =>
          cases right with
          | inl _ => exact Iff.rfl
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second =>
              exact revealFailed_iff_of_observedAlike who observer next first second same
  | _, _, .commit _ _ _ _ next, left, right, same => by
      cases left with
      | inl _ =>
          cases right with
          | inl _ => exact Iff.rfl
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second =>
              exact revealFailed_iff_of_observedAlike who observer next first second same
  | _, _, .reveal _ _ _ _ _ _ next, left, right, same => by
      cases left with
      | inl _ =>
          cases right with
          | inl _ => exact Iff.rfl
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second =>
              have published := sourceObserve_publication_eq
                (sourceObserve_base_eq_of_observedAlike observer next first second same) .here
              change (_ ∧ _ = _) ∨ _ ↔ (_ ∧ _ = _) ∨ _
              rw [published, revealFailed_iff_of_observedAlike who observer next first second
                same]

/-- **Cells found alike are observed alike.** In a program with distinct names,
two points at the same position finding the same values in every cell a player
sees are observed alike by that player. -/
theorem observedAlike_of_cell? [DecidableEq (CellTy Player L)] (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (Γ.map Prod.fst).Nodup →
    (left right : ProtocolState program) → SameShape program left right →
    (∀ name kind, (cellField kind).VisibleTo who →
      cell? program left name kind = cell? program right name kind) →
      ObservedAlike who program left right
  | _, _, .ret _, distinct, _, _, _, agree => State.sourceObserve_eq_of_cell? distinct agree
  | _, _, .sample _ fresh _ next, distinct, left, right, shape, agree => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact State.sourceObserve_eq_of_cell? distinct agree
          | inr _ => exact shape.elim
      | inr first =>
          cases right with
          | inl _ => exact shape.elim
          | inr second =>
              exact observedAlike_of_cell? who next (List.nodup_cons.mpr ⟨fresh, distinct⟩)
                first second shape agree
  | _, _, .commit _ _ fresh _ next, distinct, left, right, shape, agree => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact State.sourceObserve_eq_of_cell? distinct agree
          | inr _ => exact shape.elim
      | inr first =>
          cases right with
          | inl _ => exact shape.elim
          | inr second =>
              exact observedAlike_of_cell? who next (List.nodup_cons.mpr ⟨fresh, distinct⟩)
                first second shape agree
  | _, _, .reveal _ _ _ fresh _ _ next, distinct, left, right, shape, agree => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact State.sourceObserve_eq_of_cell? distinct agree
          | inr _ => exact shape.elim
      | inr first =>
          cases right with
          | inl _ => exact shape.elim
          | inr second =>
              exact observedAlike_of_cell? who next (List.nodup_cons.mpr ⟨fresh, distinct⟩)
                first second shape agree

end ProtocolState

end Vegas.SourceProgram
