/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.DebtObservation

/-! # Owing a failure after a cell swap

Two points of a program at the same position whose current configurations
hold the same cells (`Vegas.SourceProgram.ProtocolState.SameCells`) agree on
every player's debts, once both carry the registry and publication status of
their program point
(`Vegas.SourceProgram.ProtocolState.owesFailure_iff_of_sameCells`): a debt reads
only cells, obligations and publication status.

A cell swap sending every value found at one point to the value found at
another point at the same position makes the swapped first point hold the
cells of the second (`Vegas.SourceProgram.ProtocolState.sameCells_swap`); the
swap between the two points does
(`Vegas.SourceProgram.ProtocolState.sameCells_between`). A swap keeps
obligations and publication status
(`Vegas.SourceProgram.ProtocolState.staticAt_swap`).
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **Points with the same cells**: at the same position, with current
configurations holding the same cells. -/
def SameCells : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → ProtocolState program →
      Prop
  | _, _, .ret _ => fun left right => left.state = right.state
  | _, _, .sample _ _ _ next => fun left right =>
      match left, right with
      | .inl first, .inl second => first.state = second.state
      | .inr first, .inr second => SameCells next first second
      | _, _ => False
  | _, _, .commit _ _ _ _ next => fun left right =>
      match left, right with
      | .inl first, .inl second => first.state = second.state
      | .inr first, .inr second => SameCells next first second
      | _, _ => False
  | _, _, .reveal _ _ _ _ _ _ next => fun left right =>
      match left, right with
      | .inl first, .inl second => first.state = second.state
      | .inr first, .inr second => SameCells next first second
      | _, _ => False

/-- Points with the same cells have the same cells at the entry context. -/
theorem base_eq_of_sameCells : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (left right : ProtocolState program) →
    SameCells program left right → base program left = base program right
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
              have inner := base_eq_of_sameCells next first second same
              change (fun _ _ cell => (base next first).get (.there cell) : State L _) =
                fun _ _ cell => (base next second).get (.there cell)
              rw [inner]
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
              have inner := base_eq_of_sameCells next first second same
              change (fun _ _ cell => (base next first).get (.there cell) : State L _) =
                fun _ _ cell => (base next second).get (.there cell)
              rw [inner]
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
              have inner := base_eq_of_sameCells next first second same
              change (fun _ _ cell => (base next first).get (.there cell) : State L _) =
                fun _ _ cell => (base next second).get (.there cell)
              rw [inner]

omit [IExpr.ResultTypes L] in
private theorem config_indebted_iff_of_state {who : Player} {Γ : SourceCtx Player L}
    {unresolved : Finset VarId} {registry : Registry Γ} {revelations : Revelations Γ}
    {left right : Config Player L Γ}
    (leftStatic : left.registry = registry ∧ @left.revelations = @revelations)
    (rightStatic : right.registry = registry ∧ @right.revelations = @revelations)
    (same : left.state = right.state) :
    left.Indebted who unresolved ↔ right.Indebted who unresolved :=
  have observed := congrArg (sourceObserve who) same
  ⟨Config.Indebted.of_sourceObserve_eq (leftStatic.1.trans rightStatic.1.symm)
      (leftStatic.2.trans rightStatic.2.symm) observed,
    Config.Indebted.of_sourceObserve_eq (rightStatic.1.trans leftStatic.1.symm)
      (rightStatic.2.trans leftStatic.2.symm) observed.symm⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem config_failedBinding_iff_of_state {who : Player} {Γ : SourceCtx Player L}
    {unresolved : Finset VarId} {left right : Config Player L Γ}
    (same : left.state = right.state) :
    left.FailedBinding who unresolved ↔ right.FailedBinding who unresolved := by
  constructor <;> intro failed <;> refine ⟨failed.unique, ?_⟩
  · rw [← same]
    exact failed.pending
  · rw [same]
    exact failed.pending

/-- A debt to a guard is a function of the cells, among points carrying the
registry and publication status of their program point. -/
theorem indebted_iff_of_sameCells (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (registry : Registry Γ) →
    (revelations : Revelations Γ) → (left right : ProtocolState program) →
    StaticAt program registry revelations left → StaticAt program registry revelations right →
    SameCells program left right → (Indebted who program left ↔ Indebted who program right)
  | _, _, .ret _, _, _, _, _, leftStatic, rightStatic, same =>
      config_indebted_iff_of_state leftStatic rightStatic same
  | _, _, .sample _ _ _ next, _, _, left, right, leftStatic, rightStatic, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_indebted_iff_of_state leftStatic rightStatic same
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second =>
              exact indebted_iff_of_sameCells who next _ _ first second leftStatic rightStatic
                same
  | _, _, .commit _ _ _ _ next, _, _, left, right, leftStatic, rightStatic, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_indebted_iff_of_state leftStatic rightStatic same
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second =>
              exact indebted_iff_of_sameCells who next _ _ first second leftStatic rightStatic
                same
  | _, _, .reveal _ _ _ _ _ _ next, _, _, left, right, leftStatic, rightStatic, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_indebted_iff_of_state leftStatic rightStatic same
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second =>
              change (_ ∧ _ = _) ∨ _ ↔ (_ ∧ _ = _) ∨ _
              rw [base_eq_of_sameCells next first second same,
                indebted_iff_of_sameCells who next _ _ first second leftStatic rightStatic same]

/-- A failed binding is a function of the cells. -/
theorem failedBinding_iff_of_sameCells (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (left right : ProtocolState program) →
    SameCells program left right →
      (FailedBinding who program left ↔ FailedBinding who program right)
  | _, _, .ret _, _, _, same => config_failedBinding_iff_of_state same
  | _, _, .sample _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_failedBinding_iff_of_state same
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second => exact failedBinding_iff_of_sameCells who next first second same
  | _, _, .commit _ _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_failedBinding_iff_of_state same
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second => exact failedBinding_iff_of_sameCells who next first second same
  | _, _, .reveal _ _ _ _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_failedBinding_iff_of_state same
          | inr _ => exact same.elim
      | inr first =>
          cases right with
          | inl _ => exact same.elim
          | inr second =>
              change (_ ∧ _ = _) ∨ _ ↔ (_ ∧ _ = _) ∨ _
              rw [base_eq_of_sameCells next first second same,
                failedBinding_iff_of_sameCells who next first second same]

/-- **Owing a failure is a function of the cells**, among points carrying the
registry and publication status of their program point. -/
theorem owesFailure_iff_of_sameCells (who : Player) {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) (registry : Registry Γ)
    (revelations : Revelations Γ) (left right : ProtocolState program)
    (leftStatic : StaticAt program registry revelations left)
    (rightStatic : StaticAt program registry revelations right)
    (same : SameCells program left right) :
    OwesFailure who program left ↔ OwesFailure who program right :=
  or_congr (indebted_iff_of_sameCells who program registry revelations left right leftStatic
    rightStatic same) (failedBinding_iff_of_sameCells who program left right same)

/-- **A swap keeps obligations and publication status.** -/
theorem staticAt_swap (swap : CellSwap Player L) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (registry : Registry Γ) →
    (revelations : Revelations Γ) → (state : ProtocolState program) →
    StaticAt program registry revelations state →
      StaticAt program registry revelations (swap.protocolState program state)
  | _, _, .ret _, _, _, _, static => static
  | _, _, .sample _ _ _ next, _, _, state, static => by
      cases state with
      | inl _ => exact static
      | inr rest => exact staticAt_swap swap next _ _ rest static
  | _, _, .commit _ _ _ _ next, _, _, state, static => by
      cases state with
      | inl _ => exact static
      | inr rest => exact staticAt_swap swap next _ _ rest static
  | _, _, .reveal _ _ _ _ _ _ next, _, _, state, static => by
      cases state with
      | inl _ => exact static
      | inr rest => exact staticAt_swap swap next _ _ rest static

/-- **Points at the same position** of a program. -/
def SameShape : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → ProtocolState program →
      Prop
  | _, _, .ret _ => fun _ _ => True
  | _, _, .sample _ _ _ next => fun left right =>
      match left, right with
      | .inl _, .inl _ => True
      | .inr first, .inr second => SameShape next first second
      | _, _ => False
  | _, _, .commit _ _ _ _ next => fun left right =>
      match left, right with
      | .inl _, .inl _ => True
      | .inr first, .inr second => SameShape next first second
      | _, _ => False
  | _, _, .reveal _ _ _ _ _ _ next => fun left right =>
      match left, right with
      | .inl _, .inl _ => True
      | .inr first, .inr second => SameShape next first second
      | _, _ => False

/-- Points one player observes alike are at the same position. -/
theorem sameShape_of_observe_eq (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (left right : ProtocolState program) →
    observe who program left = observe who program right → SameShape program left right
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, left, right, same => by
      cases left with
      | inl _ =>
          cases right with
          | inl _ => trivial
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second => exact sameShape_of_observe_eq who next first second (Sum.inr.inj same)
  | _, _, .commit _ _ _ _ next, left, right, same => by
      cases left with
      | inl _ =>
          cases right with
          | inl _ => trivial
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second => exact sameShape_of_observe_eq who next first second (Sum.inr.inj same)
  | _, _, .reveal _ _ _ _ _ _ next, left, right, same => by
      cases left with
      | inl _ =>
          cases right with
          | inl _ => trivial
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second => exact sameShape_of_observe_eq who next first second (Sum.inr.inj same)

section Swap

variable [DecidableEq (CellTy Player L)]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem config_state_swap {Γ : SourceCtx Player L} (swap : CellSwap Player L)
    (distinct : (Γ.map Prod.fst).Nodup) (first second : Config Player L Γ)
    (sends : ∀ name kind value other, State.cell? first.state name kind = some value →
      State.cell? second.state name kind = some other → swap.cell name kind value = other) :
    (swap.config first).state = second.state := by
  funext name kind source
  exact sends name kind _ _ (State.cell?_eq_of_hasVar source distinct _)
    (State.cell?_eq_of_hasVar source distinct _)

/-- **A swap sending found values to found values yields the second point's
cells.** For two points at the same position in a program with distinct names, a
swap sending every value found at the first to the value found at the second
under the same name and kind makes the swapped first point hold the cells of
the second. -/
theorem sameCells_swap (swap : CellSwap Player L) : {Γ : SourceCtx Player L} →
    {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (Γ.map Prod.fst).Nodup → (first second : ProtocolState program) →
    (∀ name kind value other, cell? program first name kind = some value →
      cell? program second name kind = some other → swap.cell name kind value = other) →
    SameShape program first second →
      SameCells program (swap.protocolState program first) second
  | _, _, .ret _, distinct, first, second, sends, _ =>
      config_state_swap swap distinct first second sends
  | _, _, .sample _ fresh _ next, distinct, first, second, sends, shape => by
      cases first with
      | inl current =>
          cases second with
          | inl other => exact config_state_swap swap distinct current other sends
          | inr _ => exact shape.elim
      | inr rest =>
          cases second with
          | inl _ => exact shape.elim
          | inr other =>
              exact sameCells_swap swap next (List.nodup_cons.mpr ⟨fresh, distinct⟩) rest other
                sends shape
  | _, _, .commit _ _ fresh _ next, distinct, first, second, sends, shape => by
      cases first with
      | inl current =>
          cases second with
          | inl other => exact config_state_swap swap distinct current other sends
          | inr _ => exact shape.elim
      | inr rest =>
          cases second with
          | inl _ => exact shape.elim
          | inr other =>
              exact sameCells_swap swap next (List.nodup_cons.mpr ⟨fresh, distinct⟩) rest other
                sends shape
  | _, _, .reveal _ _ _ fresh _ _ next, distinct, first, second, sends, shape => by
      cases first with
      | inl current =>
          cases second with
          | inl other => exact config_state_swap swap distinct current other sends
          | inr _ => exact shape.elim
      | inr rest =>
          cases second with
          | inl _ => exact shape.elim
          | inr other =>
              exact sameCells_swap swap next (List.nodup_cons.mpr ⟨fresh, distinct⟩) rest other
                sends shape

/-- **The swap between two points yields the second point's cells** at the
first point, at the same position in a program with distinct names. -/
theorem sameCells_between {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (distinct : (Γ.map Prod.fst).Nodup)
    (first second : ProtocolState program) (shape : SameShape program first second) :
    SameCells program ((CellSwap.between program first second).protocolState program first)
      second :=
  sameCells_swap _ program distinct first second (fun name kind value other found otherFound => by
    simp only [CellSwap.between, found, otherFound, swapFound, Equiv.swap_apply_left]) shape

end Swap

end Vegas.SourceProgram.ProtocolState
