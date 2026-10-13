/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceSwapDecode
import Vegas.Pending.ValueSwapPairs

/-! # The graph swap between two source program points

Every field of the default graph is the field of one source cell: an initial
input is the cell of the setup context at its position, and an event's output
is the cell its source node binds (`Vegas.fieldCell`). Two source program points
define, at each field, the pair of their two values of its cell when both are
present and differ (`Vegas.betweenPairs`). Under the swap of these pairs, every
initial reference and every output reference of the program corresponds to the
swap between the two points (`Vegas.refsCorr_initial_between`,
`Vegas.outputsCorr_between`).
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The name and kind of the cell an event binds. -/
def eventCell : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Fin (eventCount program) →
      VarId × CellTy Player L
  | _, _, .ret _, event => Fin.elim0 event
  | _, _, .sample (payload := payload) name _ _ next, event =>
      Fin.cases (name, .publicData payload) (eventCell next) event
  | _, _, .commit (payload := payload) name owner _ _ next, event =>
      Fin.cases (name, .commitment owner payload) (eventCell next) event
  | _, _, .reveal (payload := payload) published _ _ _ _ _ next, event =>
      Fin.cases (published, .publication payload) (eventCell next) event

theorem outputLayout_eventCell : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (event : Fin (eventCount program)),
    outputLayout program event = cellField (eventCell program event).2
  | _, _, .ret _, event => Fin.elim0 event
  | _, _, .sample _ _ _ next, event => by
      cases event using Fin.cases with
      | zero => rfl
      | succ event => exact outputLayout_eventCell next event
  | _, _, .commit _ _ _ _ next, event => by
      cases event using Fin.cases with
      | zero => rfl
      | succ event => exact outputLayout_eventCell next event
  | _, _, .reveal _ _ _ _ _ _ next, event => by
      cases event using Fin.cases with
      | zero => rfl
      | succ event => exact outputLayout_eventCell next event

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem inputLayout_get : ∀ (Γ : SourceCtx Player L) (input : Fin Γ.length),
    inputLayout Γ input = cellField (Γ.get input).2
  | [], input => Fin.elim0 input
  | (_, kind) :: Γ, input => by
      cases input using Fin.cases with
      | zero => cases kind <;> rfl
      | succ input => exact inputLayout_get Γ input

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem inputId_get {Γ : SourceCtx Player L} {name : VarId} {kind : CellTy Player L}
    (source : HasVar Γ name kind) : Γ.get (inputId source) = (name, kind) := by
  induction source with
  | here => rfl
  | there source ih => exact ih

end Vegas.SourceProgram

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The source cell of a field of the default graph. -/
def fieldCell (setup : Setup (Player := Player) (L := L)) :
    (graph setup).Field → VarId × CellTy Player L
  | .inl input => setup.context.get input
  | .inr event => eventCell setup.program event

theorem layout_fieldCell (setup : Setup (Player := Player) (L := L))
    (field : (graph setup).Field) :
    (graph setup).layout field = cellField (fieldCell setup field).2 := by
  cases field with
  | inl input => exact inputLayout_get setup.context input
  | inr event => exact outputLayout_eventCell setup.program event

/-- Transport a pair of field values along an equality of field kinds. -/
def transportPair {first second : EventGraph.EventField Player L} (same : first = second)
    (pair : Option (first.Value × first.Value)) : Option (second.Value × second.Value) :=
  cast (congrArg (fun kind : EventGraph.EventField Player L =>
    Option (kind.Value × kind.Value)) same) pair

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem pairSwap_transportPair {first second : EventGraph.EventField Player L}
    (same : first = second) (pair : Option (first.Value × first.Value)) (value : first.Value) :
    EventGraph.pairSwap (transportPair same pair)
        (cast (congrArg EventGraph.EventField.Value same) value) =
      cast (congrArg EventGraph.EventField.Value same) (EventGraph.pairSwap pair value) := by
  subst same
  rfl

open Classical in
/-- The pair of two found cell values, when both are found and differ. -/
def cellPair {kind : CellTy Player L} (first second : Option (CellVal L kind)) :
    Option ((cellField kind).Value × (cellField kind).Value) :=
  match first, second with
  | some left, some right => if left = right then none else some (cellValue left, cellValue right)
  | _, _ => none

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem transportPair_none {first second : EventGraph.EventField Player L} (same : first = second) :
    transportPair same (none : Option (first.Value × first.Value)) = none := by
  subst same
  rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem transportPair_some {first second : EventGraph.EventField Player L} (same : first = second)
    (left right : first.Value) :
    transportPair same (some (left, right)) =
      some (cast (congrArg EventGraph.EventField.Value same) left,
        cast (congrArg EventGraph.EventField.Value same) right) := by
  subst same
  rfl

/-- The swap of two found cell values, read on the graph field of their kind. -/
def swapFoundField : {kind : CellTy Player L} → Option (CellVal L kind) →
    Option (CellVal L kind) → (cellField kind).Value → (cellField kind).Value
  | .publicData _, first, second => swapFound first second
  | .privateInput _ _, first, second => swapFound first second
  | .commitment _ _, first, second => swapFound first second
  | .publication _, first, second => swapFound first second

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- The transposition of a found pair is the swap of the found values. -/
theorem pairSwap_cellPair {kind : CellTy Player L} (first second : Option (CellVal L kind))
    (value : (cellField kind).Value) :
    EventGraph.pairSwap (cellPair first second) value = swapFoundField first second value := by
  classical
  cases kind <;>
  · cases first with
    | none => rfl
    | some left =>
        cases second with
        | none => rfl
        | some right =>
            simp only [cellPair, swapFoundField, swapFound]
            split
            · rename_i same
              subst same
              simp [EventGraph.pairSwap]
            · rfl

theorem field_between [DecidableEq (CellTy Player L)] {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (first second : ProtocolState program) (name : VarId) (kind : CellTy Player L) :
    (CellSwap.between program first second).field name kind =
      swapFoundField (ProtocolState.cell? program first name kind)
        (ProtocolState.cell? program second name kind) := by
  cases kind <;> rfl

section Between

variable (setup : Setup (Player := Player) (L := L)) [DecidableEq (CellTy Player L)]
  (first second : ProtocolState setup.program)

/-- The pair of a cell between two source program points, read on a field kind
equal to the cell's. -/
def cellPairAt {kind : EventGraph.EventField Player L} (cell : VarId × CellTy Player L)
    (kindEq : kind = cellField cell.2) : Option (kind.Value × kind.Value) :=
  transportPair kindEq.symm
    (cellPair (ProtocolState.cell? setup.program first cell.1 cell.2)
      (ProtocolState.cell? setup.program second cell.1 cell.2))

/-- The pair at a field of the default graph between two source program points. -/
def betweenPair (field : (graph setup).Field) :
    Option (((graph setup).layout field).Value × ((graph setup).layout field).Value) :=
  cellPairAt setup first second (fieldCell setup field) (layout_fieldCell setup field)

/-- Two program points agree on every public cell found at both. -/
def PublicCellsAgree : Prop :=
  ∀ name kind, (cellField kind).IsPublic → ∀ left right,
    ProtocolState.cell? setup.program first name kind = some left →
    ProtocolState.cell? setup.program second name kind = some right → left = right

/-- Every commitment cell found at both program points with different values is
a success at both. -/
def CommitmentCellsSucceed : Prop :=
  ∀ name owner payload left right,
    ProtocolState.cell? setup.program first name (.commitment owner payload) = some left →
    ProtocolState.cell? setup.program second name (.commitment owner payload) = some right →
    left ≠ right → left ≠ .failure ∧ right ≠ .failure

variable {setup first second}

/-- Read on a reference to a field of a cell, the swap of the between pairs is
the swap between the two points. -/
theorem pairSwap_betweenPair {field : (graph setup).Field} {name : VarId}
    {kind : CellTy Player L} (cell : fieldCell setup field = (name, kind))
    (layoutEq : (graph setup).layout field = cellField kind)
    (value : ((graph setup).layout field).Value) :
    cast (congrArg EventGraph.EventField.Value layoutEq)
        (EventGraph.pairSwap (betweenPair setup first second field) value) =
      (CellSwap.between setup.program first second).field name kind
        (cast (congrArg EventGraph.EventField.Value layoutEq) value) := by
  rw [field_between]
  unfold betweenPair
  have general : ∀ (found : VarId × CellTy Player L)
      (fieldEq : (graph setup).layout field = cellField found.2), found = (name, kind) →
      cast (congrArg EventGraph.EventField.Value layoutEq)
          (EventGraph.pairSwap (cellPairAt setup first second found fieldEq) value) =
        swapFoundField (ProtocolState.cell? setup.program first name kind)
          (ProtocolState.cell? setup.program second name kind)
          (cast (congrArg EventGraph.EventField.Value layoutEq) value) := by
    rintro found fieldEq rfl
    have proofEq : fieldEq = layoutEq := rfl
    subst proofEq
    unfold cellPairAt
    obtain ⟨original, rfl⟩ : ∃ original : (cellField kind).Value,
        value = cast (congrArg EventGraph.EventField.Value fieldEq.symm) original :=
      ⟨cast (congrArg EventGraph.EventField.Value fieldEq) value, by simp⟩
    rw [pairSwap_transportPair, cast_cast, cast_cast, cast_eq, cast_eq, pairSwap_cellPair]
  exact general _ _ cell

/-- **The pairs between two points.** -/
def betweenPairs (publicAgree : PublicCellsAgree setup first second)
    (succeed : CommitmentCellsSucceed setup first second) : (graph setup).SwapPairs where
  pair := betweenPair setup first second
  public_none field isPublic := by
    unfold betweenPair
    generalize layout_fieldCell setup field = fieldEq
    generalize fieldCell setup field = found at fieldEq
    rcases found with ⟨name, kind⟩
    unfold cellPairAt
    have kindPublic : (cellField kind).IsPublic := by
      unfold EventGraph.fieldPublic at isPublic
      rw [fieldEq] at isPublic
      exact isPublic
    cases found : ProtocolState.cell? setup.program first name kind with
    | none => exact transportPair_none _
    | some left =>
        cases foundSecond : ProtocolState.cell? setup.program second name kind with
        | none => exact transportPair_none _
        | some right =>
            have same := publicAgree name kind kindPublic left right found foundSecond
            subst same
            simp only [cellPair, ↓reduceIte]
            exact transportPair_none _
  binding_success event owner payload outputEq left right paired := by
    unfold betweenPair at paired
    generalize layout_fieldCell setup (.inr event) = fieldEq at paired
    generalize fieldCell setup (.inr event) = found at fieldEq paired
    rcases found with ⟨name, kind⟩
    have kindEq : cellField kind = .binding owner payload := fieldEq.symm.trans outputEq
    cases kind with
    | publicData | privateInput | publication => cases kindEq
    | commitment cellOwner cellPayload =>
        obtain ⟨ownerEq, payloadEq⟩ := EventGraph.EventField.binding.inj kindEq
        subst ownerEq payloadEq
        have proofEq : fieldEq = outputEq := rfl
        subst proofEq
        unfold cellPairAt at paired
        cases foundFirst : ProtocolState.cell? setup.program first name
            (.commitment cellOwner cellPayload) with
        | none =>
            rw [foundFirst] at paired
            simp only [cellPair, transportPair_none, reduceCtorEq] at paired
        | some firstValue =>
            cases foundSecond : ProtocolState.cell? setup.program second name
                (.commitment cellOwner cellPayload) with
            | none =>
                rw [foundFirst, foundSecond] at paired
                simp only [cellPair, transportPair_none, reduceCtorEq] at paired
            | some secondValue =>
                rw [foundFirst, foundSecond] at paired
                by_cases same : firstValue = secondValue
                · simp only [cellPair, same, ↓reduceIte, transportPair_none,
                    reduceCtorEq] at paired
                · simp only [cellPair, same, ↓reduceIte] at paired
                  obtain ⟨firstOk, secondOk⟩ := succeed name cellOwner cellPayload firstValue
                    secondValue foundFirst foundSecond same
                  rw [transportPair_some] at paired
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj paired).symm
                  exact ⟨fun equal => firstOk ((cast_inj _).mp equal),
                    fun equal => secondOk ((cast_inj _).mp equal)⟩

end Between

end Vegas
