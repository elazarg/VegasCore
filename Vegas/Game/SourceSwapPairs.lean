/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

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

section Correspondence

variable {setup : Setup (Player := Player) (L := L)} [DecidableEq (CellTy Player L)]
  {first second : ProtocolState setup.program}
  {publicAgree : PublicCellsAgree setup first second}
  {succeed : CommitmentCellsSucceed setup first second}

omit [DecidableEq Player] [IExpr.ResultTypes L] [DecidableEq (CellTy Player L)] in
private theorem cast_option_some {first second : EventGraph.EventField Player L}
    (same : first = second)
    (value : first.Value) :
    cast (congrArg (fun kind : EventGraph.EventField Player L => Option kind.Value) same)
        (some value) = some (cast (congrArg EventGraph.EventField.Value same) value) := by
  subst same
  rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] [DecidableEq (CellTy Player L)] in
private theorem cast_option_none {first second : EventGraph.EventField Player L}
    (same : first = second) :
    cast (congrArg (fun kind : EventGraph.EventField Player L => Option kind.Value) same)
        (none : Option first.Value) = none := by
  subst same
  rfl

/-- **A reference to a field of a cell corresponds to the swap between the points.** -/
theorem fieldCorr_betweenPairs {name : VarId} {kind : CellTy Player L}
    (ref : EventGraph.FieldRef (graph setup).layout (cellField kind))
    (cell : fieldCell setup ref.field = (name, kind)) :
    (CellSwap.between setup.program first second).FieldCorr
      (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed)).store
      name kind ref := by
  intro store
  rcases ref with ⟨field, layoutEq⟩
  change fieldCell setup field = (name, kind) at cell
  unfold EventGraph.FieldRef.get?
  change cast _ ((store field).map (EventGraph.pairSwap (betweenPair setup first second field))) =
    Option.map _ (cast _ (store field))
  cases store field with
  | none => rw [Option.map_none, cast_option_none layoutEq, Option.map_none]
  | some value =>
      rw [Option.map_some, cast_option_some layoutEq, cast_option_some layoutEq, Option.map_some,
        pairSwap_betweenPair cell layoutEq value]

/-- Every initial reference corresponds to the swap between the points. -/
theorem refsCorr_initial_between :
    (CellSwap.between setup.program first second).RefsCorr
      (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed)).store
      (ContextRefs.initial setup.context (outputLayout setup.program)) := by
  intro name kind source
  exact fieldCorr_betweenPairs _ (inputId_get source)

/-- Output references whose fields are the cells their events bind correspond to
the swap between the points. -/
theorem outputsCorr_of_cells : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O)
    (outputs : ∀ event, EventGraph.FieldRef (graph setup).layout (outputLayout program event)),
    (∀ event, fieldCell setup (outputs event).field = eventCell program event) →
    (CellSwap.between setup.program first second).OutputsCorr
      (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed)).store
      program outputs
  | _, _, .ret _, _, _ => trivial
  | _, _, .sample _ _ _ next, _, cells =>
      ⟨fieldCorr_betweenPairs _ (cells ⟨0, Nat.succ_pos _⟩),
        outputsCorr_of_cells next _ fun event => cells event.succ⟩
  | _, _, .commit _ _ _ _ next, _, cells =>
      ⟨fieldCorr_betweenPairs _ (cells ⟨0, Nat.succ_pos _⟩),
        outputsCorr_of_cells next _ fun event => cells event.succ⟩
  | _, _, .reveal _ _ _ _ _ _ next, _, cells =>
      ⟨fieldCorr_betweenPairs _ (cells ⟨0, Nat.succ_pos _⟩),
        outputsCorr_of_cells next _ fun event => cells event.succ⟩

/-- The program's output references correspond to the swap between the points. -/
theorem outputsCorr_between :
    (CellSwap.between setup.program first second).OutputsCorr
      (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed)).store
      setup.program (outputRef setup.program) :=
  outputsCorr_of_cells setup.program _ fun _ => rfl

end Correspondence

end Vegas

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A binding event decodes to the commitment of its cell's name. -/
theorem decodeEventAction_binding_cell {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) :
    ∀ (count : Nat) (bound : count < eventCount program) {owner : Player} {payload : L.Ty}
      (outputEq : outputLayout program ⟨count, bound⟩ = .binding owner payload)
      (choice : PublicationResult (L.Val payload)),
      decodeEventAction program ⟨count, bound⟩
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice) =
        some (.commit owner (eventCell program ⟨count, bound⟩).1 payload choice) := by
  induction program with
  | ret _ =>
      intro count bound
      simp [eventCount] at bound
  | sample _ _ _ next ih =>
      intro count bound owner payload outputEq
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq
  | commit name commitOwner fresh guard next ih =>
      intro count bound owner payload outputEq
      cases count with
      | zero =>
          change EventGraph.EventField.binding commitOwner _ = _ at outputEq
          obtain ⟨rfl, rfl⟩ := EventGraph.EventField.binding.inj outputEq
          intro choice
          rfl
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq
  | reveal published revealOwner name fresh source unresolved next ih =>
      intro count bound owner payload outputEq
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq

/-- A non-binding event decodes to no commitment, so every cell swap fixes its
decoded action. -/
theorem decodeEventAction_swap_of_not_binding (swap : CellSwap Player L)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O) :
    ∀ (count : Nat) (bound : count < eventCount program)
      (_ : ∀ owner payload, outputLayout program ⟨count, bound⟩ ≠ .binding owner payload)
      (action : EventGraph.EventField.Action (outputLayout program ⟨count, bound⟩)),
      (decodeEventAction program ⟨count, bound⟩ action).map swap.action =
        decodeEventAction program ⟨count, bound⟩ action := by
  induction program with
  | ret _ =>
      intro count bound
      simp [eventCount] at bound
  | sample _ _ _ next ih =>
      intro count bound notBinding action
      cases count with
      | zero => rfl
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) notBinding action
  | commit name commitOwner fresh guard next ih =>
      intro count bound notBinding action
      cases count with
      | zero => exact (notBinding commitOwner _ rfl).elim
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) notBinding action
  | reveal published revealOwner name fresh source unresolved next ih =>
      intro count bound notBinding action
      cases count with
      | zero => rfl
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) notBinding action

end Vegas.SourceProgram

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] in
theorem EventGraph.SwapPairs.action_of_not_binding {graph : Vegas.EventGraph Player L}
    (pairs : graph.SwapPairs) (event : graph.EventId)
    (notBinding : ∀ owner payload, graph.outputLayout event ≠ .binding owner payload) :
    pairs.action event = id := by
  unfold EventGraph.SwapPairs.action
  cases view : nodeView graph event with
  | bind owner payload outputEq _ => exact (notBinding owner payload outputEq).elim
  | resolve | sample => rfl

variable {setup : Setup (Player := Player) (L := L)} [DecidableEq (CellTy Player L)]
  {first second : ProtocolState setup.program}
  {publicAgree : PublicCellsAgree setup first second}
  {succeed : CommitmentCellsSucceed setup first second}

/-- **A swapped event decodes to the swapped action.** -/
theorem decodeEventAction_betweenPairs (event : (graph setup).EventId)
    (action : (graph setup).Action event) :
    decodeEventAction setup.program event
        ((EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed)).action event action) =
      (decodeEventAction setup.program event action).map
        (CellSwap.between setup.program first second).action := by
  rcases event with ⟨count, bound⟩
  by_cases binding : ∃ owner payload, (graph setup).outputLayout ⟨count, bound⟩ =
      .binding owner payload
  · obtain ⟨owner, payload, outputEq⟩ := binding
    obtain ⟨choice, rfl⟩ : ∃ choice : PublicationResult (L.Val payload),
        action = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :=
      ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
    have cellKind : (eventCell setup.program ⟨count, bound⟩).2 = .commitment owner payload := by
      have layoutEq := (outputLayout_eventCell setup.program ⟨count, bound⟩).symm.trans outputEq
      revert layoutEq
      rcases (eventCell setup.program ⟨count, bound⟩).2 with _ | _ | _ | _
      all_goals intro layoutEq
      all_goals cases layoutEq
      rfl
    have cell : fieldCell setup (.inr ⟨count, bound⟩) =
        ((eventCell setup.program ⟨count, bound⟩).1, .commitment owner payload) := by
      change eventCell setup.program ⟨count, bound⟩ = _
      rw [← cellKind]
    have key : cast (congrArg EventGraph.EventField.Value outputEq)
        (EventGraph.pairSwap (betweenPair setup first second (.inr ⟨count, bound⟩))
          (cast (congrArg EventGraph.EventField.Value outputEq.symm) choice)) =
        (CellSwap.between setup.program first second).cell
          (eventCell setup.program ⟨count, bound⟩).1 (.commitment owner payload) choice := by
      have swapped := pairSwap_betweenPair (first := first) (second := second) cell outputEq
        (cast (congrArg EventGraph.EventField.Value outputEq.symm) choice)
      rw [cast_cast, cast_eq] at swapped
      exact swapped
    change decodeEventAction setup.program ⟨count, bound⟩
        ((betweenPairs publicAgree succeed).action ⟨count, bound⟩
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)) = _
    rw [EventGraph.SwapPairs.action_binding _ _ owner payload outputEq choice]
    change decodeEventAction setup.program ⟨count, bound⟩
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (cast (congrArg EventGraph.EventField.Value outputEq)
            (EventGraph.pairSwap (betweenPair setup first second (.inr ⟨count, bound⟩))
              (cast (congrArg EventGraph.EventField.Value outputEq.symm) choice)))) = _
    rw [key, decodeEventAction_binding_cell setup.program count bound outputEq,
      decodeEventAction_binding_cell setup.program count bound outputEq]
    rfl
  · have notBinding : ∀ owner payload,
        (graph setup).outputLayout ⟨count, bound⟩ ≠ .binding owner payload :=
      fun owner payload same => binding ⟨owner, payload, same⟩
    change decodeEventAction setup.program ⟨count, bound⟩
      ((betweenPairs publicAgree succeed).action ⟨count, bound⟩ action) = _
    rw [EventGraph.SwapPairs.action_of_not_binding _ _ notBinding, id_eq,
      decodeEventAction_swap_of_not_binding _ setup.program count bound notBinding]

end Vegas

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} [DecidableEq (CellTy Player L)]
  {first second : ProtocolState setup.program}
  {publicAgree : PublicCellsAgree setup first second}
  {succeed : CommitmentCellsSucceed setup first second}

/-- **Swapped completions decode to swapped action lists.** -/
theorem decodeHistory_betweenPairs (completions : List (graph setup).Completion) :
    decodeHistory setup.program ((completions.map
        (EventGraph.ValueSwap.ofPairs (betweenPairs publicAgree succeed)).completion).map
          (setup.eventGraph.fromModeCompletion .sequential)) =
      (CellSwap.between setup.program first second).history
        (decodeHistory setup.program
          (completions.map (setup.eventGraph.fromModeCompletion .sequential))) := by
  funext who
  simp only [decodeHistory, CellSwap.history, decodeCompletions, EventGraph.ownCompletions,
    List.map_map, List.filter_map, List.filterMap_map, List.map_filterMap]
  congr 1
  · funext completion
    exact decodeEventAction_betweenPairs completion.event completion.action

/-- **Reading a swapped configuration reads the swapped point.** -/
theorem sourceServicePrefix?_betweenPairs (rank : Nat) (config : (graph setup).Config) :
    sourceServicePrefix? setup rank (config.swap (EventGraph.ValueSwap.ofPairs
        (betweenPairs publicAgree succeed))) =
      (sourceServicePrefix? setup rank config).map
        ((CellSwap.between setup.program first second).protocolState setup.program) := by
  unfold sourceServicePrefix? serviceSourcePrefix?
  rw [EventGraph.Config.swap_store, EventGraph.Config.swap_history, decodeHistory_betweenPairs]
  exact decodeSourcePrefix?_swap _ _ rank setup.program _ [] _ _ refsCorr_initial_between
    outputsCorr_between config.store _

end Vegas
