module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.DecodedRevelations

@[expose] public section

/-! # The swap between two source points at accepted handles

At a table of accepted handles, the swap between two source points swaps the
value prepared at a handle accepted for a commitment cell whose values at the
two points are two different successes: the transposition of the two typed
values (`Vegas.betweenHandlePairs`). Every handle accepted at a binding event of
an injective table is then compatible with the swap
(`Vegas.bindCompatible_betweenHandlePairs`).
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} [DecidableEq (CellTy Player L)]

section Pairs

variable (setup) (first second : ProtocolState setup.program)

open Classical in
/-- The pair of prepared values of a commitment cell between two points: the two
typed values, when both cells hold different successes. -/
def commitmentRawPair : VarId × CellTy Player L → Option (Raw L × Raw L)
  | (name, .commitment owner payload) =>
      match ProtocolState.cell? setup.program first name (.commitment owner payload),
        ProtocolState.cell? setup.program second name (.commitment owner payload) with
      | some (.success left), some (.success right) =>
          if left = right then none else some (⟨payload, left⟩, ⟨payload, right⟩)
      | _, _ => none
  | (_, .publicData _) | (_, .privateInput _ _) | (_, .publication _) => none

open Classical in
/-- **The handle pairs between two points at a table of accepted handles.** -/
def betweenHandlePairs (table : AcceptedHandles setup.informationGraph) (handle : Handle
  setup.informationGraph) :
    Option (Raw L × Raw L) :=
  if accepted : ∃ field, table field = some handle then
    commitmentRawPair setup first second (fieldCell setup accepted.choose)
  else none

end Pairs

/-- A table of accepted handles is injective. -/
def AcceptedInjective (table : AcceptedHandles setup.informationGraph) : Prop :=
  ∀ left right handle, table left = some handle → table right = some handle → left = right

variable {first second : ProtocolState setup.program}
  {publicAgree : PublicCellsAgree setup first second}
  {succeed : CommitmentCellsSucceed setup first second}

theorem betweenHandlePairs_of_accepted {table : AcceptedHandles setup.informationGraph}
    (injective : AcceptedInjective table) {field : setup.informationGraph.Field}
    {handle : Handle setup.informationGraph} (accepted : table field = some handle) :
    betweenHandlePairs setup first second table handle =
      commitmentRawPair setup first second (fieldCell setup field) := by
  unfold betweenHandlePairs
  have found : ∃ field, table field = some handle := ⟨field, accepted⟩
  rw [dite_eq_left_of_eq_true (eq_true found),
    injective _ _ _ found.choose_spec accepted]

theorem betweenPair_eq {field : setup.informationGraph.Field} {name : VarId} {kind : CellTy Player
  L}
    (cell : fieldCell setup field = (name, kind))
    (layoutEq : setup.informationGraph.layout field = cellField kind) :
    betweenPair setup first second field = transportPair layoutEq.symm
      (cellPair (ProtocolState.cell? setup.program first name kind)
        (ProtocolState.cell? setup.program second name kind)) := by
  unfold betweenPair
  have general : ∀ (found : VarId × CellTy Player L)
      (fieldEq : setup.informationGraph.layout field = cellField found.2), found = (name, kind) →
      cellPairAt setup first second found fieldEq = transportPair layoutEq.symm
        (cellPair (ProtocolState.cell? setup.program first name kind)
          (ProtocolState.cell? setup.program second name kind)) := by
    rintro found fieldEq rfl
    rfl
  exact general _ _ cell

/-- **Accepted handles are compatible with the swap between two points.** -/
theorem bindCompatible_betweenHandlePairs {table : AcceptedHandles setup.informationGraph}
    (injective : AcceptedInjective table) {event : setup.informationGraph.EventId}
    {handle : Handle setup.informationGraph} (accepted : table (.inr event) = some handle) :
    BindCompatible (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
      (betweenHandlePairs setup first second table)) event handle := by
  intro owner payload outputEq candidate
  have cellKind : (eventCell setup.program event).2 = .commitment owner payload := by
    have layoutEq := (outputLayout_eventCell setup.program event).symm.trans outputEq
    revert layoutEq
    rcases (eventCell setup.program event).2 with _ | _ | _ | _
    all_goals intro layoutEq
    all_goals cases layoutEq
    rfl
  rcases cellEq : eventCell setup.program event with ⟨name, kind⟩
  rw [cellEq] at cellKind
  change kind = _ at cellKind
  subst cellKind
  have pairEq := betweenPair_eq (first := first) (second := second)
    (field := .inr event) cellEq outputEq
  have handleEq := betweenHandlePairs_of_accepted (first := first) (second := second) injective
    accepted
  change _ = commitmentRawPair setup first second (eventCell setup.program event) at handleEq
  rw [cellEq] at handleEq
  cases foundFirst : ProtocolState.cell? setup.program first name (.commitment owner payload)
    with
  | none =>
      rw [foundFirst] at pairEq
      simp only [commitmentRawPair, foundFirst] at handleEq
      exact HiddenSwap.bindCompatible_ofPairs_none _ _ (pairEq.trans (transportPair_none _))
        handleEq owner payload outputEq candidate
  | some firstValue =>
      cases foundSecond : ProtocolState.cell? setup.program second name
          (.commitment owner payload) with
      | none =>
          rw [foundFirst, foundSecond] at pairEq
          simp only [commitmentRawPair, foundFirst, foundSecond] at handleEq
          exact HiddenSwap.bindCompatible_ofPairs_none _ _
            (pairEq.trans (transportPair_none _)) handleEq owner payload outputEq candidate
      | some secondValue =>
          rw [foundFirst, foundSecond] at pairEq
          by_cases same : firstValue = secondValue
          · subst same
            simp only [cellPair, ↓reduceIte] at pairEq
            have handleNone : betweenHandlePairs setup first second table handle = none := by
              rw [handleEq]
              cases firstValue <;> simp [commitmentRawPair, foundFirst, foundSecond]
            exact HiddenSwap.bindCompatible_ofPairs_none _ _
              (pairEq.trans (transportPair_none _)) handleNone owner payload outputEq candidate
          · obtain ⟨firstOk, secondOk⟩ := succeed name owner payload firstValue secondValue
              foundFirst foundSecond same
            cases firstValue with
            | failure => exact (firstOk rfl).elim
            | success left =>
                cases secondValue with
                | failure => exact (secondOk rfl).elim
                | success right =>
                    have distinct : left ≠ right := fun equal => same (by rw [equal])
                    simp only [cellPair, same, ↓reduceIte, transportPair_some] at pairEq
                    have handlePair : betweenHandlePairs setup first second table handle =
                        some (⟨payload, left⟩, ⟨payload, right⟩) := by
                      rw [handleEq]
                      simp only [commitmentRawPair, foundFirst, foundSecond, distinct,
                        ↓reduceIte]
                    exact HiddenSwap.bindCompatible_ofPairs _ _ outputEq left right pairEq
                      handlePair owner payload outputEq candidate

/-- A swap pair at a field whose cells agree at both points is absent. -/
theorem betweenPair_eq_none_of_agree {field : setup.informationGraph.Field} {name : VarId}
    {kind : CellTy Player L} (cell : fieldCell setup field = (name, kind))
    (agree : ProtocolState.cell? setup.program first name kind =
      ProtocolState.cell? setup.program second name kind) :
    betweenPair setup first second field = none := by
  rw [betweenPair_eq cell ((layout_fieldCell setup field).trans (by rw [cell]))]
  rw [agree]
  cases ProtocolState.cell? setup.program second name kind with
  | none => exact transportPair_none _
  | some value =>
      simp only [cellPair, ↓reduceIte]
      exact transportPair_none _

/-- A commitment pair at a cell whose values agree at both points is absent. -/
theorem commitmentRawPair_eq_none_of_agree {name : VarId} {owner : Player} {payload : L.Ty}
    (agree : ProtocolState.cell? setup.program first name (.commitment owner payload) =
      ProtocolState.cell? setup.program second name (.commitment owner payload)) :
    commitmentRawPair setup first second (name, .commitment owner payload) = none := by
  simp only [commitmentRawPair]
  rw [agree]
  cases ProtocolState.cell? setup.program second name (.commitment owner payload) with
  | none => rfl
  | some value => cases value <;> simp

/-- **The swap between two points fixes every reveal of a binding they agree on.** -/
theorem revealFixed_between {table : AcceptedHandles setup.informationGraph}
    (injective : AcceptedInjective table) (state : EventGraphRuntime.State setup.informationGraph)
    (kept : ∀ field handle, state.accepted field = some handle → table field = some handle)
    (event : setup.informationGraph.EventId)
    (agree : ∀ owner payload binding checks outputEq codeEq,
      nodeView setup.informationGraph event = .resolve owner payload binding checks outputEq codeEq
        →
      ProtocolState.cell? setup.program first (fieldCell setup binding.field).1
          (.commitment owner payload) =
        ProtocolState.cell? setup.program second (fieldCell setup binding.field).1
          (.commitment owner payload)) :
    RevealFixed (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
      (betweenHandlePairs setup first second table)) state event := by
  unfold RevealFixed
  cases view : nodeView setup.informationGraph event with
  | bind | sample => trivial
  | resolve owner payload binding checks outputEq codeEq =>
      have same := agree owner payload binding checks outputEq codeEq view
      obtain ⟨name, _, _, cell⟩ := fieldCell_resolveBinding outputEq codeEq
      rw [cell] at same
      refine ⟨?_, fun handle accepted => ?_⟩
      · change EventGraph.pairSwap (betweenPair setup first second binding.field) = id
        rw [betweenPair_eq_none_of_agree cell same]
        rfl
      · change EventGraph.pairSwap (betweenHandlePairs setup first second table handle) = id
        rw [betweenHandlePairs_of_accepted injective (kept _ _ accepted), cell,
          commitmentRawPair_eq_none_of_agree same]
        rfl

end Vegas
