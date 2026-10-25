/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCounterpartGuard
import Vegas.Source.PrivateInputsIndependent

/-! # Splicing two source points for a player

The splice of two program points `mine` and `others` at the same position for a
player `who` (`Vegas.SourceProgram.ProtocolState.splicePoint`) is `mine` with
every cell that is not hidden for `who` (`Vegas.CellTy.hiddenOwner?`) swapped
to the value `others` holds there: it keeps `who`'s private inputs and
commitments from `mine` and takes every other player's from `others`.

Fix a point `p` and a point `w` agreeing with `p` on public cells, and splice
them for a player `r`.

* The splice agrees with `p` on public cells
  (`Vegas.publicCellsAgree_splicePoint`).
* It agrees with `p` on every cell `r` sees (`Vegas.cell?_splicePoint_of_visible`).
  A swap between two points agreeing on every cell a player sees fixes that
  player when every accepted handle belongs to the owner of its field
  (`Vegas.fixes_between_of_visible`).
* It agrees with `p` wherever `w` does (`Vegas.cell?_splicePoint_eq_of_agree`).
* With independent hidden initial cells, it finds the cells of a supported draw
  when `p` and `w` do (`Vegas.drawn_splicePoint`).
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  [DecidableEq (CellTy Player L)]

/-- **The swap between two points outside a player's hidden cells**: the swap
between the two points, except on the cells hidden for `who`. -/
noncomputable def CellSwap.betweenOthers {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (who : Player)
    (first second : ProtocolState program) : CellSwap Player L where
  cell name kind := if kind.hiddenOwner? = some who then id
    else swapFound (ProtocolState.cell? program first name kind)
      (ProtocolState.cell? program second name kind)
  cell_involutive name kind := by
    by_cases hidden : kind.hiddenOwner? = some who
    · simp only [hidden, ↓reduceIte]
      exact fun _ => rfl
    · simp only [hidden, ↓reduceIte]
      exact swapFound_involutive _ _

namespace ProtocolState

/-- **The splice of two points for a player**: `mine`, with every cell not hidden
for `who` swapped to the value `others` holds there. -/
noncomputable def splicePoint {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (who : Player) (mine others : ProtocolState program) :
    ProtocolState program :=
  (CellSwap.betweenOthers program who mine others).protocolState program mine

variable {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}
  {who : Player} {mine others : ProtocolState program} {name : VarId} {kind : CellTy Player L}

/-- The splice keeps a cell hidden for the player. -/
theorem cell?_splicePoint_of_hidden (hidden : kind.hiddenOwner? = some who) :
    cell? program (splicePoint program who mine others) name kind =
      cell? program mine name kind := by
  rw [splicePoint, cell?_swap]
  simp only [CellSwap.betweenOthers, hidden, ↓reduceIte]
  cases cell? program mine name kind <;> rfl

/-- The splice keeps every cell whose value found at both points agrees. -/
theorem cell?_splicePoint_eq_mine
    (agree : ∀ left right, cell? program mine name kind = some left →
      cell? program others name kind = some right → left = right) :
    cell? program (splicePoint program who mine others) name kind =
      cell? program mine name kind := by
  rw [splicePoint, cell?_swap]
  cases mineFound : cell? program mine name kind with
  | none => rfl
  | some left =>
      simp only [CellSwap.betweenOthers, Option.map_some, mineFound]
      split_ifs
      · rfl
      · cases othersFound : cell? program others name kind with
        | none => rfl
        | some right =>
            obtain rfl := agree left right mineFound othersFound
            simp [swapFound]

/-- The splice keeps every cell holding the same lookup at both points. -/
theorem cell?_splicePoint_of_eq
    (same : cell? program mine name kind = cell? program others name kind) :
    cell? program (splicePoint program who mine others) name kind =
      cell? program mine name kind :=
  cell?_splicePoint_eq_mine fun _ _ left right =>
    Option.some.inj (left.symm.trans (same.trans right))

/-- Outside the player's hidden cells, the splice takes the value found at
`others` wherever both points find one. -/
theorem cell?_splicePoint_of_found (hidden : kind.hiddenOwner? ≠ some who)
    {left right : CellVal L kind} (mineFound : cell? program mine name kind = some left)
    (othersFound : cell? program others name kind = some right) :
    cell? program (splicePoint program who mine others) name kind = some right := by
  rw [splicePoint, cell?_swap, mineFound]
  simp [CellSwap.betweenOthers, hidden, mineFound, othersFound, swapFound]

/-- The splice keeps the cells of `mine` that `others` does not find. -/
theorem cell?_splicePoint_of_none (missing : cell? program others name kind = none) :
    cell? program (splicePoint program who mine others) name kind =
      cell? program mine name kind :=
  cell?_splicePoint_eq_mine fun _ _ _ found => by rw [missing] at found; cases found

omit [DecidableEq (CellTy Player L)] in
/-- **A swapped point stays at its position.** -/
theorem sameShape_swap (swap : CellSwap Player L) : {Γ : SourceCtx Player L} →
    {O : Finset VarId} → (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    SameShape program state (swap.protocolState program state)
  | _, _, .ret _, _ => trivial
  | _, _, .sample _ _ _ next, state => by
      cases state with
      | inl _ => trivial
      | inr rest => exact sameShape_swap swap next rest
  | _, _, .commit _ _ _ _ next, state => by
      cases state with
      | inl _ => trivial
      | inr rest => exact sameShape_swap swap next rest
  | _, _, .reveal _ _ _ _ _ _ next, state => by
      cases state with
      | inl _ => trivial
      | inr rest => exact sameShape_swap swap next rest

omit [DecidableEq (CellTy Player L)] in
/-- **A swapped point stays at the position of the points it shares one with.** -/
theorem sameShape_swap_left (swap : CellSwap Player L) : {Γ : SourceCtx Player L} →
    {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (left right : ProtocolState program) → SameShape program left right →
      SameShape program (swap.protocolState program left) right
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, left, right, shape => by
      cases left with
      | inl _ =>
          cases right with
          | inl _ => trivial
          | inr _ => exact shape.elim
      | inr first =>
          cases right with
          | inl _ => exact shape.elim
          | inr second => exact sameShape_swap_left swap next first second shape
  | _, _, .commit _ _ _ _ next, left, right, shape => by
      cases left with
      | inl _ =>
          cases right with
          | inl _ => trivial
          | inr _ => exact shape.elim
      | inr first =>
          cases right with
          | inl _ => exact shape.elim
          | inr second => exact sameShape_swap_left swap next first second shape
  | _, _, .reveal _ _ _ _ _ _ next, left, right, shape => by
      cases left with
      | inl _ =>
          cases right with
          | inl _ => trivial
          | inr _ => exact shape.elim
      | inr first =>
          cases right with
          | inl _ => exact shape.elim
          | inr second => exact sameShape_swap_left swap next first second shape

end ProtocolState

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Whether a state finds a cell depends only on its context. -/
theorem State.isSome_cell?_eq (name : VarId) (kind : CellTy Player L) :
    {Γ : SourceCtx Player L} → (left right : State L Γ) →
      (State.cell? left name kind).isSome = (State.cell? right name kind).isSome
  | [], _, _ => rfl
  | (current, currentKind) :: _, left, right => by
      rw [State.cell?.eq_2, State.cell?.eq_2]
      split_ifs
      · rfl
      · exact State.isSome_cell?_eq name kind _ _

namespace ProtocolState

/-- Whether a point finds a cell depends only on its position. -/
theorem isSome_cell?_eq_of_sameShape (name : VarId) (kind : CellTy Player L) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (left right : ProtocolState program) → SameShape program left right →
      (cell? program left name kind).isSome = (cell? program right name kind).isSome
  | _, _, .ret _, left, right, _ => State.isSome_cell?_eq name kind left.state right.state
  | _, _, .sample _ _ _ next, left, right, shape => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact State.isSome_cell?_eq name kind first.state second.state
          | inr _ => exact shape.elim
      | inr first =>
          cases right with
          | inl _ => exact shape.elim
          | inr second => exact isSome_cell?_eq_of_sameShape name kind next first second shape
  | _, _, .commit _ _ _ _ next, left, right, shape => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact State.isSome_cell?_eq name kind first.state second.state
          | inr _ => exact shape.elim
      | inr first =>
          cases right with
          | inl _ => exact shape.elim
          | inr second => exact isSome_cell?_eq_of_sameShape name kind next first second shape
  | _, _, .reveal _ _ _ _ _ _ next, left, right, shape => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact State.isSome_cell?_eq name kind first.state second.state
          | inr _ => exact shape.elim
      | inr first =>
          cases right with
          | inl _ => exact shape.elim
          | inr second => exact isSome_cell?_eq_of_sameShape name kind next first second shape

variable {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}
  {who : Player} {mine others : ProtocolState program} {name : VarId} {kind : CellTy Player L}

/-- Outside the player's hidden cells, the splice of two points at the same
position finds what `others` finds. -/
theorem cell?_splicePoint_of_not_hidden (hidden : kind.hiddenOwner? ≠ some who)
    (shape : SameShape program mine others) :
    cell? program (splicePoint program who mine others) name kind =
      cell? program others name kind := by
  have found := isSome_cell?_eq_of_sameShape name kind program mine others shape
  cases mineFound : cell? program mine name kind with
  | none =>
      rw [mineFound] at found
      cases othersFound : cell? program others name kind with
      | none => rw [cell?_splicePoint_of_none othersFound, mineFound]
      | some _ => rw [othersFound] at found; cases found
  | some left =>
      rw [mineFound] at found
      cases othersFound : cell? program others name kind with
      | none => rw [othersFound] at found; cases found
      | some right => exact cell?_splicePoint_of_found hidden mineFound othersFound

end ProtocolState

end Vegas.SourceProgram

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} [DecidableEq (CellTy Player L)]
  {p w : ProtocolState setup.program} {r : Player}

/-- **The splice agrees with the first point on public cells.** -/
theorem publicCellsAgree_splicePoint (publicAgree : PublicCellsAgree setup p w) :
    PublicCellsAgree setup p (ProtocolState.splicePoint setup.program r p w) := by
  intro name kind isPublic left right leftFound rightFound
  have kept := ProtocolState.cell?_splicePoint_eq_mine (who := r) (others := w)
    (publicAgree name kind isPublic)
  rw [kept, leftFound] at rightFound
  exact Option.some.inj rightFound

/-- **The splice agrees with the first point on every cell the player sees**,
when the two points agree on public cells. -/
theorem cell?_splicePoint_of_visible (publicAgree : PublicCellsAgree setup p w) (name : VarId)
    {kind : CellTy Player L} (visible : (cellField kind).VisibleTo r) :
    ProtocolState.cell? setup.program p name kind =
      ProtocolState.cell? setup.program (ProtocolState.splicePoint setup.program r p w)
        name kind := by
  symm
  cases kind with
  | publicData => exact ProtocolState.cell?_splicePoint_eq_mine (publicAgree name _ trivial)
  | publication => exact ProtocolState.cell?_splicePoint_eq_mine (publicAgree name _ trivial)
  | commitment owner payload =>
      cases (visible : owner = r)
      exact ProtocolState.cell?_splicePoint_of_hidden rfl
  | privateInput owner payload =>
      cases (visible : owner = r)
      exact ProtocolState.cell?_splicePoint_of_hidden rfl

/-- **The splice agrees with the first point wherever the second does.** -/
theorem cell?_splicePoint_eq_of_agree {name : VarId} {kind : CellTy Player L}
    (agree : ProtocolState.cell? setup.program p name kind =
      ProtocolState.cell? setup.program w name kind) :
    ProtocolState.cell? setup.program p name kind =
      ProtocolState.cell? setup.program (ProtocolState.splicePoint setup.program r p w)
        name kind :=
  (ProtocolState.cell?_splicePoint_of_eq agree).symm

/-- **The splice finds the splice of the draws found at the two points.** -/
theorem initialCellsAt_splicePoint {mine others : State L setup.context}
    (mineCells : InitialCellsAt mine p) (othersCells : InitialCellsAt others w) :
    InitialCellsAt (splice r mine others) (ProtocolState.splicePoint setup.program r p w) := by
  intro name kind source
  change _ = some (if kind.hiddenOwner? = some r then mine name kind source
    else others name kind source)
  split_ifs with hidden
  · rw [ProtocolState.cell?_splicePoint_of_hidden hidden]
    exact mineCells source
  · exact ProtocolState.cell?_splicePoint_of_found hidden (mineCells source) (othersCells source)

/-- **With independent hidden initial cells, the splice finds the cells of a
supported draw** when both points do. -/
theorem drawn_splicePoint (independent : setup.PrivateInputsIndependent)
    (drawnP : ∃ initial ∈ setup.initialLaw.support, InitialCellsAt initial p)
    (drawnW : ∃ initial ∈ setup.initialLaw.support, InitialCellsAt initial w) :
    ∃ initial ∈ setup.initialLaw.support,
      InitialCellsAt initial (ProtocolState.splicePoint setup.program r p w) := by
  obtain ⟨mine, mineMember, mineCells⟩ := drawnP
  obtain ⟨others, othersMember, othersCells⟩ := drawnW
  exact ⟨_, setup.splice_mem_support (fun _ => ())
    (fun owner first second _ => independent owner first second) r mineMember othersMember rfl,
    initialCellsAt_splicePoint mineCells othersCells⟩

section Fixes

variable {q : ProtocolState setup.program} {publicAgree : PublicCellsAgree setup p q}
  {succeed : CommitmentCellsSucceed setup p q}

/-- A field a player sees has no pair between two points agreeing on the cells
the player sees. -/
theorem betweenPairs_of_visible {who : Player}
    (visibleAgree : ∀ name {kind : CellTy Player L}, (cellField kind).VisibleTo who →
      ProtocolState.cell? setup.program p name kind = ProtocolState.cell? setup.program q name kind)
    {field : (graph setup).Field} (visible : (graph setup).fieldVisibleTo who field) :
    (betweenPairs publicAgree succeed).pair field = none := by
  have seen : (cellField (fieldCell setup field).2).VisibleTo who :=
    (layout_fieldCell setup field) ▸ visible
  exact betweenPair_eq_none_of_agree (field := field) rfl (visibleAgree _ seen)

/-- **The swap between two points agreeing on the cells a player sees fixes the
player** when every accepted handle belongs to the owner of its field. -/
theorem fixes_between_of_visible {who : Player}
    (visibleAgree : ∀ name {kind : CellTy Player L}, (cellField kind).VisibleTo who →
      ProtocolState.cell? setup.program p name kind = ProtocolState.cell? setup.program q name kind)
    {table : AcceptedHandles (graph setup)}
    (owned : ∀ field handle, table field = some handle →
      ∃ payload, (graph setup).layout field = .binding handle.1 payload) :
    (HiddenSwap.ofPairs (betweenPairs publicAgree succeed)
      (betweenHandlePairs setup p q table)).Fixes who := by
  refine ⟨fun field visible => ?_, fun event acting => ?_, fun slot => ?_⟩
  · change EventGraph.pairSwap ((betweenPairs publicAgree succeed).pair field) = id
    rw [betweenPairs_of_visible visibleAgree visible]
    rfl
  · change (betweenPairs publicAgree succeed).action event = id
    unfold EventGraph.SwapPairs.action
    cases nodeView (graph setup) event with
    | resolve | sample => rfl
    | bind owner payload outputEq codeEq =>
        rw [nodeView_bind_actor outputEq codeEq] at acting
        cases Option.some.inj acting
        have visible : (graph setup).fieldVisibleTo who (.inr event) := by
          change ((graph setup).outputLayout event).VisibleTo who
          rw [outputEq]
          rfl
        rw [betweenPairs_of_visible visibleAgree visible]
        funext original
        simp [EventGraph.pairSwap]
  · change EventGraph.pairSwap (betweenHandlePairs setup p q table (who, slot)) = id
    unfold betweenHandlePairs
    split_ifs with found
    · obtain ⟨payload, layoutEq⟩ := owned _ _ found.choose_spec
      have kind := cellField_eq_binding
        ((layout_fieldCell setup found.choose).symm.trans layoutEq)
      have cell : fieldCell setup found.choose =
          ((fieldCell setup found.choose).1, .commitment who payload) := Prod.ext rfl kind
      rw [cell, commitmentRawPair_eq_none_of_agree
        (visibleAgree _ (show (cellField (CellTy.commitment who payload)).VisibleTo who from rfl))]
      rfl
    · rfl

end Fixes

end Vegas
