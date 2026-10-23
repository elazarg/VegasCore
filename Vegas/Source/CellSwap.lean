/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProtocolState

/-! # Swapping source cells by name

A *cell swap* (`Vegas.SourceProgram.CellSwap`) is an involution on the value of
every cell, indexed by the cell's name and kind. It acts on a typed source
state cell by cell, on an action by swapping a commitment's choice under the
committed name, on the per-player action lists, and on configurations and
program points, leaving the obligations and publication status unchanged
(`Vegas.SourceProgram.CellSwap.protocolState`).

The cells of a program point can be looked up by name and kind
(`Vegas.SourceProgram.ProtocolState.cell?`). Two program points define the
swap that exchanges, at every name and kind present at both, the two values
found there (`Vegas.SourceProgram.CellSwap.between`).
-/

namespace Vegas.SourceProgram

variable {Player : Type} {L : IExpr}

variable (Player L) in
/-- **A cell swap.** An involution on cell values, by name and kind. -/
structure CellSwap where
  /-- The swap of the value of a cell with this name and kind. -/
  cell : VarId → (kind : CellTy Player L) → CellVal L kind → CellVal L kind
  cell_involutive : ∀ name kind, Function.Involutive (cell name kind)

namespace CellSwap

variable (swap : CellSwap Player L)

/-- The swap of a typed source state, cell by cell. -/
def state {Γ : SourceCtx Player L} (cells : State L Γ) : State L Γ :=
  fun name kind source => swap.cell name kind (cells name kind source)

/-- The swap of an own action: a commitment's choice is swapped under its name. -/
def action : OwnAction Player L → OwnAction Player L
  | .commit owner name payload choice =>
      .commit owner name payload (swap.cell name (.commitment owner payload) choice)
  | .reveal owner name disclose => .reveal owner name disclose

/-- The swap of every player's action list. -/
def history (actions : History Player L) : History Player L :=
  fun who => (actions who).map swap.action

variable [IExpr.ResultTypes L]

/-- The swap of a configuration: of its cells and its action lists. -/
def config {Γ : SourceCtx Player L} (current : Config Player L Γ) : Config Player L Γ :=
  ⟨swap.state current.state, current.registry, current.revelations, swap.history current.history⟩

variable [DecidableEq Player]

/-- **The swap of a program point.** -/
def protocolState : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → ProtocolState program
  | _, _, .ret _ => swap.config
  | _, _, .sample _ _ _ next => Sum.map swap.config (protocolState next)
  | _, _, .commit _ _ _ _ next => Sum.map swap.config (protocolState next)
  | _, _, .reveal _ _ _ _ _ _ next => Sum.map swap.config (protocolState next)

omit [IExpr.ResultTypes L] [DecidableEq Player] in
theorem state_involutive {Γ : SourceCtx Player L} :
    Function.Involutive (swap.state (Γ := Γ)) := by
  intro cells
  funext name kind source
  exact swap.cell_involutive name kind _

omit [IExpr.ResultTypes L] [DecidableEq Player] in
theorem action_involutive : Function.Involutive swap.action := by
  intro original
  cases original with
  | commit owner name payload choice =>
      simp only [action, swap.cell_involutive name (.commitment owner payload) choice]
  | reveal => rfl

omit [IExpr.ResultTypes L] [DecidableEq Player] in
theorem history_involutive : Function.Involutive swap.history := by
  intro actions
  funext who
  simp only [history, List.map_map]
  conv_rhs => rw [← List.map_id (actions who)]
  exact List.map_congr_left fun original _ => swap.action_involutive original

omit [IExpr.ResultTypes L] [DecidableEq Player] in
theorem config_involutive {Γ : SourceCtx Player L} :
    Function.Involutive (swap.config (Γ := Γ)) := by
  rintro ⟨cells, registry, revelations, actions⟩
  simp only [config, swap.state_involutive cells, swap.history_involutive actions]

theorem protocolState_involutive : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Function.Involutive (swap.protocolState program)
  | _, _, .ret _ => swap.config_involutive
  | _, _, .sample _ _ _ next => by
      rintro (current | rest)
      · exact congrArg Sum.inl (swap.config_involutive current)
      · exact congrArg Sum.inr (protocolState_involutive next rest)
  | _, _, .commit _ _ _ _ next => by
      rintro (current | rest)
      · exact congrArg Sum.inl (swap.config_involutive current)
      · exact congrArg Sum.inr (protocolState_involutive next rest)
  | _, _, .reveal _ _ _ _ _ _ next => by
      rintro (current | rest)
      · exact congrArg Sum.inl (swap.config_involutive current)
      · exact congrArg Sum.inr (protocolState_involutive next rest)

@[simp] theorem protocolState_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (current : Config Player L Γ) :
    swap.protocolState program (ProtocolState.entry program current) =
      ProtocolState.entry program (swap.config current) := by
  cases program <;> rfl

end CellSwap

variable [IExpr.ResultTypes L] [DecidableEq Player]

/-- The value of the first cell of a state with this name and kind. -/
def State.cell? [DecidableEq (CellTy Player L)] :
    {Γ : SourceCtx Player L} → State L Γ → VarId → (kind : CellTy Player L) →
      Option (CellVal L kind)
  | [], _, _, _ => none
  | (current, currentKind) :: _, cells, name, kind =>
      if same : current = name ∧ currentKind = kind then
        some (same.2 ▸ cells current currentKind .here)
      else State.cell? (fun other otherKind source => cells other otherKind (.there source))
        name kind

/-- The value of a cell of a program point, by name and kind. -/
def ProtocolState.cell? [DecidableEq (CellTy Player L)] :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → VarId →
      (kind : CellTy Player L) → Option (CellVal L kind)
  | _, _, .ret _ => fun current => State.cell? current.state
  | _, _, .sample _ _ _ next => Sum.elim (fun current => State.cell? current.state)
      (ProtocolState.cell? next)
  | _, _, .commit _ _ _ _ next => Sum.elim (fun current => State.cell? current.state)
      (ProtocolState.cell? next)
  | _, _, .reveal _ _ _ _ _ _ next => Sum.elim (fun current => State.cell? current.state)
      (ProtocolState.cell? next)

open Classical in
/-- The transposition of two found values; the identity unless both are found. -/
noncomputable def swapFound {α : Type*} : Option α → Option α → α → α
  | some left, some right => Equiv.swap left right
  | _, _ => id

theorem swapFound_involutive {α : Type*} (left right : Option α) :
    Function.Involutive (swapFound left right) := by
  classical
  cases left <;> cases right <;> first
    | exact fun _ => rfl
    | exact fun value => Equiv.swap_apply_self _ _ value

/-- **The swap between two program points**: at each name and kind present at
both, the transposition of their two values. -/
noncomputable def CellSwap.between [DecidableEq (CellTy Player L)] {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (first second : ProtocolState program) : CellSwap Player L where
  cell name kind := swapFound (ProtocolState.cell? program first name kind)
    (ProtocolState.cell? program second name kind)
  cell_involutive _ _ := swapFound_involutive _ _

end Vegas.SourceProgram
