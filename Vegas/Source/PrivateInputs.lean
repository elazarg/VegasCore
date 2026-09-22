/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.InitialState

/-! # Persistent private inputs

Only setup introduces private inputs. Programs preserve these ordinary values,
policies observe their own, and publication accounting ignores them. The shared
typed environment retains correlations with all other initial data.
-/

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Carry an initial reference through the immutable extensions of a program. -/
def terminalRef {name : VarId} {cell : CellTy Player L} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → HasVar Γ name cell →
      HasVar p.terminalCtx name cell
  | _, _, .ret _, input => input
  | _, _, .sample _ _ _ k, input => terminalRef k (.there input)
  | _, _, .commit _ _ _ _ k, input => terminalRef k (.there input)
  | _, _, .reveal _ _ _ _ _ _ k, input => terminalRef k (.there input)

/-- A terminal lookup of an initial reference agrees with initial-state readout. -/
theorem terminalRef_get {name : VarId} {cell : CellTy Player L}
    {Γ : SourceCtx Player L} {O : Finset VarId} (p : SourceProgram Player L Γ O)
    (terminal : State L p.terminalCtx) (input : HasVar Γ name cell) :
    terminal.get (terminalRef p input) = (initialState p terminal).get input := by
  induction p with
  | ret => rfl
  | sample _ _ _ k ih => exact ih terminal (.there input)
  | commit _ _ _ _ k ih => exact ih terminal (.there input)
  | reveal _ _ _ _ _ _ k ih => exact ih terminal (.there input)

/-- Every private input in a terminal context was already present at setup. -/
def initialInputRef {name : VarId} {owner : Player} {payload : L.Ty} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) →
      HasVar p.terminalCtx name (.privateInput owner payload) →
      HasVar Γ name (.privateInput owner payload)
  | _, _, .ret _, input => input
  | _, _, .sample _ _ _ k, input => match initialInputRef k input with
    | .there initial => initial
  | _, _, .commit _ _ _ _ k, input => match initialInputRef k input with
    | .there initial => initial
  | _, _, .reveal _ _ _ _ _ _ k, input => match initialInputRef k input with
    | .there initial => initial

/-- A supported execution preserves each owner's private input exactly. -/
theorem privateInput_preserved {Γ : SourceCtx Player L} {O : Finset VarId}
    (p : SourceProgram Player L Γ O) (profile : BehavioralProfile p)
    (config : Config Player L Γ) (terminal : State L p.terminalCtx)
    (supported : terminal ∈ (runFrom p profile config).support)
    {name : VarId} {owner : Player} {payload : L.Ty}
    (input : HasVar Γ name (.privateInput owner payload)) :
    terminal.get (terminalRef p input) = config.state.get input := by
  rw [terminalRef_get, initialState_runFrom p profile config terminal supported]

end Vegas.SourceProgram
