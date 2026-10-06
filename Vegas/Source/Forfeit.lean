/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Honest
import Vegas.Source.PrivateInputs

/-! # Forfeiting failed reveals

A reveal instruction writes one publication cell of the terminal context and has
one owner. `Vegas.SourceProgram.revealCells` lists those cells with their owners;
publication cells present at setup are not reveal sites and are not listed.
`Vegas.SourceProgram.failedReveals` counts, in a public outcome, the failed
publications of a player's reveals, and `Vegas.SourceProgram.forfeitUtility`
subtracts a forfeit for each of them from a utility. Nothing is subtracted on a
terminal state in which no cell records a failure.
-/

noncomputable section

namespace Vegas

variable {Player : Type} {L : IExpr} [R : IExpr.ResultTypes L]

/-- A publication cell's place in the public context. -/
def publicRef {x : VarId} {τ : L.Ty} : {Γ : SourceCtx Player L} →
    HasVar Γ x (.publication τ) → HasVar (SourcePublicCtx L Γ) x (R.result τ)
  | (_, .publication _) :: _, .here => .here
  | (_, .publicData _) :: _, .there cell => .there (publicRef cell)
  | (_, .commitment _ _) :: _, .there cell => (publicRef cell :)
  | (_, .privateInput _ _) :: _, .there cell => (publicRef cell :)
  | (_, .publication _) :: _, .there cell => .there (publicRef cell)

/-- The public environment carries each publication result at its public
reference. -/
theorem sourcePublicEnv_get_publicRef {x : VarId} {τ : L.Ty} :
    {Γ : SourceCtx Player L} → (state : State L Γ) → (cell : HasVar Γ x (.publication τ)) →
      (sourcePublicEnv state).get (publicRef cell) = (R.valueEquiv τ).symm (state.get cell)
  | (_, .publication _) :: _, _, .here => by
      rw [sourcePublicEnv]
      rfl
  | (_, .publicData _) :: _, state, .there cell => by
      rw [sourcePublicEnv]
      exact sourcePublicEnv_get_publicRef (fun _ _ h => state.get (HasVar.there h)) cell
  | (_, .commitment _ _) :: _, state, .there cell => by
      rw [sourcePublicEnv]
      exact sourcePublicEnv_get_publicRef (fun _ _ h => state.get (HasVar.there h)) cell
  | (_, .privateInput _ _) :: _, state, .there cell => by
      rw [sourcePublicEnv]
      exact sourcePublicEnv_get_publicRef (fun _ _ h => state.get (HasVar.there h)) cell
  | (_, .publication _) :: _, state, .there cell => by
      rw [sourcePublicEnv]
      exact sourcePublicEnv_get_publicRef (fun _ _ h => state.get (HasVar.there h)) cell

namespace SourceProgram

variable [DecidableEq Player]

/-- The publication cell a reveal instruction writes, with the reveal's owner. -/
structure RevealCell (Γ : SourceCtx Player L) where
  owner : Player
  payload : L.Ty
  name : VarId
  cell : HasVar Γ name (.publication payload)

/-- The reveal sites of a program, as cells of its terminal context. -/
def revealCells : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → List (RevealCell p.terminalCtx)
  | _, _, .ret _ => []
  | _, _, .sample _ _ _ next => revealCells next
  | _, _, .commit _ _ _ _ next => revealCells next
  | _, _, .reveal (payload := payload) published owner _ _ _ _ next =>
      ⟨owner, payload, published, terminalRef next .here⟩ :: revealCells next

/-- Whether a public outcome records a failed publication at a reveal cell. -/
def RevealCell.failed {Γ : SourceCtx Player L} (cell : RevealCell Γ)
    (outcome : Env L.Val (SourcePublicCtx L Γ)) : Bool :=
  !(R.valueEquiv cell.payload (outcome.get (publicRef cell.cell))).isSuccess

/-- How many of a player's reveals failed in a public outcome. -/
def failedReveals {Γ : SourceCtx Player L} {O : Finset VarId}
    (p : SourceProgram Player L Γ O) (who : Player) (outcome : PublicOutcome p) : ℕ :=
  ((revealCells p).filter fun cell => decide (cell.owner = who) && cell.failed outcome).length

/-- A utility with a forfeit of `forfeit` for each failed reveal a player owns. -/
def forfeitUtility {Γ : SourceCtx Player L} {O : Finset VarId} {Parameter : Type}
    (p : SourceProgram Player L Γ O) (forfeit : ℝ)
    (utility : Parameter × PublicOutcome p → Player → ℝ) :
    Parameter × PublicOutcome p → Player → ℝ :=
  fun outcome who => utility outcome who - forfeit * failedReveals p who outcome.2

variable {Γ : SourceCtx Player L} {O : Finset VarId}

/-- A cell holding a value is not failed in the public outcome. -/
theorem RevealCell.failed_publicOutcome_of_success (p : SourceProgram Player L Γ O)
    (cell : RevealCell p.terminalCtx) (terminal : State L p.terminalCtx)
    {value : L.Val cell.payload} (holds : terminal.get cell.cell = .success value) :
    cell.failed (publicOutcome p terminal) = false := by
  simp [RevealCell.failed, publicOutcome, sourcePublicEnv_get_publicRef, holds,
    PublicationResult.isSuccess]

/-- No reveal fails on a terminal state in which no cell records a failure. -/
theorem failedReveals_publicOutcome_of_successful (p : SourceProgram Player L Γ O)
    (terminal : State L p.terminalCtx) (successful : Successful terminal) (who : Player) :
    failedReveals p who (publicOutcome p terminal) = 0 := by
  rw [failedReveals, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro cell _
  obtain ⟨value, holds⟩ := successful.publications cell.cell
  simp [RevealCell.failed_publicOutcome_of_success p cell terminal holds]

/-- The forfeit changes no payoff on a terminal state in which no cell records
a failure. -/
theorem forfeitUtility_of_successful {Parameter : Type} (p : SourceProgram Player L Γ O)
    (forfeit : ℝ) (utility : Parameter × PublicOutcome p → Player → ℝ)
    (parameter : Parameter) (terminal : State L p.terminalCtx)
    (successful : Successful terminal) (who : Player) :
    forfeitUtility p forfeit utility (parameter, publicOutcome p terminal) who =
      utility (parameter, publicOutcome p terminal) who := by
  simp [forfeitUtility, failedReveals_publicOutcome_of_successful p terminal successful]

/-- A nonnegative forfeit never raises a payoff. -/
theorem forfeitUtility_le {Parameter : Type} (p : SourceProgram Player L Γ O)
    {forfeit : ℝ} (nonnegative : 0 ≤ forfeit)
    (utility : Parameter × PublicOutcome p → Player → ℝ)
    (outcome : Parameter × PublicOutcome p) (who : Player) :
    forfeitUtility p forfeit utility outcome who ≤ utility outcome who := by
  have : 0 ≤ forfeit * (failedReveals p who outcome.2 : ℝ) :=
    mul_nonneg nonnegative (Nat.cast_nonneg _)
  simp only [forfeitUtility]
  linarith

end SourceProgram

end Vegas
