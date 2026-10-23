/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOwnerSwap
import Vegas.Source.PrivateInputsIndependent

/-! # The owner swap on initial draws

The owner swap between two views of `who` acts on the initial inputs of a draw
whose hidden cells for `who` are the first view's values by taking those hidden
cells from a draw holding the second view's values, and every other cell from
the draw itself (`Vegas.ownerSwap_inputs_splice`): its pairs sit exactly at the
inputs private to `who`, which are the inputs of the cells `who` hides
(`Vegas.privateTo_inl_iff`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Every position of a context is the position of a variable of it. -/
private theorem exists_inputId : ∀ (Γ : SourceCtx Player L) (input : Fin Γ.length),
    ∃ (name : VarId) (kind : CellTy Player L) (source : HasVar Γ name kind),
      inputId source = input
  | [], input => Fin.elim0 input
  | (name, kind) :: Γ, input => by
      cases input using Fin.cases with
      | zero => exact ⟨name, kind, .here, rfl⟩
      | succ input =>
          obtain ⟨other, otherKind, source, rfl⟩ := exists_inputId Γ input
          exact ⟨other, otherKind, .there source, rfl⟩

/-- **The inputs private to `who` are those of the cells `who` hides.** -/
theorem privateTo_inl_iff (who : Player) {name : VarId} {kind : CellTy Player L}
    (source : HasVar setup.context name kind) :
    PrivateTo who (setup := setup) (.inl (inputId source)) ↔ kind.hiddenOwner? = some who := by
  have layoutEq : (graph setup).layout (.inl (inputId source)) = cellField kind :=
    inputLayout_inputId source
  unfold PrivateTo EventGraph.fieldVisibleTo EventGraph.fieldPublic
  rw [layoutEq]
  cases kind with
  | publicData | publication =>
      simp [cellField, CellTy.hiddenOwner?, EventGraph.EventField.IsPublic]
  | privateInput owner payload | commitment owner payload =>
      simp [cellField, CellTy.hiddenOwner?, EventGraph.EventField.IsPublic,
        EventGraph.EventField.VisibleTo, eq_comm]

/-- At a private field where both views hold values that are not failures, the
owner swap sends the first view's value to the second's. -/
theorem pairSwap_ownerValuePair_of_present (who : Player)
    {first second : PlayerView (graph setup)} {field : (graph setup).Field}
    (privateTo : PrivateTo who field)
    {left right : ((graph setup).layout field).Value}
    (firstStore : first.observation.store field = some left)
    (secondStore : second.observation.store field = some right)
    (leftOk : ¬ ((graph setup).layout field).IsFailure left)
    (rightOk : ¬ ((graph setup).layout field).IsFailure right) :
    EventGraph.pairSwap (ownerValuePair who first second field) left = right := by
  classical
  unfold ownerValuePair
  simp only [privateTo, ↓reduceIte, firstStore, secondStore]
  by_cases same : left = right
  · subst same
    simp [EventGraph.pairSwap]
  · simp only [same, leftOk, rightOk, or_self, ↓reduceIte, EventGraph.pairSwap]
    exact Equiv.swap_apply_left _ _

/-- **The owner swap splices initial draws.** If the first view stores the
inputs of a draw `first` and the second view those of a draw `second` at every
input private to `who`, and no such stored value is a failure, the owner swap
sends the inputs of `first` to the inputs of the draw with `who`'s hidden cells
from `second` and every other cell from `first`. -/
theorem ownerSwap_inputs_splice (who : Player) {firstView secondView : PlayerView (graph setup)}
    (first second : State L setup.context)
    (firstStore : ∀ input, PrivateTo who (setup := setup) (.inl input) →
      firstView.observation.store (.inl input) = some (setup.eventInputs first input))
    (secondStore : ∀ input, PrivateTo who (setup := setup) (.inl input) →
      secondView.observation.store (.inl input) = some (setup.eventInputs second input))
    (firstOk : ∀ input, PrivateTo who (setup := setup) (.inl input) →
      ¬ ((graph setup).layout (.inl input)).IsFailure (setup.eventInputs first input))
    (secondOk : ∀ input, PrivateTo who (setup := setup) (.inl input) →
      ¬ ((graph setup).layout (.inl input)).IsFailure (setup.eventInputs second input)) :
    (ownerSwap who firstView secondView).inputs (setup.eventInputs first) =
      setup.eventInputs (splice who second first) := by
  funext input
  obtain ⟨name, kind, source, rfl⟩ := exists_inputId setup.context input
  change EventGraph.pairSwap (ownerValuePair who firstView secondView (.inl (inputId source)))
    (setup.eventInputs first (inputId source)) = _
  have layoutEq : (graph setup).layout (.inl (inputId source)) = cellField kind :=
    inputLayout_inputId source
  have splicedValue := encodeInputs_get (splice who second first : State L setup.context) source
  change cast _ (setup.eventInputs (splice who second first) (inputId source)) = _
    at splicedValue
  by_cases hidden : kind.hiddenOwner? = some who
  · have privateTo := (privateTo_inl_iff who source).mpr hidden
    rw [pairSwap_ownerValuePair_of_present who privateTo (firstStore _ privateTo)
      (secondStore _ privateTo) (firstOk _ privateTo) (secondOk _ privateTo)]
    apply (cast_inj (congrArg EventGraph.EventField.Value layoutEq)).mp
    have secondValue := encodeInputs_get second source
    change cast _ (setup.eventInputs second (inputId source)) = _ at secondValue
    rw [secondValue, splicedValue]
    unfold splice Env.get
    simp only [hidden, ↓reduceIte]
  · have notPrivate : ¬ PrivateTo who (setup := setup) (.inl (inputId source)) :=
      fun privateTo => hidden ((privateTo_inl_iff who source).mp privateTo)
    have pairNone : ownerValuePair who firstView secondView (.inl (inputId source)) = none := by
      unfold ownerValuePair
      simp [notPrivate]
    rw [pairNone]
    apply (cast_inj (congrArg EventGraph.EventField.Value layoutEq)).mp
    have firstValue := encodeInputs_get first source
    change cast _ (setup.eventInputs first (inputId source)) = _ at firstValue
    change cast _ (id (setup.eventInputs first (inputId source))) = _
    rw [id, firstValue, splicedValue]
    unfold splice Env.get
    simp only [hidden, ↓reduceIte]

end Vegas
