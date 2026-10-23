/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProtocolSuffix

/-! # Intended typed commitment completions in the whole source program -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- Any actual typed attempt preserves every cell that existed at its entry. -/
theorem Attempt.base_liftPoint {block : CommitPrefix Γ O Δ P} {entry : Config Player L Γ}
    {excluded : Finset Player} {finished : Config Player L Δ} {after : Finset Player}
    (attempt : block.Attempt entry excluded finished after) (suffix : SourceProgram Player L Δ P) :
    ProtocolState.base (block.prepend suffix)
      (block.liftPoint suffix (ProtocolState.entry suffix finished)) = entry.state := by
  induction attempt with
  | nil => exact ProtocolState.base_entry suffix _
  | active _ choice _ _ _later ih =>
      change (fun _ _ cell => (ProtocolState.base _ _).get (.there cell)) = _
      rw [ih suffix]
      rfl
  | excluded _ _later ih =>
      change (fun _ _ cell => (ProtocolState.base _ _).get (.there cell)) = _
      rw [ih suffix]
      rfl

/-- Traversing only commitments adds no already-processed reveal obligation. -/
theorem intended_liftPoint (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (point : ProtocolState suffix) (intended : ProtocolState.Intended suffix point) :
    ProtocolState.Intended (block.prepend suffix) (block.liftPoint suffix point) := by
  induction block with
  | nil => exact intended
  | commit _ _ _ _ _rest ih => exact ih suffix point intended

/-- Guard-admitted completion of the residual prefix lifts to an intended
whole source point. The saved reference supplies prior publication success;
the actual typed attempt preserves precisely those old entry cells. -/
theorem Attempt.intended_lift {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO)
    {block : CommitPrefix Γ O Δ P} {entry : Config Player L Γ}
    {excluded : Finset Player} {finished : Config Player L Δ} {after : Finset Player}
    (attempt : block.Attempt entry excluded finished after) (suffix : SourceProgram Player L Δ P)
    (lift : ProtocolState (block.prepend suffix) → ProtocolState whole)
    (origin : ProtocolSuffix whole (block.prepend suffix) lift)
    (reference : ProtocolState.Intended whole
      (lift (ProtocolState.entry (block.prepend suffix) entry)))
    (intended : ProtocolState.Intended suffix (ProtocolState.entry suffix finished)) :
    ProtocolState.Intended whole
      (lift (block.liftPoint suffix (ProtocolState.entry suffix finished))) := by
  apply origin.intended_of_base_eq (ProtocolState.entry (block.prepend suffix) entry)
    (block.liftPoint suffix (ProtocolState.entry suffix finished)) reference
    (block.intended_liftPoint suffix _ intended)
  rw [ProtocolState.base_entry]
  exact attempt.base_liftPoint suffix

end Vegas.SourceProgram.CommitPrefix
