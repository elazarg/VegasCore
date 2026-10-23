/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.CommitPrefixCompletion

/-! # Exact physical completion at the final commitment of a telescope -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO)

/-- Casting source syntax preserves the physical event at every equal index. -/
theorem OutputEmbedding.event_cast {Γ : SourceCtx Player L} {O : Finset VarId}
    {first second : SourceProgram Player L Γ O} (same : first = second)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) first)
    (left : Fin (eventCount first)) (right : Fin (eventCount second))
    (coordinate : left.val = right.val) :
    embedding.event left = (cast (congrArg (fun program =>
      OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program) same) embedding).event
        right := by
  cases same
  have equal : left = right := Fin.ext coordinate
  subst right
  rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem fieldRef_eq_of_field_eq {Field : Type}
    {layout : Field → EventField Player L} {kind : EventField Player L}
    (first second : FieldRef layout kind) (same : first.field = second.field) : first = second := by
  rcases first with ⟨left, leftLayout⟩
  rcases second with ⟨right, rightLayout⟩
  dsimp only at same
  subst right
  rfl

end Vegas
