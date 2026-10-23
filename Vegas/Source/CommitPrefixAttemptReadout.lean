/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitPrefixWordRecall
import Vegas.Source.CommitPrefixReadout

/-! # Complete entry-view readback through genuine clear typed attempts -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

variable {Player : Type} [DecidableEq Player] {L : IExpr}
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- A clear typed attempt retains its entire entry view in the original
source backprojection. Nonmissing failed values remain genuine actions. -/
theorem Attempt.entryView_eq (block : CommitPrefix Γ O Δ P)
    (entry : Config Player L Γ) (final : Config Player L Δ)
    (attempt : block.Attempt entry ∅ final ∅) (who : Player) :
    block.entryView who (final.view who) = entry.view who := by
  induction block with
  | nil => cases attempt; rfl
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
    obtain ⟨result, ⟨tail⟩⟩ := attempt.clear_tail
    change (rest.entryView who (final.view who)).back (decide (owner = who)) = _
    rw [ih _ _ tail]
    exact back_commit_view who name guard entry result

end Vegas.SourceProgram.CommitPrefix
