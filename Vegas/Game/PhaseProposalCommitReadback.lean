/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledCommitHead

/-! # The same decoded attempt retains an admitted ordinary draw

This scalar identity attaches a previously emitted and admitted value to the
existing source-ranked decoder. It does not choose a second source attempt.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO) (mode : ExecutionMode)

/-- Actual admission and the retained typed candidate meaning identify the
literal source joint in the existing head of the SAME decoded attempt. Both
facts are native table facts; no source choice or desired kernel is assumed. -/
theorem decodeCommitAttempt_head_joints_of_typed_admission
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (tail : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.commit name owner fresh guard tail))
    (native : EventGraphRuntime.State ((toEventGraph whole).withMode mode))
    (entry : SourceProgram.Config Player L Γ) (source : CommitRecoveryState whole)
    (candidate : Handle ((toEventGraph whole).withMode mode)) (value : L.Val payload)
    (admitted : native.accepted
      (.inr (embedding.event ⟨0, by simp only [eventCount]; omega⟩)) = some candidate)
    (meaning : native.bindingResult candidate payload = .success value) :
    let head : SourceProgram.CommitPrefix Γ O ((name, .commitment owner payload) :: Γ)
      (insert name O) := .commit name owner fresh guard .nil
    (decodeCommitAttempt whole mode head tail embedding native entry source.excluded).2.2.joints =
      [source.commitJoint owner name payload (.success value) false] := by
  dsimp only
  rw [decodeCommitAttempt_head_joints whole mode fresh guard tail embedding native entry source]
  simp only [admitted, Option.elim_some, Option.isNone_some, meaning]

end Vegas
