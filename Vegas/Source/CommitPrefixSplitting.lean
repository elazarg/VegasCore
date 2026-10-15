/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryBlockEmbedding

/-! # Typed initial segments of a commitment telescope -/

noncomputable section

namespace Vegas.SourceProgram.CommitPrefix

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- An initial commitment segment leaves the maximal commitment endpoint
determined by its remaining suffix. -/
theorem commitEnd_suffix (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P) (entry : Config Player L Γ)
    (later : Config Player L Δ) :
    ProtocolState.commitEnd (block.prepend suffix)
        (ProtocolState.entry (block.prepend suffix) entry) =
      ProtocolState.commitEnd suffix (ProtocolState.entry suffix later) := by
  simp only [ProtocolState.commitEnd_entry]
  induction block with
  | nil => rfl
  | commit _ _ _ _ _ ih => exact ih suffix (automaticCommit _ _ _ entry) later

/-- Every initial number of commitment instructions is a genuine typed
telescope, followed by the remaining original instructions. -/
theorem exists_split (block : CommitPrefix Γ O Δ P) (count : Nat) (bounded : count ≤ block.length) :
    ∃ (Ξ : SourceCtx Player L) (Q : Finset VarId)
      (earlier : CommitPrefix Γ O Ξ Q) (later : CommitPrefix Ξ Q Δ P),
      earlier.length = count ∧ later.length + count = block.length ∧
        ∀ suffix, earlier.prepend (later.prepend suffix) = block.prepend suffix := by
  induction block generalizing count with
  | nil =>
      have zero : count = 0 := by simpa only [length, Nat.le_zero] using bounded
      subst count
      exact ⟨_, _, .nil, .nil, rfl, rfl, fun _ => rfl⟩
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      cases count with
      | zero => exact ⟨Γ, O, .nil, .commit name owner fresh guard rest, rfl, rfl, fun _ => rfl⟩
      | succ count =>
          have below : count ≤ rest.length := by
            simp only [length] at bounded
            omega
          obtain ⟨Ξ, Q, earlier, later, size, remaining, reconstruct⟩ := ih count below
          refine ⟨Ξ, Q, .commit name owner fresh guard earlier, later, ?_, ?_, ?_⟩
          · simp only [length, size]
          · simp only [length]
            omega
          · intro suffix
            exact congrArg (SourceProgram.commit name owner fresh guard) (reconstruct suffix)

end Vegas.SourceProgram.CommitPrefix
