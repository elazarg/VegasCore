/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitPrefixWord

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

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Every initial number of commitment instructions is a genuine typed
telescope, followed by the remaining original instructions. -/
theorem exists_split (block : CommitPrefix Γ O Δ P) (count : Nat) (bounded : count ≤ block.length) :
    ∃ (Ξ : SourceCtx Player L) (Q : Finset VarId)
      (earlier : CommitPrefix Γ O Ξ Q) (later : CommitPrefix Ξ Q Δ P),
      earlier.length = count ∧ later.length + count = block.length ∧
        earlier.append later = block := by
  induction block generalizing count with
  | nil =>
      have zero : count = 0 := by simpa only [length, Nat.le_zero] using bounded
      subst count
      exact ⟨_, _, .nil, .nil, rfl, rfl, rfl⟩
  | @commit Γ O Δ P name owner payload fresh guard rest ih =>
      cases count with
      | zero => exact ⟨Γ, O, .nil, .commit name owner fresh guard rest, rfl, rfl, rfl⟩
      | succ count =>
          have below : count ≤ rest.length := by
            simp only [length] at bounded
            omega
          obtain ⟨Ξ, Q, earlier, later, size, remaining, reconstruct⟩ := ih count below
          refine ⟨Ξ, Q, .commit name owner fresh guard earlier, later, ?_, ?_, ?_⟩
          · simp only [length, size]
          · simp only [length]
            omega
          · exact congrArg (CommitPrefix.commit name owner fresh guard) reconstruct

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Every interior rank splits the same original commitment telescope just
before its concrete binding instruction. The remaining original instructions
and their names are retained, so the complete source-word prior is unchanged. -/
theorem exists_binding_split (block : CommitPrefix Γ O Δ P) (position : Nat)
    (inside : position < block.length) :
    ∃ (Ξ : SourceCtx Player L) (Q : Finset VarId) (name : VarId) (owner : Player)
      (payload : L.Ty) (fresh : name ∉ Ξ.map Prod.fst)
      (guard : SourceGuard L Ξ owner name payload) (earlier : CommitPrefix Γ O Ξ Q)
      (later : CommitPrefix ((name, .commitment owner payload) :: Ξ) (insert name Q) Δ P),
      earlier.length = position ∧
        earlier.append (.commit name owner fresh guard later) = block := by
  obtain ⟨Ξ, Q, earlier, later, size, remaining, reconstruct⟩ :=
    block.exists_split position (Nat.le_of_lt inside)
  cases later with
  | nil => simp only [length] at remaining; omega
  | commit name owner fresh guard rest =>
    exact ⟨Ξ, Q, name, owner, _, fresh, guard, earlier, rest, size, reconstruct⟩

end Vegas.SourceProgram.CommitPrefix
