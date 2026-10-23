/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CompiledRevealPhase

/-! # Determinacy of the actual source disclosure step -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- At the SAME source point and exclusion set, an owned noncommitment step
depends only on its active owner's selected disclosure Boolean. This compares
the actual recovery kernel, retaining failed guards and every hidden cell. -/
theorem publication_source_step_eq :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (excluded : Finset Player) (owner : Player)
      (_acting : ProtocolState.actor program point = some owner)
      (_notCommit : ProtocolState.atCommit program point = false)
      (first second : Player → Option (CommitRecoveryMove Player L)),
      (owner ∉ excluded → OwnAction.disclosure ((first owner).map (·.action)) =
        OwnAction.disclosure ((second owner).map (·.action))) →
      ∀ left ∈ (ProtocolState.recoveryStep program point excluded first).support,
      ∀ right ∈ (ProtocolState.recoveryStep program point excluded second).support,
        left = right
  | _, _, .ret _, _, _, _, acting, _, _, _, _, _, _, _, _ => by cases acting
  | _, _, .sample _ _ _ next, point, excluded, owner, acting, notCommit,
      first, second, same, left, leftSupport, right, rightSupport => by
      cases point with
      | inl config => cases acting
      | inr point =>
          simp only [ProtocolState.recoveryStep, Sum.elim_inr] at leftSupport rightSupport
          obtain ⟨leftResult, leftReached, rfl⟩ := (PMF.mem_support_map_iff
            (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
            (ProtocolState.recoveryStep next point excluded first) left).mp leftSupport
          obtain ⟨rightResult, rightReached, rfl⟩ := (PMF.mem_support_map_iff
            (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
            (ProtocolState.recoveryStep next point excluded second) right).mp rightSupport
          exact congrArg (fun result : ProtocolState next × Finset Player =>
            (Sum.inr result.1, result.2))
              (publication_source_step_eq next point excluded owner acting notCommit first second
                same leftResult leftReached rightResult rightReached)
  | _, _, .commit _ _ _ _ next, point, excluded, owner, acting, notCommit,
      first, second, same, left, leftSupport, right, rightSupport => by
      cases point with
      | inl config => cases notCommit
      | inr point =>
          simp only [ProtocolState.recoveryStep, Sum.elim_inr] at leftSupport rightSupport
          obtain ⟨leftResult, leftReached, rfl⟩ := (PMF.mem_support_map_iff
            (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
            (ProtocolState.recoveryStep next point excluded first) left).mp leftSupport
          obtain ⟨rightResult, rightReached, rfl⟩ := (PMF.mem_support_map_iff
            (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
            (ProtocolState.recoveryStep next point excluded second) right).mp rightSupport
          exact congrArg (fun result : ProtocolState next × Finset Player =>
            (Sum.inr result.1, result.2))
              (publication_source_step_eq next point excluded owner acting notCommit first second
                same leftResult leftReached rightResult rightReached)
  | _, _, .reveal _ author _ _ _ _ next, point, excluded, owner, acting, notCommit,
      first, second, same, left, leftSupport, right, rightSupport => by
      cases point with
      | inl config =>
          have authorEq : author = owner := Option.some.inj acting
          subst author
          by_cases debt : owner ∈ excluded
          · simp only [ProtocolState.recoveryStep, Sum.elim_inl, debt, ↓reduceIte,
              PMF.mem_support_pure_iff] at leftSupport rightSupport
            exact leftSupport.trans rightSupport.symm
          · have disclosure := same debt
            simp only [ProtocolState.recoveryStep, Sum.elim_inl, debt, ↓reduceIte,
              PMF.mem_support_pure_iff] at leftSupport rightSupport
            rw [disclosure] at leftSupport
            exact leftSupport.trans rightSupport.symm
      | inr point =>
          simp only [ProtocolState.recoveryStep, Sum.elim_inr] at leftSupport rightSupport
          obtain ⟨leftResult, leftReached, rfl⟩ := (PMF.mem_support_map_iff
            (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
            (ProtocolState.recoveryStep next point excluded first) left).mp leftSupport
          obtain ⟨rightResult, rightReached, rfl⟩ := (PMF.mem_support_map_iff
            (fun result : ProtocolState next × Finset Player => (Sum.inr result.1, result.2))
            (ProtocolState.recoveryStep next point excluded second) right).mp rightSupport
          exact congrArg (fun result : ProtocolState next × Finset Player =>
            (Sum.inr result.1, result.2))
              (publication_source_step_eq next point excluded owner acting notCommit first second
                same leftResult leftReached rightResult rightReached)

end Vegas
