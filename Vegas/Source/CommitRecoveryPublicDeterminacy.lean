/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryWordObservation

/-! # Genuine source successors determined by their public sample

All strategic instructions are deterministic once the original joint is
fixed. The only Nature branch adds an immutable public sample cell.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- Equal public successors of the SAME raw source state and joint are the
same actual result. The equality retains all hidden cells and obligations. -/
theorem recoveryStep_result_eq_of_public (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program)
      (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L)),
      ∀ l ∈ (recoveryStep program point excluded joint).support,
      ∀ r ∈ (recoveryStep program point excluded joint).support,
        ProtocolView.publicOnly who program (observe who program l.1) =
          ProtocolView.publicOnly who program (observe who program r.1) → l = r
  | _, _, .ret _, _, _, _, l, lm, r, rm, _ => by
      rw [recoveryStep, PMF.mem_support_pure_iff] at lm rm
      exact lm.trans rm.symm
  | _, _, .sample (payload := payload) name _ _ next, point, excluded, joint,
      l, lm, r, rm, after => by
      cases point with
      | inl config =>
          obtain ⟨left, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp lm
          obtain ⟨right, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rm
          have cells := ProtocolView.publicOnly_entry_cells who next _ _ (Sum.inr.inj after)
          have values := congrArg
            (fun view => view.cells name (.publicData payload) .here) cells
          change left = right at values
          subst right
          rfl
      | inr point =>
          obtain ⟨left, leftSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp lm
          obtain ⟨right, rightSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rm
          have equal := recoveryStep_result_eq_of_public who next point excluded joint
            left leftSupport right rightSupport (Sum.inr.inj after)
          exact congrArg (fun result : ProtocolState next × Finset Player =>
            (Sum.inr result.1, result.2)) equal
  | _, _, .commit name owner fresh guard next, point, excluded, joint, l, lm, r, rm, after => by
      cases point with
      | inl config =>
          obtain ⟨result, pure⟩ := recoveryStep_commit_pure
            (.commit name owner fresh guard next) (.inl config) excluded joint rfl
          rw [pure, PMF.mem_support_pure_iff] at lm rm
          exact lm.trans rm.symm
      | inr point =>
          obtain ⟨left, leftSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp lm
          obtain ⟨right, rightSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rm
          have equal := recoveryStep_result_eq_of_public who next point excluded joint
            left leftSupport right rightSupport (Sum.inr.inj after)
          exact congrArg (fun result : ProtocolState next × Finset Player =>
            (Sum.inr result.1, result.2)) equal
  | _, _, .reveal _ _ _ _ _ _ next, point, excluded, joint, l, lm, r, rm, after => by
      cases point with
      | inl config =>
          simp only [recoveryStep, Sum.elim_inl, PMF.mem_support_pure_iff] at lm rm
          exact lm.trans rm.symm
      | inr point =>
          obtain ⟨left, leftSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp lm
          obtain ⟨right, rightSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rm
          have equal := recoveryStep_result_eq_of_public who next point excluded joint
            left leftSupport right rightSupport (Sum.inr.inj after)
          exact congrArg (fun result : ProtocolState next × Finset Player =>
            (Sum.inr result.1, result.2)) equal

end ProtocolState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- The genuine dispatcher introduces no ambiguity after its original joint
and public successor are fixed, including clean/retry/exhausted closure. -/
theorem commitRecovery_step_eq_of_public (who : Player)
    (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (joint : Player → Option (CommitRecoveryMove Player L))
    (left right : CommitRecoveryState setup.program)
    (leftSupport : left ∈ (first.step joint).support)
    (rightSupport : right ∈ (first.step joint).support)
    (same : setup.attemptPublicSignal who (some left) =
      setup.attemptPublicSignal who (some right)) : left = right := by
  by_cases committing : ProtocolState.atCommit setup.program first.point = true
  · exact first.step_unique_of_commit committing joint left right leftSupport rightSupport
  · have notCommit : ProtocolState.atCommit setup.program first.point = false :=
      Bool.eq_false_iff.mpr committing
    obtain ⟨leftRaw, leftRawSupport, rfl⟩ := first.step_noncommit_atPoint
      (setup.commitRecovery_blockFrontier prior) notCommit joint left leftSupport
    obtain ⟨rightRaw, rightRawSupport, rfl⟩ := first.step_noncommit_atPoint
      (setup.commitRecovery_blockFrontier prior) notCommit joint right rightSupport
    have cells : ProtocolView.publicOnly who setup.program
        (ProtocolState.observe who setup.program leftRaw.1) =
      ProtocolView.publicOnly who setup.program
        (ProtocolState.observe who setup.program rightRaw.1) :=
      Option.some.inj (congrArg Prod.fst same)
    exact congrArg (fun result : SourceProgram.ProtocolState setup.program × Finset Player =>
      CommitRecoveryState.atPoint result.1 result.2 first.generation)
        (ProtocolState.recoveryStep_result_eq_of_public who setup.program first.point
          first.excluded joint leftRaw leftRawSupport rightRaw rightRawSupport cells)

end Setup
end Vegas.SourceProgram
