/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryNonCommitPath

/-! # Lifting completed noncommitment phases into the whole source program -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability
open CommitRecoveryState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Syntax-derived residual kernel and cursor equations lift a completed
reveal or sample phase to genuine legal transitions of the whole recovery
game. No global source-state map or closure hypothesis is needed. -/
theorem CommitRecoveryState.reaches_of_lifted_nonCommit_path
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (whole : SourceProgram Player L Γ O) (initial : Config Player L Γ)
    (program : SourceProgram Player L Δ P)
    (lift : ProtocolState program → ProtocolState whole)
    (remaining : ∀ point, ProtocolState.remaining whole (lift point) =
      ProtocolState.remaining program point)
    (atCommit : ∀ point, ProtocolState.atCommit whole (lift point) =
      ProtocolState.atCommit program point)
    (step : ∀ point excluded joint,
      ProtocolState.recoveryStep whole (lift point) excluded joint =
        (ProtocolState.recoveryStep program point excluded joint).map
          (fun result => (lift result.1, result.2)))
    (generation : Nat) (first last : ProtocolState program × Finset Player)
    (path : Relation.ReflTransGen
      (fun earlier later : ProtocolState program × Finset Player =>
        ¬ ProtocolState.terminal program earlier.1 ∧
        ProtocolState.atCommit program earlier.1 = false ∧
        ∃ joint, later ∈ (ProtocolState.recoveryStep program earlier.1 earlier.2 joint).support)
      first last) :
    (commitRecoveryProtocol whole initial).Reaches
      (atPoint (lift first.1) first.2 generation) (atPoint (lift last.1) last.2 generation) := by
  have lifted : Relation.ReflTransGen
      (fun earlier later : ProtocolState whole × Finset Player =>
        ¬ ProtocolState.terminal whole earlier.1 ∧
        ProtocolState.atCommit whole earlier.1 = false ∧
        ∃ joint, later ∈ (ProtocolState.recoveryStep whole earlier.1 earlier.2 joint).support)
      (lift first.1, first.2) (lift last.1, last.2) := by
    apply Relation.ReflTransGen.lift
      (fun point : ProtocolState program × Finset Player => (lift point.1, point.2))
      (fun earlier later moved => ?_) first last path
    obtain ⟨running, notCommit, joint, supported⟩ := moved
    refine ⟨?_, ?_, joint, ?_⟩
    · intro stopped
      apply running
      apply (ProtocolState.remaining_zero_iff_terminal program earlier.1).mp
      rw [← remaining earlier.1]
      exact (ProtocolState.remaining_zero_iff_terminal whole (lift earlier.1)).mpr stopped
    · exact (atCommit earlier.1).trans notCommit
    · change (lift later.1, later.2) ∈
        (ProtocolState.recoveryStep whole (lift earlier.1) earlier.2 joint).support
      rw [step]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨later, supported, rfl⟩
  obtain ⟨_states, _joints, _chain, _ending, instructions⟩ :=
    instructions_of_nonCommit_path whole initial generation (fun _ _ moved => moved)
      (lift first.1, first.2) (lift last.1, last.2) lifted
  exact instructions.reaches

end Vegas.SourceProgram
