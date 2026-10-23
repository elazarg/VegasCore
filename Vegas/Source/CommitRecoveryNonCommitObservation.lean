/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryFrontier

/-! # Observable public successors of noncommitment recovery instructions -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]


namespace CommitRecoveryState

/-- An actual noncommitment step installs its result directly, without retry. -/
theorem step_noncommit_atPoint {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} (state : CommitRecoveryState program)
    (frontier : state.BlockFrontier)
    (notCommit : ProtocolState.atCommit program state.point = false)
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (reached : next ∈ (state.step joint).support) :
    ∃ result ∈ (ProtocolState.recoveryStep program state.point state.excluded joint).support,
      next = atPoint result.1 result.2 state.generation := by
  obtain ⟨result, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  let law := ProtocolState.recoveryStep program state.point state.excluded joint
  let keep := fun value (member : value ∈ law.support) =>
    ProtocolState.recoveryStep_excluded_monotone program state.point state.excluded joint
      value member
  have raw : result.1 ∈ law.support := by
    rw [← map_val_pmfToSubtype law keep]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, supported, rfl⟩
  have saved : ProtocolState.atCommit program state.saved = false := by
    rw [frontier.saved_eq_point_of_not_atCommit notCommit, notCommit]
  refine ⟨result.1, raw, ?_⟩
  simp only [close, Finished, install, saved, Bool.false_eq_true, false_and, ↓reduceIte]

end CommitRecoveryState
end Vegas.SourceProgram
