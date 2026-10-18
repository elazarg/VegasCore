/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryNonCommitPath
import Vegas.Source.CommitRecoveryDeviation
import Vegas.Source.CommitRecoveryClear
import Vegas.Source.ProtocolSuffix
import Vegas.Source.CommitRecoveryDebt

/-! # Intended source states along clear noncommitment recovery paths -/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}

/-- A sample or disclosure step ending clear cannot leave the intended game.
Actual recovery legality is derived by the existing noncommitment legalization. -/
theorem recoveryStep_intended_of_clear_nonCommit
    (program : SourceProgram Player L Γ O) (point target : ProtocolState program)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (intended : Intended program point) (notCommit : atCommit program point = false)
    (supported : (target, ∅) ∈ (recoveryStep program point ∅ joint).support) :
    Intended program target := by
  obtain ⟨legalJoint, legal, same, _disclosure⟩ :=
    recoveryStep_legalize_nonCommit program point ∅ joint notCommit
  have member : (target, ∅) ∈ (recoveryStep program point ∅ legalJoint).support := by
    rw [same]
    exact supported
  have projected : target ∈ (step program point
      (fun who => (legalJoint who).map (·.action))).support := by
    rw [← recoveryStep_empty_point]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(target, ∅), member, rfl⟩
  apply intended_step_of_actors program point _ target intended _ projected
  intro who acting
  have actualActing := (actor_observe_eq program point who).symm.trans acting
  have offered := legal who
  cases chosen : legalJoint who with
  | none =>
      rw [chosen] at offered
      exact (offered ⟨actualActing, Finset.notMem_empty who⟩).elim
  | some move =>
      rw [chosen] at offered
      refine ⟨move.action, rfl, ?_⟩
      by_contra extra
      rcases recoveryStep_deviation who program point intended legalJoint move chosen
          actualActing offered.2 (Or.inr extra) (target, ∅) member with excluded | binding
      · exact Finset.notMem_empty who excluded
      · rw [notCommit] at binding
        cases binding.1

/-- Final clarity forces clarity at every preceding noncommitment step, so
an actual source-ordered sample/disclosure path preserves whole intendedness. -/
theorem intended_of_clear_nonCommit_path
    (program : SourceProgram Player L Γ O)
    (first last : ProtocolState program × Finset Player)
    (path : Relation.ReflTransGen
      (fun earlier later : ProtocolState program × Finset Player =>
        ¬ terminal program earlier.1 ∧ atCommit program earlier.1 = false ∧
        ∃ joint, later ∈ (recoveryStep program earlier.1 earlier.2 joint).support)
      first last)
    (intended : Intended program first.1) (finalClear : last.2 = ∅) :
    Intended program last.1 := by
  induction path with
  | refl => exact intended
  | @tail before after _ edge ih =>
      obtain ⟨_running, notCommit, joint, supported⟩ := edge
      have priorClear : before.2 = ∅ := by
        apply Finset.subset_empty.mp
        rw [← finalClear]
        exact recoveryStep_excluded_monotone program before.1 before.2 joint after supported
      have priorIntended := ih priorClear
      rw [priorClear] at supported
      have same : after = (after.1, ∅) := Prod.ext rfl finalClear
      rw [same] at supported
      exact recoveryStep_intended_of_clear_nonCommit program before.1 after.1 joint
        priorIntended notCommit supported

end Vegas.SourceProgram.ProtocolState

namespace Vegas.SourceProgram.ProtocolSuffix

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
  {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
  {lift : ProtocolState program → ProtocolState whole}

/-- The unchanged old entry cells retain all earlier successful publications
when a genuine residual sample/disclosure path ends without exclusions. -/
theorem intended_of_clear_nonCommit_path (origin : ProtocolSuffix whole program lift)
    (first last : ProtocolState program × Finset Player)
    (path : Relation.ReflTransGen
      (fun earlier later : ProtocolState program × Finset Player =>
        ¬ ProtocolState.terminal program earlier.1 ∧
        ProtocolState.atCommit program earlier.1 = false ∧
        ∃ joint, later ∈ (ProtocolState.recoveryStep program earlier.1 earlier.2 joint).support)
      first last)
    (intended : ProtocolState.Intended whole (lift first.1)) (finalClear : last.2 = ∅) :
    ProtocolState.Intended whole (lift last.1) := by
  apply origin.intended_of_base_eq first.1 last.1 intended
    (ProtocolState.intended_of_clear_nonCommit_path program first last path
      (origin.intended_reflect first.1 intended) finalClear)
  clear finalClear
  induction path with
  | refl => rfl
  | @tail before after _ edge ih =>
      obtain ⟨_running, _notCommit, joint, supported⟩ := edge
      exact (ProtocolState.base_recoveryStep program before.1 before.2 joint after
        supported).trans ih

end Vegas.SourceProgram.ProtocolSuffix
