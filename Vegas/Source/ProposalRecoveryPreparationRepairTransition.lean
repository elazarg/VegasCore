/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryPreparationRepairStep
import Vegas.Source.CommitRecoveryVirtualHistory

/-! # Actual selective recovery partners through reset and exhaustion -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CommitRecoveryState

/-- The original actual instruction, saved checkpoint and closure branch are
retained together. No survival of the repaired owner is required. -/
theorem FocalRepair.preparation_step {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} {who : Player}
    {original repaired : CommitRecoveryState program}
    (related : FocalRepair who original repaired)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : IsLegalJoint original.Active original.available joint)
    (after : CommitRecoveryState program) (reached : after ∈ (original.step joint).support) :
    ∃ translated : Player → Option (CommitRecoveryMove Player L),
      translated = ProtocolState.repairPreparationRawJoint who program original.point joint ∧
      (∀ observer, observer ≠ who → translated observer = joint observer) ∧
      IsLegalJoint repaired.Active repaired.available translated ∧
      ∃ paired ∈ (repaired.step translated).support,
        FocalRepair who after paired := by
  obtain ⟨result, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  subst after
  have raw : result.1 ∈
      (ProtocolState.recoveryStep program original.point original.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program original.point original.excluded joint)
      (fun value supported => ProtocolState.recoveryStep_excluded_monotone program original.point
        original.excluded joint value supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  obtain ⟨translated, foreign, described, permitted, paired, supported, exclusions, point⟩ :=
    ProtocolState.FocalRepair.preparation_recoveryStep who program original.point repaired.point
      related.point original.excluded joint legal result.1 raw
  have actual : paired ∈
      (ProtocolState.recoveryStep program repaired.point repaired.excluded translated).support := by
    simpa only [related.excluded] using supported
  let monotone := ProtocolState.recoveryStep_excluded_monotone program repaired.point
    repaired.excluded translated paired actual
  have installed : FocalRepair who (original.install result.1 result.2)
      (repaired.install paired monotone) :=
    ⟨point, related.saved, exclusions, related.entryExcluded, related.generation⟩
  refine ⟨translated, described, foreign, ?_, (repaired.install paired monotone).close,
    repaired.step_contains_close translated paired monotone actual, installed.close⟩
  simpa only [IsLegalJoint, Active, available, atPoint, related.excluded] using permitted

end CommitRecoveryState
end Vegas.SourceProgram
