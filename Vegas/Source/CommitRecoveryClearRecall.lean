/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryClearSuccessor
import Vegas.Source.SetupObservationRecall

/-! # Complete information along arbitrary clear source recovery histories -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

theorem commitRecoveryClearTrace_length_eq_of_private (who : Player)
    {first second : setup.commitRecoveryProtocol.State}
    (firstTrace : setup.commitRecoveryProtocol.Trace first)
    (secondTrace : setup.commitRecoveryProtocol.Trace second)
    (firstClear : setup.CommitRecoveryClear first)
    (secondClear : setup.CommitRecoveryClear second)
    (same : setup.commitRecoveryPrivate who first = setup.commitRecoveryPrivate who second) :
    firstTrace.length = secondTrace.length := by
  have firstCount := setup.protocol_history_length
    (CommitmentInterface.forfeiture setup.program)
    (setup.commitRecoveryClearTrace firstTrace firstClear)
  have secondCount := setup.protocol_history_length
    (CommitmentInterface.forfeiture setup.program)
    (setup.commitRecoveryClearTrace secondTrace secondClear)
  have remaining := setup.protocolRemaining_eq_of_observe who _ _
    ((setup.commitRecoveryPrivate_source who first).symm.trans
      (same.trans (setup.commitRecoveryPrivate_source who second)))
  rw [setup.commitRecoveryClearTrace_length] at firstCount secondCount
  omega

theorem commitRecovery_clear_predecessor_private (who : Player)
    {first second firstAfter secondAfter : setup.commitRecoveryProtocol.State}
    (firstTrace : setup.commitRecoveryProtocol.Trace first)
    (secondTrace : setup.commitRecoveryProtocol.Trace second)
    (firstJoint secondJoint : Player → Option (CommitRecoveryMove Player L))
    (firstLegal : setup.commitRecoveryProtocol.Legal first firstJoint)
    (secondLegal : setup.commitRecoveryProtocol.Legal second secondJoint)
    (firstSupported : firstAfter ∈
      (setup.commitRecoveryProtocol.step first ⟨firstJoint, firstLegal⟩).support)
    (secondSupported : secondAfter ∈
      (setup.commitRecoveryProtocol.step second ⟨secondJoint, secondLegal⟩).support)
    (firstClear : setup.CommitRecoveryClear firstAfter)
    (secondClear : setup.CommitRecoveryClear secondAfter)
    (same : setup.commitRecoveryPrivate who firstAfter =
      setup.commitRecoveryPrivate who secondAfter) :
    setup.commitRecoveryPrivate who first = setup.commitRecoveryPrivate who second := by
  have lengths := setup.commitRecoveryClearTrace_length_eq_of_private who
    (firstTrace.extend firstJoint firstLegal firstSupported)
    (secondTrace.extend secondJoint secondLegal secondSupported) firstClear secondClear same
  simp only [Trace.length, Nat.add_right_cancel_iff] at lengths
  have left := setup.protocol_recover_predecessor
    (CommitmentInterface.forfeiture setup.program) who
    (setup.commitRecoveryClearTrace firstTrace
      (setup.commitRecoveryClear_before ⟨firstJoint, firstLegal⟩ firstSupported firstClear))
    (fun actor => (firstJoint actor).map (·.action))
    (setup.commitRecovery_source_step ⟨firstJoint, firstLegal⟩ firstSupported firstClear)
  have right := setup.protocol_recover_predecessor
    (CommitmentInterface.forfeiture setup.program) who
    (setup.commitRecoveryClearTrace secondTrace
      (setup.commitRecoveryClear_before ⟨secondJoint, secondLegal⟩ secondSupported secondClear))
    (fun actor => (secondJoint actor).map (·.action))
    (setup.commitRecovery_source_step ⟨secondJoint, secondLegal⟩ secondSupported secondClear)
  simp only [setup.commitRecoveryClearTrace_length,
    ← setup.commitRecoveryPrivate_source] at left right
  rw [lengths, same] at left
  exact Option.some.inj (left.symm.trans right)

/-- The current private source view determines the complete observed recovery
transcript whenever neither legal history has excluded a player. -/
theorem commitRecovery_clear_signals_eq (who : Player) :
    ∀ {first second : setup.commitRecoveryProtocol.State}
      (firstTrace : setup.commitRecoveryProtocol.Trace first)
      (secondTrace : setup.commitRecoveryProtocol.Trace second)
      (_firstClear : setup.CommitRecoveryClear first)
      (_secondClear : setup.CommitRecoveryClear second),
      setup.commitRecoveryPrivate who first = setup.commitRecoveryPrivate who second →
        setup.commitRecoverySignals.infoOf who firstTrace =
          setup.commitRecoverySignals.infoOf who secondTrace
  | _, _, .start, .start, _, _, _ => rfl
  | _, _, .start, .extend prior joint legal supported, firstClear, secondClear, same => by
      have lengths := setup.commitRecoveryClearTrace_length_eq_of_private who .start
        (prior.extend joint legal supported) firstClear secondClear same
      simp only [Trace.length] at lengths
      omega
  | _, _, .extend prior joint legal supported, .start, firstClear, secondClear, same => by
      have lengths := setup.commitRecoveryClearTrace_length_eq_of_private who
        (prior.extend joint legal supported) .start firstClear secondClear same
      simp only [Trace.length] at lengths
      omega
  | firstAfter, secondAfter, .extend firstPrior firstJoint firstLegal firstSupported,
      .extend secondPrior secondJoint secondLegal secondSupported, firstClear, secondClear,
      same => by
      have firstBefore := setup.commitRecoveryClear_before
        ⟨firstJoint, firstLegal⟩ firstSupported firstClear
      have secondBefore := setup.commitRecoveryClear_before
        ⟨secondJoint, secondLegal⟩ secondSupported secondClear
      have before := setup.commitRecovery_clear_predecessor_private who firstPrior secondPrior
        firstJoint secondJoint firstLegal secondLegal firstSupported secondSupported
        firstClear secondClear same
      have earlier := commitRecovery_clear_signals_eq who firstPrior secondPrior
        firstBefore secondBefore before
      have current := congrArg Prod.fst earlier
      rw [setup.commitRecoverySignals_current, setup.commitRecoverySignals_current] at current
      have sourceSame := (setup.commitRecoveryPrivate_source who firstAfter).symm.trans
        (same.trans (setup.commitRecoveryPrivate_source who secondAfter))
      have publicView := setup.commitRecoveryLiftSuccessor_public who _ _
        firstBefore secondBefore before (congrArg Prod.snd current) _ _ sourceSame
      have firstReconstruct := setup.commitRecovery_clear_step_reconstruct
        ⟨firstJoint, firstLegal⟩ firstSupported firstClear
      have secondReconstruct := setup.commitRecovery_clear_step_reconstruct
        ⟨secondJoint, secondLegal⟩ secondSupported secondClear
      have publicSame : setup.commitRecoveryPublic firstAfter =
          setup.commitRecoveryPublic secondAfter :=
        (congrArg setup.commitRecoveryPublic firstReconstruct).trans
          (publicView.trans (congrArg setup.commitRecoveryPublic secondReconstruct).symm)
      change ((setup.commitRecoveryPrivate who firstAfter, setup.commitRecoveryPublic firstAfter),
        (setup.commitRecoverySignals.infoOf who firstPrior).1 ::
          (setup.commitRecoverySignals.infoOf who firstPrior).2) =
        ((setup.commitRecoveryPrivate who secondAfter, setup.commitRecoveryPublic secondAfter),
        (setup.commitRecoverySignals.infoOf who secondPrior).1 ::
          (setup.commitRecoverySignals.infoOf who secondPrior).2)
      rw [same, publicSame, earlier]

end Vegas.SourceProgram.Setup
