/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryClearSuccessor
import Vegas.Source.CommitRecoveryInformation
import Vegas.Source.SetupObservationRecall
import Vegas.Source.SetupProtocolRecall
import Vegas.Source.CommitBlockRecovery

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

/-- A legal move on a clear transition cannot carry a physical omission. -/
theorem commitRecovery_clear_joint_lift
    {before after : setup.commitRecoveryProtocol.State}
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal before joint)
    (supported : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support)
    (clear : setup.CommitRecoveryClear after) (who : Player) :
    joint who = CommitRecoveryMove.lift ((joint who).map (·.action)) := by
  cases before with
  | none =>
      have offered := legal.2 who
      cases chosen : joint who with
      | none => rfl
      | some move => rw [chosen] at offered; exact offered.1.elim
  | some current =>
      obtain ⟨next, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      have offered := legal.2 who
      cases chosen : joint who with
      | none => rfl
      | some move =>
          rw [chosen] at offered
          have menu : move ∈ current.available who := offered.2
          have noMiss : move.missing = false := by
            by_cases active : ProtocolState.atCommit setup.program current.point = true
            · cases missing : move.missing with
              | false => rfl
              | true =>
                  have excluded := current.missed_excludes who joint active offered.1.1
                    (by simp only [chosen, CommitRecoveryMove.missed, Option.elim_some, missing])
                    next reached
                  change next.excluded = ∅ at clear
                  rw [clear] at excluded
                  exact (Finset.notMem_empty who excluded).elim
            · have notCommit : ProtocolState.atCommit setup.program current.point = false :=
                Bool.eq_false_iff.mpr active
              simpa only [CommitRecoveryState.available, ProtocolView.recoveryAvailable,
                Set.mem_ofPred_eq, ProtocolState.atCommit_observe, notCommit,
                Bool.false_eq_true, ↓reduceIte] using menu.2
          simp only [CommitRecoveryMove.lift, Option.map_some]
          cases move
          simp_all

/-- Complete own-play recall is also determined by the current private view
along arbitrary legal clear recovery histories, including latent bad bindings. -/
theorem commitRecovery_clear_ownPlay_eq (who : Player) :
    ∀ {first second : setup.commitRecoveryProtocol.State}
      (firstTrace : setup.commitRecoveryProtocol.Trace first)
      (secondTrace : setup.commitRecoveryProtocol.Trace second)
      (_firstClear : setup.CommitRecoveryClear first)
      (_secondClear : setup.CommitRecoveryClear second),
      setup.commitRecoveryPrivate who first = setup.commitRecoveryPrivate who second →
        setup.commitRecoverySignals.ownPlay who firstTrace =
          setup.commitRecoverySignals.ownPlay who secondTrace
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
  | _, _, .extend firstPrior firstJoint firstLegal firstSupported,
      .extend secondPrior secondJoint secondLegal secondSupported, firstClear, secondClear,
      same => by
      have firstBefore := setup.commitRecoveryClear_before
        ⟨firstJoint, firstLegal⟩ firstSupported firstClear
      have secondBefore := setup.commitRecoveryClear_before
        ⟨secondJoint, secondLegal⟩ secondSupported secondClear
      have before := setup.commitRecovery_clear_predecessor_private who firstPrior secondPrior
        firstJoint secondJoint firstLegal secondLegal firstSupported secondSupported
        firstClear secondClear same
      have earlier := commitRecovery_clear_ownPlay_eq who firstPrior secondPrior
        firstBefore secondBefore before
      have signals := setup.commitRecovery_clear_signals_eq who firstPrior secondPrior
        firstBefore secondBefore before
      have projected := setup.protocol_perfectRecall
        (CommitmentInterface.forfeiture setup.program) who
        (setup.commitRecoveryClearTrace (firstPrior.extend firstJoint firstLegal firstSupported)
          firstClear)
        (setup.commitRecoveryClearTrace (secondPrior.extend secondJoint secondLegal secondSupported)
          secondClear)
        (by rw [setup.commitRecoveryClearTrace_observe, setup.commitRecoveryClearTrace_observe];
            exact same)
      change (setup.protocolSignals _).ownPlay who _ =
        (setup.protocolSignals _).ownPlay who _ at projected
      simp only [commitRecoveryClearTrace, InfoSignals.ownPlay_extend] at projected
      have sourcePrior : (setup.protocolSignals _).ownPlay who
          (setup.commitRecoveryClearTrace firstPrior firstBefore) =
          (setup.protocolSignals _).ownPlay who
            (setup.commitRecoveryClearTrace secondPrior secondBefore) := by
        rw [setup.protocol_ownPlay, setup.protocol_ownPlay,
          ← setup.commitRecoveryPrivate_source, ← setup.commitRecoveryPrivate_source, before]
      rw [sourcePrior] at projected
      have underlying : (firstJoint who).map (·.action) = (secondJoint who).map (·.action) := by
        cases firstChosen : firstJoint who with
        | none =>
            cases secondChosen : secondJoint who with
            | none => rfl
            | some move =>
                have lengths := congrArg List.length projected
                simp only [CommitRecoveryMove.underlying, firstChosen, secondChosen,
                  Option.map_none, Option.map_some, List.length_cons] at lengths
                omega
        | some firstMove =>
            cases secondChosen : secondJoint who with
            | none =>
                have lengths := congrArg List.length projected
                simp only [CommitRecoveryMove.underlying, firstChosen, secondChosen,
                  Option.map_none, Option.map_some, List.length_cons] at lengths
                omega
            | some secondMove =>
                simp only [CommitRecoveryMove.underlying, firstChosen, secondChosen,
                  Option.map_some] at projected
                exact congrArg some (congrArg Prod.snd (List.cons.inj projected).1)
      have jointEq : firstJoint who = secondJoint who :=
        Eq.trans
          (setup.commitRecovery_clear_joint_lift firstJoint firstLegal firstSupported
            firstClear who)
          ((congrArg CommitRecoveryMove.lift underlying).trans
            (setup.commitRecovery_clear_joint_lift secondJoint secondLegal secondSupported
              secondClear who).symm)
      simp only [InfoSignals.ownPlay_extend]
      rw [signals, earlier, jointEq]

/-- A clear source recovery history carries no additional information beyond
its current source view, including the full transcript and own-action recall. -/
theorem commitRecovery_clear_info_eq (who : Player)
    {first second : setup.commitRecoveryProtocol.State}
    (firstTrace : setup.commitRecoveryProtocol.Trace first)
    (secondTrace : setup.commitRecoveryProtocol.Trace second)
    (firstClear : setup.CommitRecoveryClear first)
    (secondClear : setup.CommitRecoveryClear second)
    (same : setup.commitRecoveryPrivate who first = setup.commitRecoveryPrivate who second) :
    setup.commitRecoveryModel.infoOf who firstTrace =
      setup.commitRecoveryModel.infoOf who secondTrace := by
  change setup.commitRecoverySignals.withOwnPlayRecall.infoOf who firstTrace =
    setup.commitRecoverySignals.withOwnPlayRecall.infoOf who secondTrace
  rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf]
  exact Prod.ext
    (setup.commitRecovery_clear_signals_eq who firstTrace secondTrace firstClear secondClear same)
    (setup.commitRecovery_clear_ownPlay_eq who firstTrace secondTrace firstClear secondClear same)

end Vegas.SourceProgram.Setup
