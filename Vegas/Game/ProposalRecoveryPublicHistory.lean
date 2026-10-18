/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryProjection
import Vegas.Game.CommitRecoveryGlobalWordDensity

/-! # Full public source chronology with truthful proposal deltas -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

def proposalRecoveryPublicRecall (who : Player) :
    ∀ {state : setup.proposalRecoveryProtocol.State},
    setup.proposalRecoveryProtocol.Trace state →
      List ((setup.ProtocolView who × (Finset Player × Nat × Nat)) ×
        Option (ProposalRecoveryProposal L))
  | _, .start => [(setup.attemptPublicSignal who setup.commitRecoveryProtocol.init, none)]
  | after, @Trace.extend _ _ before _ prior joint _ _ =>
      (setup.attemptPublicSignal who after,
        setup.proposalRecoveryProposalOf before joint) :: proposalRecoveryPublicRecall who prior

theorem proposalRecoveryPublicRecall_semantic (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryPublicRecall who trace).map Prod.fst =
      setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace trace) := by
  induction trace with
  | start => rfl
  | extend prior joint legal supported ih =>
      simp only [proposalRecoveryPublicRecall, List.map_cons, proposalRecoveryEraseTrace,
        setup.publicRecall_extend, ih]

theorem proposalRecoveryPublicRecall_length (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryPublicRecall who trace).length = trace.length + 1 := by
  have projected := congrArg List.length (setup.proposalRecoveryPublicRecall_semantic who trace)
  simpa only [List.length_map, setup.publicRecall_length,
    setup.proposalRecoveryEraseTrace_length] using projected

theorem proposalRecoveryPublicRecall_semantic_eq (who : Player)
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (left : setup.proposalRecoveryProtocol.Trace leftState)
    (right : setup.proposalRecoveryProtocol.Trace rightState)
    (same : setup.proposalRecoveryPublicRecall who left =
      setup.proposalRecoveryPublicRecall who right) :
    setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace left) =
      setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace right) := by
  rw [← setup.proposalRecoveryPublicRecall_semantic, ← setup.proposalRecoveryPublicRecall_semantic]
  exact congrArg (List.map Prod.fst) same

theorem proposalRecovery_information_extend_congr (who : Player)
    {leftSource leftTarget rightSource rightTarget : setup.proposalRecoveryProtocol.State}
    (left : setup.proposalRecoveryProtocol.Trace leftSource)
    (right : setup.proposalRecoveryProtocol.Trace rightSource)
    (leftJoint rightJoint : Player → Option (ProposalRecoveryMove Player L))
    (leftLegal : setup.proposalRecoveryProtocol.Legal leftSource leftJoint)
    (rightLegal : setup.proposalRecoveryProtocol.Legal rightSource rightJoint)
    (leftSupport : leftTarget ∈
      (setup.proposalRecoveryProtocol.step leftSource ⟨leftJoint, leftLegal⟩).support)
    (rightSupport : rightTarget ∈
      (setup.proposalRecoveryProtocol.step rightSource ⟨rightJoint, rightLegal⟩).support)
    (before : setup.proposalRecoveryModel.infoOf who left =
      setup.proposalRecoveryModel.infoOf who right)
    (ownChoice : leftJoint who = rightJoint who)
    (signal : (setup.commitRecoveryPrivate who leftTarget,
        (setup.commitRecoveryPublic leftTarget,
          setup.proposalRecoveryProposalOf leftSource leftJoint)) =
      (setup.commitRecoveryPrivate who rightTarget,
        (setup.commitRecoveryPublic rightTarget,
          setup.proposalRecoveryProposalOf rightSource rightJoint))) :
    setup.proposalRecoveryModel.infoOf who (left.extend leftJoint leftLegal leftSupport) =
      setup.proposalRecoveryModel.infoOf who (right.extend rightJoint rightLegal rightSupport) := by
  change setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who _ =
    setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who _
  change setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who left =
    setup.proposalRecoverySignals.withOwnPlayRecall.infoOf who right at before
  rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf] at before ⊢
  have base := congrArg Prod.fst before
  have record := congrArg Prod.snd before
  dsimp only at base record
  apply Prod.ext
  · rw [InfoSignals.infoOf_extend, InfoSignals.infoOf_extend]
    change ((setup.commitRecoveryPrivate who leftTarget,
      (setup.commitRecoveryPublic leftTarget,
        setup.proposalRecoveryProposalOf leftSource leftJoint)), _) =
      ((setup.commitRecoveryPrivate who rightTarget,
        (setup.commitRecoveryPublic rightTarget,
          setup.proposalRecoveryProposalOf rightSource rightJoint)), _)
    rw [signal, base]
  · rw [InfoSignals.ownPlay_extend, InfoSignals.ownPlay_extend, ownChoice]
    cases rightJoint who with
    | none => exact record
    | some action => exact congrArg₂ List.cons (congrArg (fun info => (info, action)) base) record

end Vegas.SourceProgram.Setup
