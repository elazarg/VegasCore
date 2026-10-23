/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryPerturbation

/-! # Actual neutral omission kernels on archive-refined information -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
theorem proposalRecoveryEraseInfo_current (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryEraseInfo who
      (setup.proposalRecoveryModel.infoOf who trace)).1.1 =
        (setup.commitRecoveryPrivate who state, setup.commitRecoveryPublic state) := by
  rw [setup.proposalRecoveryEraseInfo_observed]
  change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who
    (setup.proposalRecoveryEraseTrace trace)).1.1 = _
  rw [InfoSignals.withOwnPlayRecall_infoOf, setup.commitRecoverySignals_current]

/-- The existing behavioral joint law is the independent product of its
actual information-local omission marginals. Proposal labels are retained
by the policy and erased only by this explicit marginal. -/
theorem proposalRecovery_joint_missed_law
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (history : setup.proposalRecoveryProtocol.History)
    (running : ¬ setup.proposalRecoveryProtocol.terminal history.state) :
    (setup.proposalRecoveryModel.behavioralJoint profile history.trace running).map
        (fun draw who => CommitRecoveryMove.missed ((draw.val who).map (·.semantic))) =
      independentProduct (fun who =>
        (profile who (setup.proposalRecoveryModel.infoOf who history.trace)).map
          (fun choice => CommitRecoveryMove.missed (choice.val.map (·.semantic)))) := by
  calc
    _ = ((setup.proposalRecoveryModel.behavioralJoint profile history.trace running).map
      Subtype.val).map
        (fun joint who => CommitRecoveryMove.missed ((joint who).map (·.semantic))) := by
          rw [PMF.map_comp]
          rfl
    _ = _ := by
      rw [setup.proposalRecoveryModel.behavioralJoint_map_val]
      have product := independentProduct_map
        (μ := fun who => (profile who
          (setup.proposalRecoveryModel.infoOf who history.trace)).map Subtype.val)
        (f := fun who (choice : Option (setup.proposalRecoveryProtocol.Action who)) =>
          CommitRecoveryMove.missed
            (choice.map (fun move : ProposalRecoveryMove Player L => move.semantic)))
      simp only [PMF.map_comp, Function.comp_def] at product
      convert product using 1 <;> rfl

/-- On actual commitment controls, the omission joint depends only on the
current actor and exclusions. Ordinary domains may read different archives
and all hidden source values may differ. -/
theorem proposalRecoveryNormalizedTrembledProfile_joint_missed_eq
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (delivery : ℝ) (deliveryNonnegative : 0 ≤ delivery) (deliveryBounded : delivery ≤ 1)
    (leftValues rightValues : (who : Player) → (key : setup.ProposalRecoveryComponent who) →
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (left right : CommitRecoveryState setup.program)
    (leftTrace : setup.proposalRecoveryProtocol.Trace (some left))
    (rightTrace : setup.proposalRecoveryProtocol.Trace (some right))
    (leftRunning : ¬ setup.proposalRecoveryProtocol.terminal (some left))
    (rightRunning : ¬ setup.proposalRecoveryProtocol.terminal (some right))
    (leftCommit : ProtocolState.atCommit setup.program left.point = true)
    (rightCommit : ProtocolState.atCommit setup.program right.point = true)
    (excluded : left.excluded = right.excluded)
    (actor : ProtocolState.actor setup.program left.point =
      ProtocolState.actor setup.program right.point) :
    (setup.proposalRecoveryModel.behavioralJoint
      (setup.proposalRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded delivery deliveryNonnegative deliveryBounded leftValues)
          leftTrace leftRunning).map
        (fun draw who => CommitRecoveryMove.missed ((draw.val who).map (·.semantic))) =
      (setup.proposalRecoveryModel.behavioralJoint
        (setup.proposalRecoveryNormalizedTrembledProfile omission omissionNonnegative
          omissionBounded bad badNonnegative badBounded
          delivery deliveryNonnegative deliveryBounded rightValues) rightTrace rightRunning).map
          (fun draw who => CommitRecoveryMove.missed ((draw.val who).map (·.semantic))) := by
  classical
  have leftMarginal := setup.proposalRecovery_joint_missed_law
    (setup.proposalRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded delivery deliveryNonnegative deliveryBounded leftValues)
    ⟨some left, leftTrace⟩ leftRunning
  have rightMarginal := setup.proposalRecovery_joint_missed_law
    (setup.proposalRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded delivery deliveryNonnegative deliveryBounded rightValues)
    ⟨some right, rightTrace⟩ rightRunning
  apply leftMarginal.trans
  refine Eq.trans ?_ rightMarginal.symm
  apply congrArg independentProduct
  funext who
  have active : setup.proposalRecoveryActive who
      (setup.proposalRecoveryModel.infoOf who leftTrace).1.1 ↔
        setup.proposalRecoveryActive who
          (setup.proposalRecoveryModel.infoOf who rightTrace).1.1 := by
    change setup.commitRecoveryActive who
        (setup.proposalRecoveryEraseInfo who
          (setup.proposalRecoveryModel.infoOf who leftTrace)).1.1 ↔
      setup.commitRecoveryActive who
        (setup.proposalRecoveryEraseInfo who
          (setup.proposalRecoveryModel.infoOf who rightTrace)).1.1
    rw [setup.proposalRecoveryEraseInfo_current, setup.proposalRecoveryEraseInfo_current]
    simp only [commitRecoveryActive, commitRecoveryPrivate, Option.map_some, Option.elim_some,
      ProtocolState.actor_observe_eq, commitRecoveryPublic, actor, excluded]
  have leftIsCommit : (setup.proposalRecoveryModel.infoOf who leftTrace).1.1.1.elim false
      (ProtocolView.atCommit who setup.program) = true := by
    change (setup.proposalRecoveryEraseInfo who
      (setup.proposalRecoveryModel.infoOf who leftTrace)).1.1.1.elim false _ = true
    rw [setup.proposalRecoveryEraseInfo_current]
    simpa only [commitRecoveryPrivate, Option.map_some, Option.elim_some,
      ProtocolState.atCommit_observe] using leftCommit
  have rightIsCommit : (setup.proposalRecoveryModel.infoOf who rightTrace).1.1.1.elim false
      (ProtocolView.atCommit who setup.program) = true := by
    change (setup.proposalRecoveryEraseInfo who
      (setup.proposalRecoveryModel.infoOf who rightTrace)).1.1.1.elim false _ = true
    rw [setup.proposalRecoveryEraseInfo_current]
    simpa only [commitRecoveryPrivate, Option.map_some, Option.elim_some,
      ProtocolState.atCommit_observe] using rightCommit
  rw [setup.proposalRecoveryNormalizedTrembledProfile_missed_law omission omissionNonnegative
    omissionBounded bad badNonnegative badBounded delivery deliveryNonnegative deliveryBounded
    leftValues who _ leftIsCommit,
    setup.proposalRecoveryNormalizedTrembledProfile_missed_law omission omissionNonnegative
      omissionBounded bad badNonnegative badBounded delivery deliveryNonnegative deliveryBounded
      rightValues who _ rightIsCommit, propext active]

end Vegas.SourceProgram.Setup
