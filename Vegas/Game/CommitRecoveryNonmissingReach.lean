/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryNonmissingLaw

/-! # Exact nonmissing factors of actual auxiliary source histories -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
/-- Every recorded coordinate of an actual clear step carries a false
physical omission bit. This uses permanent exclusion in the real protocol. -/
theorem commitRecovery_clear_joint_nonmissing
    {before after : setup.commitRecoveryProtocol.State}
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal before joint)
    (reached : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support)
    (clear : setup.CommitRecoveryClear after) (who : Player) :
    CommitRecoveryMove.missed (joint who) = false := by
  rw [setup.commitRecovery_clear_joint_lift joint legal reached clear who]
  exact CommitRecoveryMove.missed_lift _

/-- A genuine clear one-step history has exactly the product of the local
nonmissing marginals times its mass under the conditioned source policy.
The actual transition and automatic close kernels are identical on both sides. -/
theorem commitRecovery_nonmissing_step_density
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    {before after : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace before)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal before joint)
    (reached : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support)
    (clear : setup.CommitRecoveryClear after) :
    setup.commitRecoveryModel.stepProb assessment.strategy prior ⟨joint, legal⟩ after =
      (∏ who, (setup.commitRecoveryNonmissingMass assessment.strategy who
        (setup.commitRecoveryModel.infoOf who prior)).toReal) *
      setup.commitRecoveryModel.stepProb
        (setup.commitRecoveryNonmissingProfile assessment.strategy) prior ⟨joint, legal⟩ after := by
  unfold GameTheory.Protocol.InformationModel.stepProb
  rw [setup.commitRecoveryModel.behavioralJoint_prob_eq_prod,
    setup.commitRecoveryModel.behavioralJoint_prob_eq_prod]
  have coordinate (who : Player) :
      (assessment.strategy who (setup.commitRecoveryModel.infoOf who prior)
        (setup.commitRecoveryModel.choicesOfLegal prior ⟨joint, legal⟩ who)).toReal =
      (setup.commitRecoveryNonmissingMass assessment.strategy who
        (setup.commitRecoveryModel.infoOf who prior)).toReal *
      (setup.commitRecoveryNonmissingProfile assessment.strategy who
        (setup.commitRecoveryModel.infoOf who prior)
        (setup.commitRecoveryModel.choicesOfLegal prior ⟨joint, legal⟩ who)).toReal := by
    rw [setup.commitRecovery_nonmissing_atom assessment.strategy who _
      (setup.commitRecovery_nonmissing_present assessment mixed ⟨_, prior⟩ legal.1 who) _
      (setup.commitRecovery_clear_joint_nonmissing joint legal reached clear who),
      ENNReal.toReal_mul]
  simp_rw [coordinate]
  rw [Finset.prod_mul_distrib]
  ring

/-- Exact actual-history density under chronological nonmissing sampling.
The complete source trace, private actions, chance outputs and automatic
checkpoint changes are retained; only its scalar omission weight is removed. -/
theorem commitRecovery_nonmissing_history_density
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) :
    ∀ {state : setup.commitRecoveryProtocol.State}
      (trace : setup.commitRecoveryProtocol.Trace state) (_clear : setup.CommitRecoveryClear state),
      (setup.commitRecoveryModel.historyReachWeight assessment.strategy ⟨state, trace⟩).toReal =
        setup.commitRecoveryNonmissingFactor assessment.strategy trace *
          (setup.commitRecoveryModel.historyReachWeight
            (setup.commitRecoveryNonmissingProfile assessment.strategy) ⟨state, trace⟩).toReal
  | _, .start, _ => by
      simp only [commitRecoveryNonmissingFactor, one_mul]
      rfl
  | _, .extend prior joint legal reached, clear => by
      rw [setup.commitRecoveryModel.historyReachProbability_extend,
        setup.commitRecoveryModel.historyReachProbability_extend,
        commitRecovery_nonmissing_history_density assessment mixed prior
          (setup.commitRecoveryClear_before ⟨joint, legal⟩ reached clear),
        setup.commitRecovery_nonmissing_step_density assessment mixed prior joint legal reached
          clear]
      change (_ * _) * (_ * _) = (_ * _) * (_ * _)
      ring

end Vegas.SourceProgram.Setup
