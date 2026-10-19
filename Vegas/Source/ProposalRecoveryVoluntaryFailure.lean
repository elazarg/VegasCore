/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryFlags
import Vegas.Source.CommitRecoveryVoluntaryFailure

/-! # Voluntary omission in the actual proposal-labeled source protocol -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- A noncontinuing semantic choice excludes its owner on the SAME actual
step, whether or not a truthful failed-delivery proposal label is present. -/
theorem proposalRecovery_voluntaryFailure_step (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state)
    (choice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who trace))
    (fails : ¬ setup.CommitRecoveryContinues who
      (setup.proposalRecoveryEraseInfo who (setup.proposalRecoveryModel.infoOf who trace))
        (choice.1.map (·.semantic)))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal state joint) (chosen : joint who = choice.1)
    (target : setup.proposalRecoveryProtocol.State)
    (reached : target ∈ (setup.proposalRecoveryProtocol.step state ⟨joint, legal⟩).support) :
    who ∈ (setup.commitRecoveryPublic target).1 := by
  have permitted := ((setup.proposalRecoveryMenu_semantic who
    (setup.proposalRecoveryModel.infoOf who trace) choice.1).mp choice.2).1
  rw [setup.proposalRecoveryEraseInfo_observed] at permitted fails
  let oldChoice : setup.commitRecoveryModel.Choice who
      (setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace trace)) :=
    ⟨choice.1.map ProposalRecoveryMove.semantic, permitted⟩
  exact setup.commitRecovery_voluntaryFailure_step who (setup.proposalRecoveryEraseTrace trace)
    oldChoice fails (proposalRecoveryJoint joint)
    (setup.proposalRecovery_erase_legal joint legal)
    (congrArg (Option.map ProposalRecoveryMove.semantic) chosen) target reached

end Vegas.SourceProgram.Setup
