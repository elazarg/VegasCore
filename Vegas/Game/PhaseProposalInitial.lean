/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalTransition
import Vegas.Game.PhaseProposalExecution

/-! # The actual single setup draw starts the consumed proposal archive empty -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem archivedProposals_cast
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state next : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (same : state = next) (checkpoint : RecoverySourceCheckpoint setup mode state)
    (messages : List (Message Player
      (CommitAttemptPacket ((toEventGraph setup.program).withMode mode))))
    (prior : checkpoint.ArchivedProposals messages) :
    (cast (congrArg (RecoverySourceCheckpoint setup mode) same) checkpoint).ArchivedProposals
      messages := by
  cases same
  exact prior

/-- Both archives start empty under the original one supported setup draw.
The actual initialization source trace has only its setup step. -/
theorem RecoverySourceWitness.initialized_archivedProposals
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (initial : State L setup.context) (supported : initial ∈ setup.initialLaw.support) :
    (RecoverySourceWitness.initialized setup mode plan initial
      supported).checkpoint.ArchivedProposals
      [] := by
  change (RecoverySourceCheckpoint.initialized setup mode plan initial
    supported).ArchivedProposals []
  unfold RecoverySourceCheckpoint.initialized
  apply archivedProposals_cast (phaseInitial_eq_raw plan (encodeInputs initial)).symm
    (RecoverySourceCheckpoint.initial setup mode plan initial supported) []
  intro who _active
  have generated := setup.proposalRecoveryArchive_lift (nativeArchiveLabels setup ∅) who
    (RecoverySourceCheckpoint.initial setup mode plan initial supported).trace
  exact generated.trans (by rfl)

end Vegas
