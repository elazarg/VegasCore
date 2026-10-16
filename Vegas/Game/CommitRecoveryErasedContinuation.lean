/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryErasedContinuation
import Vegas.Source.CommitRecoveryErasedModel
import Vegas.Game.CommitRecoveryPayoff

/-! # Terminal payoff laws for the selected erased source prescription -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- The concrete reduced prescription gives identical terminal readout and
permanent-exclusion laws from equivalent genuine erased source histories. -/
theorem commitRecoveryErasedProfile_terminal_readout_excluded_eq
    (profile : ∀ who, setup.commitRecoveryErasedModel.BehavioralPolicy who)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (first second : setup.commitRecoveryProtocol.History)
    (same : setup.commitRecoveryErasedHistory first = setup.commitRecoveryErasedHistory second) :
    (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.commitRecoveryErasedProfile profile) first).map
        (fun history =>
          (setup.protocolReadout (setup.commitRecoverySourceState history.state),
            (setup.commitRecoveryPublic history.state).1)) =
      (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.commitRecoveryErasedProfile profile) second).map
        (fun history =>
          (setup.protocolReadout (setup.commitRecoverySourceState history.state),
            (setup.commitRecoveryPublic history.state).1)) :=
  setup.commitRecovery_terminal_readout_excluded_erased_eq
    (setup.commitRecoveryErasedProfile profile)
    (setup.commitRecoveryErasedProfile_congr profile) certificate first second same

/-- Arbitrary source utilities and exclusion payoffs are read jointly from
that same terminal law; no continuation-payoff equality is assumed. -/
theorem commitRecoveryErasedProfile_terminal_joint_eq
    (profile : ∀ who, setup.commitRecoveryErasedModel.BehavioralPolicy who)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (first second : setup.commitRecoveryProtocol.History)
    (same : setup.commitRecoveryErasedHistory first = setup.commitRecoveryErasedHistory second) :
    (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.commitRecoveryErasedProfile profile) first).map
        (fun history =>
          (setup.protocolReadout (setup.commitRecoverySourceState history.state),
            fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)) =
      (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
        (setup.commitRecoveryErasedProfile profile) second).map
        (fun history =>
          (setup.protocolReadout (setup.commitRecoverySourceState history.state),
            fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)) := by
  let read := fun result : Option (State L setup.program.terminalCtx) × Finset Player =>
    (result.1, fun who => if who ∈ result.2 then excludedPayoff who else
      result.1.elim 0 (fun terminal => utility terminal who))
  have joint := setup.commitRecoveryErasedProfile_terminal_readout_excluded_eq profile certificate
    first second same
  have projected := congrArg (PMF.map read) joint
  simpa only [PMF.map_comp, Function.comp_def, read, commitRecoveryPayoff] using projected

end Vegas.SourceProgram.Setup
