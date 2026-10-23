/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryRestriction
import Vegas.Game.ProposalRecoveryPayoff
import GameTheory.Protocol.RestrictionExecution

/-! # The selected initialized history and joint payoff law of ordinary lifts -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

theorem proposalRecoveryPayoff_lift (wellFormed : setup.WellFormed)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (who : Player) (history : setup.intendedProtocol.History) :
    setup.proposalRecoveryPayoff utility excludedPayoff who
        (setup.proposalRecoveryIntendedLift wellFormed history) =
      (setup.protocolReadout history.state).elim 0 (fun terminal => utility terminal who) := by
  change setup.commitRecoveryPayoff utility excludedPayoff who
    ⟨(setup.commitRecoveryLiftHistory wellFormed history).state,
      setup.proposalRecoveryEraseTrace
        (setup.proposalRecoveryLiftTrace (fun _ _ => false)
          (setup.commitRecoveryLiftHistory wellFormed history).trace)⟩ = _
  rw [setup.proposalRecoveryEraseTrace_lift]
  exact setup.commitRecoveryPayoff_lift wellFormed utility excludedPayoff who history

/-- Exact initialized FULL history law for any profile agreeing with the
selected intended strategy at the concrete intended information embedding. -/
theorem proposalRecovery_initialized_history [Fintype Player] (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (agrees : (setup.proposalRecoveryRestriction wellFormed).ExtendsProfile source target)
    (fuel : Nat) :
    (setup.intendedModel.runBehavioral source fuel).map
        (setup.proposalRecoveryIntendedLift wellFormed) =
      setup.proposalRecoveryModel.runBehavioral target fuel :=
  (setup.proposalRecoveryRestriction wellFormed).initialized_law source target agrees fuel

/-- The initialized readout and the ENTIRE realized payoff vector are
preserved jointly. This is a pushforward of the concrete full history law,
including the original initializer and every actual source Nature draw. -/
theorem proposalRecovery_initialized_joint [Fintype Player] (wellFormed : setup.WellFormed)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (agrees : (setup.proposalRecoveryRestriction wellFormed).ExtendsProfile source target)
    (fuel : Nat) :
    (setup.intendedModel.runBehavioral source fuel).map
        (fun history => (setup.protocolReadout history.state,
          fun who => (setup.protocolReadout history.state).elim 0
            (fun terminal => utility terminal who))) =
      (setup.proposalRecoveryModel.runBehavioral target fuel).map
        (fun history =>
          (setup.protocolReadout (setup.commitRecoverySourceState history.state),
            fun who => setup.proposalRecoveryPayoff utility excludedPayoff who history)) := by
  have law := setup.proposalRecovery_initialized_history wellFormed source target agrees fuel
  have joint := congrArg (PMF.map fun history : setup.proposalRecoveryProtocol.History =>
    (setup.protocolReadout (setup.commitRecoverySourceState history.state),
      fun who => setup.proposalRecoveryPayoff utility excludedPayoff who history)) law
  simp only [PMF.map_comp, Function.comp_def, setup.proposalRecoveryPayoff_lift] at joint
  simpa only [proposalRecoveryIntendedLift, setup.commitRecoveryLiftHistory_source] using joint

/-- Every initialized history selected by such an extension has no actual
exclusions; this is a support consequence, not an equilibrium assumption. -/
theorem proposalRecovery_run_clear [Fintype Player] (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (agrees : (setup.proposalRecoveryRestriction wellFormed).ExtendsProfile source target)
    (fuel : Nat) (history : setup.proposalRecoveryProtocol.History)
    (supported : history ∈ (setup.proposalRecoveryModel.runBehavioral target fuel).support) :
    setup.CommitRecoveryClear history.state := by
  rw [← setup.proposalRecovery_initialized_history wellFormed source target agrees fuel]
    at supported
  obtain ⟨original, _reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact setup.commitRecoveryLiftHistory_clear wellFormed original

end Vegas.SourceProgram.Setup
