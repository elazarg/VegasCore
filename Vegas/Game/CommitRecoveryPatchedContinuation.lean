/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryLocalSourcePatch

/-! # Full source continuations after one retained local lottery changes -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

open Classical in
/-- A literal source-site intervention has the exact original source terminal
readout and payoff law from every genuine retained history. The auxiliary
continuation changes only at that site, and its continuing support is retained. -/
theorem commitRecovery_local_source_patch_continuation
    (wellFormed : setup.WellFormed)
    (source : ∀ owner, setup.intendedModel.BehavioralPolicy owner)
    (target : ∀ owner, setup.commitRecoveryModel.BehavioralPolicy owner)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source target)
    (continuing : ∀ owner (site : setup.commitRecoveryModel.InformationSite owner),
      ∀ choice ∈ (target owner site.1).support,
        setup.CommitRecoveryContinues owner site.1 choice.1)
    (who : Player) (selected : setup.intendedModel.InformationSite who)
    (law : PMF (setup.intendedModel.Choice who selected.1))
    (original : setup.intendedProtocol.History)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ) :
    let restriction := setup.commitRecoveryRestriction wellFormed
    let changed := Profile.update (sig := setup.intendedModel.behavioralSignature) source who
      ((source who).withLaw selected.1 law)
    let patched := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) target who
      ((target who).withLaw (restriction.information who selected.1)
        (law.map (restriction.choice who selected.1)))
    (∀ owner (site : setup.commitRecoveryModel.InformationSite owner),
      ∀ choice ∈ (patched owner site.1).support,
        setup.CommitRecoveryContinues owner site.1 choice.1) ∧
    (setup.intendedModel.runBehavioralTerminalFrom setup.intended_bounded.wellFoundedHistories
        changed original).map (fun final => (setup.protocolReadout final.state,
          fun owner => (setup.protocolReadout final.state).elim 0
            (fun terminal => utility terminal owner))) =
      (setup.commitRecoveryModel.runBehavioralTerminalFrom
        setup.commitRecoveryProtocol_bounded.wellFoundedHistories patched
        (restriction.history original)).map (fun final =>
          (setup.protocolReadout (setup.commitRecoverySourceState final.state),
            fun owner => setup.commitRecoveryPayoff utility excludedPayoff owner final)) := by
  classical
  intro restriction changed patched
  obtain ⟨extended, remains⟩ := setup.commitRecovery_local_source_patch wellFormed source target
    copies continuing who selected law
  refine ⟨remains, ?_⟩
  have historyLaw :
      (setup.intendedModel.runBehavioralTerminalFrom setup.intended_bounded.wellFoundedHistories
        changed original).map restriction.history =
      setup.commitRecoveryModel.runBehavioralTerminalFrom
        setup.commitRecoveryProtocol_bounded.wellFoundedHistories patched
        (restriction.history original) := by
    rw [setup.intendedModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
        setup.intended_bounded.wellFoundedHistories
        (restriction.boundedHorizon setup.commitRecoveryProtocol_bounded),
      setup.commitRecoveryModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
        setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        setup.commitRecoveryProtocol_bounded]
    exact restriction.runFrom_law changed patched extended _ original
  rw [← historyLaw, PMF.map_comp]
  apply map_congr_on_support
  intro final _supported
  apply Prod.ext
  · exact (congrArg setup.protocolReadout
      (setup.commitRecoveryLiftHistory_source wellFormed final)).symm
  · funext owner
    exact (setup.commitRecoveryPayoff_lift wellFormed utility excludedPayoff owner final).symm

end Vegas.SourceProgram.Setup
