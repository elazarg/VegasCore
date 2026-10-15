/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryDeviationPayoff
import GameTheoryExtensions.Analysis.Protocol.PassageRestrictionExtension

/-! # Intended sequential equilibria with source commitment rollback -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Intended sequential equilibria extend to the actual auxiliary source game
with end-of-block rollback and permanent exclusion. Only actually intended
terminal readouts must lie above exclusion. Strategies, retained beliefs and
the initialized joint readout/payoff-vector law are preserved. -/
theorem intended_sequentialEquilibrium_commitRecovery
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal, (∃ history : setup.intendedProtocol.History,
      setup.protocolReadout history.state = some terminal) →
      ∀ who, excludedPayoff who ≤ utility terminal who)
    (source : setup.intendedModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who history => (setup.protocolReadout history.state).elim 0
        (fun terminal => utility terminal who))) :
    ∃ target : setup.commitRecoveryModel.BehavioralAssessment,
      target.IsSequentialEquilibrium setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryProtocol_bounded.wellFoundedHistories
        (setup.commitRecoveryPayoff utility excludedPayoff) ∧
      (setup.commitRecoveryRestriction wellFormed).ExtendsProfile
        source.strategy target.strategy ∧
      (∀ who site, target.belief who ((setup.commitRecoveryRestriction wellFormed).site who site) =
        (source.belief who site).map
          ((setup.commitRecoveryRestriction wellFormed).informationHistory who site)) ∧
      (∀ fuel, (setup.intendedModel.runBehavioral source.strategy fuel).map
          (fun history => (setup.protocolReadout history.state,
            fun who => (setup.protocolReadout history.state).elim 0
              (fun terminal => utility terminal who))) =
        (setup.commitRecoveryModel.runBehavioral target.strategy fuel).map
          (fun history => (setup.protocolReadout (setup.commitRecoverySourceState history.state),
            fun who => setup.commitRecoveryPayoff utility excludedPayoff who history))) ∧
      (∀ fuel history, history ∈
        (setup.commitRecoveryModel.runBehavioral target.strategy fuel).support →
        setup.CommitRecoveryClear history.state) ∧
      (setup.intendedModel.runBehavioralTerminalFrom setup.intended_bounded.wellFoundedHistories
          source.strategy setup.intendedProtocol.initHistory).map
          (fun history => (setup.protocolReadout history.state,
            fun who => (setup.protocolReadout history.state).elim 0
              (fun terminal => utility terminal who))) =
        (setup.commitRecoveryModel.runBehavioralTerminalFrom
          setup.commitRecoveryProtocol_bounded.wellFoundedHistories
            target.strategy setup.commitRecoveryProtocol.initHistory).map
          (fun history => (setup.protocolReadout (setup.commitRecoverySourceState history.state),
            fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)) := by
  classical
  let restriction := setup.commitRecoveryRestriction wellFormed
  let _ := setup.commitRecovery_finite_history finite
  have : Finite setup.intendedProtocol.History :=
    Finite.of_injective restriction.history restriction.history.injective
  let sourcePayoff : Player → setup.intendedProtocol.History → ℝ := fun who history =>
    (setup.protocolReadout history.state).elim 0 (fun terminal => utility terminal who)
  let targetPayoff := setup.commitRecoveryPayoff utility excludedPayoff
  have matching (who : Player) (history : setup.intendedProtocol.History) :
      targetPayoff who (restriction.history history) = sourcePayoff who history :=
    setup.commitRecoveryPayoff_lift wellFormed utility excludedPayoff who history
  let comparator : ∀ who (site : setup.intendedModel.InformationSite who),
      setup.commitRecoveryModel.Choice who (restriction.site who site).1 →
        PMF (setup.intendedModel.Choice who site.1) :=
    fun _ _ _ => PMF.pure (Classical.arbitrary _)
  obtain ⟨target, sequential, agrees, beliefs, _historyLaw, jointLaw⟩ :=
    restriction.sequentialEquilibrium_extends_of_comparator_unclocked
      setup.intended_decision_antichain setup.intended_bounded.wellFoundedHistories
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories
      (setup.commitRecoveryReference finite) (setup.commitRecoveryReference_fullyMixed finite)
      (setup.commitRecoveryModel.decisionRecall_of_perfectRecall
        setup.commitRecoveryModel_perfectRecall)
      sourcePayoff targetPayoff matching comparator
      (by
        intro sourceProfile targetProfile copies who site action extra history
        have deviation := setup.commitRecovery_deviation_payoff wellFormed utility excludedPayoff
          sourceProfile targetProfile copies who site action extra history
        calc
          _ = expect (setup.intendedModel.runBehavioralTerminalFrom
              setup.intended_bounded.wellFoundedHistories
              (Profile.update (sig := setup.intendedModel.behavioralSignature) sourceProfile who
                ((sourceProfile who).withLaw site.1 (comparator who site action))) history.1)
            (fun _ => expect (setup.commitRecoveryModel.runBehavioralTerminalFrom
              setup.commitRecoveryProtocol_bounded.wellFoundedHistories
              (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
                targetProfile who ((targetProfile who).commit (restriction.site who site).1 action))
              (restriction.history history.1)) (targetPayoff who)) :=
            (expect_constant _ _).symm
          _ ≤ _ := by
            refine expect_mono (fun reached supported => ?_) (payoffIntegrable_constant _ _)
              (payoffIntegrable_of_finite _ _)
            have terminal := setup.intendedModel.runBehavioralTerminalFrom_support_terminal
              setup.intended_bounded.wellFoundedHistories _ _ reached supported
            obtain ⟨terminalState, read⟩ := setup.exists_protocolReadout_of_terminal
              (CommitmentInterface.values setup.program) terminal
            refine expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
              (fun final deviated => ?_)
            change setup.commitRecoveryPayoff utility excludedPayoff who final ≤
              (setup.protocolReadout reached.state).elim 0 (fun terminal => utility terminal who)
            rw [deviation final deviated, read]
            exact below terminalState ⟨reached, read⟩ who)
      source equilibrium
  refine ⟨target, sequential, agrees, beliefs, ?_, ?_, ?_⟩
  · exact setup.commitRecovery_initialized_joint wellFormed utility excludedPayoff
      source.strategy target.strategy agrees
  · exact fun fuel history supported => setup.commitRecovery_run_clear wellFormed
      source.strategy target.strategy agrees fuel history supported
  · have projected := congrArg (PMF.map (fun pair :
        setup.commitRecoveryProtocol.History × (Player → ℝ) =>
          (setup.protocolReadout (setup.commitRecoverySourceState pair.1.state), pair.2))) jointLaw
    simpa only [PMF.map_comp, Function.comp_def, restriction, commitRecoveryRestriction,
      Function.Embedding.coeFn_mk, commitRecoveryLiftHistory_source] using projected

end Vegas.SourceProgram.Setup
