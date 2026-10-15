/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryPreservation
import Vegas.Game.CommitRecoveryVoluntaryFailurePayoff
import Vegas.Game.ExclusionMoveExtension
import GameTheoryExtensions.Analysis.Protocol.RestrictedComponentCompletion

/-! # Source rollback equilibria without voluntary omissions or withheld openings -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Under the global terminal payoff floor, intended equilibria extend to
actual source rollback equilibria that never voluntarily omit or withhold.
Accepted failed bindings remain legal. The original strategies, retained
beliefs and initialized joint terminal law are preserved. -/
theorem intended_sequentialEquilibrium_commitRecovery_continuing
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
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
      (∀ who (site : setup.commitRecoveryModel.InformationSite who),
        ∀ choice ∈ (target.strategy who site.1).support,
          setup.CommitRecoveryContinues who site.1 choice.1) ∧
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
            fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)) ∧
      Nonempty ((setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
        (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice) := by
  classical
  let restriction := setup.commitRecoveryRestriction wellFormed
  let _ := setup.commitRecovery_finite_history finite
  have : Finite setup.intendedProtocol.History :=
    Finite.of_injective restriction.history restriction.history.injective
  let sourcePayoff : Player → setup.intendedProtocol.History → ℝ := fun who history =>
    (setup.protocolReadout history.state).elim 0 (fun terminal => utility terminal who)
  let targetPayoff := setup.commitRecoveryPayoff utility excludedPayoff
  let certificate := setup.commitRecoveryProtocol_bounded.wellFoundedHistories
  let decisionRecall := setup.commitRecoveryModel.decisionRecall_of_perfectRecall
    setup.commitRecoveryModel_perfectRecall
  have matching (who : Player) (history : setup.intendedProtocol.History) :
      targetPayoff who (restriction.history history) = sourcePayoff who history :=
    setup.commitRecoveryPayoff_lift wellFormed utility excludedPayoff who history
  let comparator : ∀ who (site : setup.intendedModel.InformationSite who),
      setup.commitRecoveryModel.Choice who (restriction.site who site).1 →
        PMF (setup.intendedModel.Choice who site.1) :=
    fun _ _ _ => PMF.pure (Classical.arbitrary _)
  have : ∀ who info, Finite (setup.CommitRecoveryContinuingChoice who info) :=
    fun who info => setup.commitRecoveryContinuingChoice_finite finite who info
  have : ∀ who info, Nonempty (setup.CommitRecoveryContinuingChoice who info) :=
    fun who info => setup.commitRecoveryContinuingChoice_nonempty who info
  obtain ⟨target, consistent, agrees, beliefs, newAllowed, ⟨approximation⟩⟩ :=
    restriction.exists_consistent_restricted_extension_unclocked source
      setup.intended_decision_antichain equilibrium.2 (setup.commitRecoveryReference finite)
      (setup.commitRecoveryReference_fullyMixed finite) decisionRecall certificate targetPayoff
      setup.commitRecoveryContinuingChoice
  have contextLower (who : Player) (site : setup.commitRecoveryModel.InformationSite who)
      (policy : setup.commitRecoveryModel.BehavioralPolicy who) :
      excludedPayoff who ≤
        (target.continuationContext certificate site (targetPayoff who)).value policy := by
    let context := target.continuationContext certificate site (targetPayoff who)
    change excludedPayoff who ≤ expect (context.outcome policy) (targetPayoff who)
    calc
      _ = expect (context.outcome policy) (fun _ => excludedPayoff who) :=
        (expect_constant _ _).symm
      _ ≤ _ := expect_mono (fun final supported =>
        setup.commitRecovery_terminal_payoff_lower utility excludedPayoff below who final
          (target.continuationContext_support_terminal certificate site (targetPayoff who)
            policy final supported)) (payoffIntegrable_constant _ _)
        (payoffIntegrable_of_finite _ _)
  have localOptimal : ∀ who (site : setup.commitRecoveryModel.InformationSite who)
      (law : PMF (setup.commitRecoveryModel.Choice who site.1)),
      (target.continuationContext certificate site (targetPayoff who)).value
          ((target.strategy who).withLaw site.1 law) ≤
        (target.continuationContext certificate site (targetPayoff who)).value
          (target.strategy who) := by
    intro who site law
    by_cases retained : restriction.Retained who site.1
    · obtain ⟨original, observed⟩ := retained
      have same : restriction.site who original = site := Subtype.ext observed
      subst site
      apply restriction.retained_localOptimal_of_comparator
        setup.intended_bounded.wellFoundedHistories certificate source target agrees
        decisionRecall.actsOnceWhereItMatters who original (beliefs who original)
        (sourcePayoff who) (targetPayoff who) (matching who) (equilibrium.1 who original)
        (comparator who original) ?_ law
      intro action extra history
      have deviation := setup.commitRecovery_deviation_payoff wellFormed utility excludedPayoff
        source.strategy target.strategy agrees who original action extra history
      calc
        _ ≤ excludedPayoff who := expect_le_const _ _ (payoffIntegrable_of_finite _ _) _
          (fun final supported => (deviation final supported).le)
        _ = expect (setup.intendedModel.runBehavioralTerminalFrom
            setup.intended_bounded.wellFoundedHistories
            (Profile.update (sig := setup.intendedModel.behavioralSignature) source.strategy who
              ((source.strategy who).withLaw original.1 (comparator who original action)))
            history.1) (fun _ => excludedPayoff who) := (expect_constant _ _).symm
        _ ≤ _ := expect_mono (fun final supported => by
            have stopped := setup.intendedModel.runBehavioralTerminalFrom_support_terminal
              setup.intended_bounded.wellFoundedHistories _ _ final supported
            obtain ⟨terminal, read⟩ := setup.exists_protocolReadout_of_terminal
              (CommitmentInterface.values setup.program) stopped
            change excludedPayoff who ≤ (setup.protocolReadout final.state).elim 0 _
            rw [read]
            exact below terminal who) (payoffIntegrable_constant _ _)
          (payoffIntegrable_of_finite _ _)
    · obtain ⟨_current, _mixture, optimal⟩ := newAllowed who site retained
      rw [target.continuationContext_withLaw_eq_expect decisionRecall.actsOnceWhereItMatters
        certificate site (target.strategy who) law (targetPayoff who)]
      refine expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ fun choice _supported => ?_
      by_cases continuing : setup.CommitRecoveryContinues who site.1 choice.1
      · let move : setup.CommitRecoveryContinuingChoice who site.1 := ⟨choice, continuing⟩
        have same : setup.commitRecoveryContinuingChoice who site.1 move = choice := rfl
        have pureEq : (PMF.pure move).map (setup.commitRecoveryContinuingChoice who site.1) =
            PMF.pure choice := by rw [PMF.pure_map, same]
        have bound := optimal (PMF.pure move)
        have valueEq := congrArg (fun localLaw :
            PMF (setup.commitRecoveryModel.Choice who site.1) =>
          (target.continuationContext certificate site (targetPayoff who)).value
            ((target.strategy who).withLaw site.1 localLaw)) pureEq
        exact valueEq.symm.le.trans bound
      · rw [setup.commitRecovery_voluntaryFailure_context_value target who site choice continuing
          utility excludedPayoff]
        exact contextLower who site (target.strategy who)
  have sequential :=
    (InformationModel.BehavioralAssessment.isSequentialEquilibrium_iff_locallyOptimal
      setup.commitRecoveryModel decisionRecall target certificate targetPayoff).mpr
        ⟨consistent, localOptimal⟩
  have continues : ∀ who (site : setup.commitRecoveryModel.InformationSite who),
      ∀ choice ∈ (target.strategy who site.1).support,
        setup.CommitRecoveryContinues who site.1 choice.1 := by
    intro who site choice supported
    by_cases retained : restriction.Retained who site.1
    · obtain ⟨original, observed⟩ := retained
      have same : restriction.site who original = site := Subtype.ext observed
      subst site
      change choice ∈ (target.strategy who (restriction.information who original.1)).support
        at supported
      rw [agrees who original] at supported
      obtain ⟨sourceChoice, _supported, equal⟩ :=
        (PMF.mem_support_map_iff _ _ _).mp supported
      have values : (restriction.choice who original.1 sourceChoice).1 =
          CommitRecoveryMove.lift sourceChoice.1 := rfl
      have selected := values.symm.trans (congrArg Subtype.val equal)
      intro move chosen
      rw [chosen] at selected
      cases raw : sourceChoice.1 with
      | none => rw [raw] at selected; cases selected
      | some action =>
          rw [raw] at selected
          have sameMove : (⟨action, false⟩ : CommitRecoveryMove Player L) = move :=
            Option.some.inj selected
          subst move
          exact ⟨rfl, fun _ => setup.intendedMenu_not_failure who original.1 sourceChoice.1
            sourceChoice.2 action raw⟩
    · obtain ⟨current, mixture, _optimal⟩ := newAllowed who site retained
      rw [mixture] at supported
      obtain ⟨move, _supported, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact (congrArg Subtype.val equal) ▸ move.2
  refine ⟨target, sequential, agrees, continues, beliefs, ?_, ?_, ?_, ⟨approximation⟩⟩
  · exact setup.commitRecovery_initialized_joint wellFormed utility excludedPayoff
      source.strategy target.strategy agrees
  · exact fun fuel history supported => setup.commitRecovery_run_clear wellFormed
      source.strategy target.strategy agrees fuel history supported
  · have historyLaw := restriction.terminal_law setup.intended_bounded.wellFoundedHistories
      certificate source.strategy target.strategy agrees setup.intendedProtocol.initHistory
    rw [restriction.initial] at historyLaw
    rw [← historyLaw, PMF.map_comp]
    apply map_congr_on_support
    intro history _supported
    apply Prod.ext
    · exact (congrArg setup.protocolReadout
        (setup.commitRecoveryLiftHistory_source wellFormed history)).symm
    · funext who
      exact (matching who history).symm

end Vegas.SourceProgram.Setup
