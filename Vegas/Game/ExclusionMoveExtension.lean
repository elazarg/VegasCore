/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ExclusionMoveGame
import Vegas.Source.ExclusionFailure
import Vegas.Game.ExclusionExtension
import GameTheoryExtensions.Analysis.Protocol.RestrictedComponentCompletion

/-! # Intended equilibrium extension through mandatory moves

The mandatory-move game embeds the intended game and restricts the exclusion
game. Voluntary failures can be restored by a local comparator once the fixed
exclusion payoff bounds all nonexcluded terminal utilities from below.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Intended actions bind a value or open, and never voluntarily fail. -/
theorem ProtocolView.intendedAvailable_not_failure (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (view : ProtocolView who program) →
    (action : OwnAction Player L) → action ∈ ProtocolView.intendedAvailable who program view →
      ¬ action.IsFailure
  | _, _, .ret _, _, _, impossible => impossible.elim
  | _, _, .sample _ _ _ next, view, action, offered => by
      cases view with
      | inl _ => exact offered.elim
      | inr later => exact intendedAvailable_not_failure who next later action offered
  | _, _, .commit _ _ _ _ next, view, action, offered => by
      cases view with
      | inl _ =>
          obtain ⟨value, _, rfl⟩ := offered
          simp [OwnAction.IsFailure]
      | inr later => exact intendedAvailable_not_failure who next later action offered
  | _, _, .reveal _ _ _ _ _ _ next, view, action, offered => by
      cases view with
      | inl _ =>
          subst offered
          simp [OwnAction.IsFailure]
      | inr later => exact intendedAvailable_not_failure who next later action offered

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

theorem intendedMenu_not_failure (who : Player) (view : setup.ProtocolView who)
    (choice : Option (OwnAction Player L)) (offered : choice ∈ setup.intendedMenu who view)
    (action : OwnAction Player L) (selected : choice = some action) : ¬ action.IsFailure := by
  subst selected
  cases view with
  | none => cases offered
  | some view =>
      exact ProtocolView.intendedAvailable_not_failure who setup.program view action offered.2

/-- Every intended equilibrium has a full exclusion-game extension that never
voluntarily fails at a nonexcluded decision, under the global continuation
payoff floor. Beliefs and the honest joint terminal law are retained. -/
theorem intended_sequentialEquilibrium_extends_without_voluntary_failure [Fintype Player]
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (below : ∀ (final : setup.exclusionProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0 →
          excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (intendedTerminates : setup.intendedProtocol.WellFoundedHistories)
    (exclusionTerminates : setup.exclusionProtocol.WellFoundedHistories)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      intendedTerminates
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who))) :
    ∃ target : setup.exclusionModel.BehavioralAssessment,
      target.IsSequentialEquilibrium setup.exclusion_decisionRecall.decisionInformationAntichain
        exclusionTerminates
        (fun who final => (setup.protocolReadout final.state).elim 0
          (fun state => exclusionUtility setup.program excludedPayoff utility
            (setup.parameterOutcome parameter state) who)) ∧
      (setup.exclusionRestriction wellFormed).ExtendsProfile intended.strategy
        target.strategy ∧
      (∀ who (site : setup.exclusionModel.InformationSite who), site.1.2 = false →
        ∀ choice ∈ (target.strategy who site.1).support, ∀ action,
          choice.1 = some action → ¬ action.IsFailure) ∧
      (∀ who site, target.belief who ((setup.exclusionRestriction wellFormed).site who site) =
        (intended.belief who site).map
          ((setup.exclusionRestriction wellFormed).informationHistory who site)) ∧
      (setup.exclusionModel.runBehavioralTerminalFrom exclusionTerminates target.strategy
          setup.exclusionProtocol.initHistory).map
          (fun final => (setup.protocolReadout final.state,
            fun who => (setup.protocolReadout final.state).elim 0
              (fun state => exclusionUtility setup.program excludedPayoff utility
                (setup.parameterOutcome parameter state) who))) =
        (setup.intendedModel.runBehavioralTerminalFrom intendedTerminates intended.strategy
            setup.intendedProtocol.initHistory).map
          (fun final => (setup.protocolReadout final.state,
            fun who => (setup.protocolReadout final.state).elim 0
              (fun state => utility (setup.parameterOutcome parameter state) who))) ∧
      Nonempty ((setup.exclusionRestriction wellFormed).RestrictedExtensionApproximation
        (setup.exclusionReference finite) target
        setup.exclusion_decisionRecall.decisionInformationAntichain
        (fun who info => setup.exclusionMoveRestriction.choice who info)) := by
  classical
  let restriction := setup.exclusionRestriction wellFormed
  have : Finite setup.exclusionProtocol.History := setup.exclusion_finite_history finite
  have : Finite setup.intendedProtocol.History :=
    Finite.of_injective restriction.history restriction.history.injective
  let intendedPayoff : Player → setup.intendedProtocol.History → ℝ :=
    fun who final => (setup.protocolReadout final.state).elim 0
      (fun state => utility (setup.parameterOutcome parameter state) who)
  let exclusionPayoff : Player → setup.exclusionProtocol.History → ℝ :=
    fun who final => (setup.protocolReadout final.state).elim 0
      (fun state => exclusionUtility setup.program excludedPayoff utility
        (setup.parameterOutcome parameter state) who)
  have matching : ∀ who (history : setup.intendedProtocol.History),
      exclusionPayoff who (restriction.history history) = intendedPayoff who history := by
    intro who history
    change (setup.protocolReadout history.state).elim 0 _ =
      (setup.protocolReadout history.state).elim 0 _
    cases read : setup.protocolReadout history.state with
    | none => rfl
    | some terminal =>
        exact exclusionUtility_of_failedReveals_eq_zero _ _ _
          (setup.failedReveals_eq_zero_of_intendedState
            (setup.intendedState_trace wellFormed history.trace) who read)
  let comparator : ∀ who (site : setup.intendedModel.InformationSite who),
      setup.exclusionModel.Choice who (restriction.site who site).1 →
        PMF (setup.intendedModel.Choice who site.1) :=
    fun _ _ _ => PMF.pure (Classical.arbitrary _)
  have payoffLower (who : Player) (final : setup.exclusionProtocol.History)
      (stopped : setup.exclusionProtocol.terminal final.state) :
      excludedPayoff who ≤ exclusionPayoff who final := by
    obtain ⟨terminal, read⟩ := setup.exists_protocolReadout_of_terminal
      (CommitmentInterface.forfeiture setup.program) stopped
    change excludedPayoff who ≤ (setup.protocolReadout final.state).elim 0 _
    rw [read]
    simp only [Option.elim_some]
    unfold exclusionUtility
    split
    · exact below final terminal read who ‹_›
    · exact le_rfl
  have : ∀ who (info : setup.exclusionModel.InfoState who),
      Finite (setup.exclusionMoveModel.Choice who info) :=
    fun who info => setup.exclusionMove_finite_choice finite who info
  have : ∀ who (info : setup.exclusionModel.InfoState who),
      Nonempty (setup.exclusionMoveModel.Choice who info) :=
    fun who info => setup.exclusionMove_choice_nonempty who info
  obtain ⟨target, consistent, agrees, beliefs, newAllowed, ⟨approximation⟩⟩ :=
    restriction.exists_consistent_restricted_extension_unclocked intended
      setup.intended_decision_antichain equilibrium.2 (setup.exclusionReference finite)
      (setup.exclusionReference_fullyMixed finite) setup.exclusion_decisionRecall
      exclusionTerminates exclusionPayoff (fun who info =>
        setup.exclusionMoveRestriction.choice who info)
  have contextLower (who : Player) (site : setup.exclusionModel.InformationSite who)
      (policy : setup.exclusionModel.BehavioralPolicy who) :
      excludedPayoff who ≤ (target.continuationContext exclusionTerminates site
        (exclusionPayoff who)).value policy := by
    let context := target.continuationContext exclusionTerminates site (exclusionPayoff who)
    change excludedPayoff who ≤ expect (context.outcome policy) (exclusionPayoff who)
    calc
      excludedPayoff who = expect (context.outcome policy) (fun _ => excludedPayoff who) :=
        (expect_constant _ _).symm
      _ ≤ _ := expect_mono (fun final supported => payoffLower who final
        (target.continuationContext_support_terminal exclusionTerminates site
          (exclusionPayoff who) policy final supported))
        (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
  have localOptimal : ∀ who (site : setup.exclusionModel.InformationSite who)
      (law : PMF (setup.exclusionModel.Choice who site.1)),
      (target.continuationContext exclusionTerminates site (exclusionPayoff who)).value
          ((target.strategy who).withLaw site.1 law) ≤
        (target.continuationContext exclusionTerminates site (exclusionPayoff who)).value
          (target.strategy who) := by
    intro who site law
    by_cases retained : restriction.Retained who site.1
    · obtain ⟨original, observed⟩ := retained
      have same : restriction.site who original = site := Subtype.ext observed
      subst site
      apply restriction.retained_localOptimal_of_comparator intendedTerminates
        exclusionTerminates intended target agrees
        setup.exclusion_decisionRecall.actsOnceWhereItMatters who original (beliefs who original)
        (intendedPayoff who) (exclusionPayoff who) (matching who) (equilibrium.1 who original)
        (comparator who original) ?_ law
      intro action extra history
      have deviation := setup.exclusion_deviation_failedReveals_pos wellFormed
        exclusionTerminates target.strategy who original action extra history
      calc
        _ ≤ excludedPayoff who := expect_le_const _ _ (payoffIntegrable_of_finite _ _)
          _ (fun final supported => by
            obtain ⟨terminal, read, positive⟩ := deviation final supported
            change (setup.protocolReadout final.state).elim 0 _ ≤ excludedPayoff who
            rw [read]
            simp only [Option.elim_some]
            rw [exclusionUtility_of_failedReveals_pos _ _ _ positive])
        _ = expect (setup.intendedModel.runBehavioralTerminalFrom intendedTerminates
            (Profile.update (sig := setup.intendedModel.behavioralSignature) intended.strategy who
              ((intended.strategy who).withLaw original.1 (comparator who original action)))
            history.1) (fun _ => excludedPayoff who) := (expect_constant _ _).symm
        _ ≤ _ := expect_mono (fun final supported => by
            rw [← matching who final]
            exact payoffLower who (restriction.history final)
              ((restriction.terminal final).mpr
                (setup.intendedModel.runBehavioralTerminalFrom_support_terminal
                  intendedTerminates _ _ final supported)))
          (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
    · obtain ⟨_current, _mixture, optimal⟩ := newAllowed who site retained
      rw [target.continuationContext_withLaw_eq_expect
        setup.exclusion_decisionRecall.actsOnceWhereItMatters exclusionTerminates site
        (target.strategy who) law (exclusionPayoff who)]
      refine expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ fun choice _ => ?_
      by_cases permitted : choice.1 ∈ setup.exclusionMoveMenu who site.1
      · let move : setup.exclusionMoveModel.Choice who site.1 := ⟨choice.1, permitted⟩
        have same : setup.exclusionMoveRestriction.choice who site.1 move = choice :=
          Subtype.ext rfl
        have pureEq : (PMF.pure move).map
            (setup.exclusionMoveRestriction.choice who site.1) = PMF.pure choice := by
          rw [PMF.pure_map, same]
        have bound := optimal (PMF.pure move)
        have valueEq := congrArg (fun localLaw : PMF (setup.exclusionModel.Choice who site.1) =>
          (target.continuationContext exclusionTerminates site (exclusionPayoff who)).value
            ((target.strategy who).withLaw site.1 localLaw)) pureEq
        exact valueEq.symm.le.trans bound
      · have failure : ∃ action, choice.1 = some action ∧ action.IsFailure := by
          cases selected : choice.1 with
          | none =>
              exact (permitted ⟨choice.2, fun _ _ chosen => by
                rw [selected] at chosen
                cases chosen⟩).elim
          | some action =>
              refine ⟨action, rfl, ?_⟩
              by_contra moves
              apply permitted
              refine ⟨choice.2, fun _ other chosen => ?_⟩
              rw [selected] at chosen
              cases Option.some.inj chosen
              exact moves
        obtain ⟨action, selected, fails⟩ := failure
        rw [setup.exclusion_failure_context_value exclusionTerminates target who site choice
          selected fails parameter utility excludedPayoff]
        exact contextLower who site (target.strategy who)
  have sequential :=
    (InformationModel.BehavioralAssessment.isSequentialEquilibrium_iff_locallyOptimal
    setup.exclusionModel setup.exclusion_decisionRecall target exclusionTerminates
    exclusionPayoff).mpr ⟨consistent, localOptimal⟩
  have neverFails : ∀ who (site : setup.exclusionModel.InformationSite who), site.1.2 = false →
      ∀ choice ∈ (target.strategy who site.1).support, ∀ action,
        choice.1 = some action → ¬ action.IsFailure := by
    intro who site clear choice supported action selected
    by_cases retained : restriction.Retained who site.1
    · obtain ⟨original, observed⟩ := retained
      have same : restriction.site who original = site := Subtype.ext observed
      subst site
      change choice ∈ (target.strategy who (restriction.information who original.1)).support
        at supported
      rw [agrees who original] at supported
      obtain ⟨sourceChoice, _sourceSupported, sameChoice⟩ :=
        (PMF.mem_support_map_iff _ _ _).mp supported
      have values : (restriction.choice who original.1 sourceChoice).1 = sourceChoice.1 := rfl
      apply setup.intendedMenu_not_failure who original.1 sourceChoice.1 sourceChoice.2 action
      exact values.symm.trans ((congrArg Subtype.val sameChoice).trans selected)
    · obtain ⟨current, mixture, _optimal⟩ := newAllowed who site retained
      rw [mixture] at supported
      obtain ⟨move, _moveSupported, sameChoice⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact setup.exclusionMove_choice_not_failure who site.1 clear move action
        ((congrArg Subtype.val sameChoice).trans selected)
  refine ⟨target, sequential, agrees, neverFails, beliefs, ?_, ⟨approximation⟩⟩
  have historyLaw := restriction.terminal_law intendedTerminates exclusionTerminates
    intended.strategy target.strategy agrees setup.intendedProtocol.initHistory
  have jointLaw :
      (setup.intendedModel.runBehavioralTerminalFrom intendedTerminates intended.strategy
          setup.intendedProtocol.initHistory).map
          (fun history => (restriction.history history, fun who => intendedPayoff who history)) =
        (setup.exclusionModel.runBehavioralTerminalFrom exclusionTerminates target.strategy
          setup.exclusionProtocol.initHistory).map
          (fun history => (history, fun who => exclusionPayoff who history)) := by
    rw [restriction.initial] at historyLaw
    rw [← historyLaw, PMF.map_comp]
    congr 1
    funext history
    exact congrArg (fun values => (restriction.history history, values))
      (funext fun who => (matching who history).symm)
  have readouts := congrArg (PMF.map fun pair => (setup.protocolReadout pair.1.state, pair.2))
    jointLaw
  simp only [PMF.map_comp] at readouts
  exact readouts.symm

end Setup
end Vegas.SourceProgram
