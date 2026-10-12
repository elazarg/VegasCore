/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ExclusionGame
import Vegas.Game.IntendedPreservation

/-! # Extending intended equilibria to the source game with exclusion

The intended game of a well-formed setup embeds into the exclusion game
(`Vegas.SourceProgram.Setup.exclusionRestriction`): no position of the intended
game excludes anyone, so every intended view is carried with an unset flag,
where the exclusion game offers the full source menu.

With a payoff under exclusion no larger than any intended terminal payoff,
every sequential equilibrium of the intended game extends to a sequential
equilibrium of the exclusion game
(`Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_extends_to_exclusion`).
It plays the intended laws at every intended decision site, keeps the intended
beliefs there, and has the intended joint law of terminal store and payoff. A
source action that the intended game does not offer leaves its author owing a
failed reveal, whatever anyone plays afterwards; the exclusion payoff then pays
it the fixed exclusion payoff, no more than any intended continuation.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable (setup : Setup (Player := Player) (L := L))

/-- The uniform law over the legal choices at every information value of the
exclusion game. -/
def exclusionReference (finite : setup.program.FiniteBindingTypes) :
    setup.exclusionModel.BehavioralAssessment :=
  .ofStrategy fun who info =>
    let := setup.exclusion_finite_choice finite who info
    let := Fintype.ofFinite (setup.exclusionModel.Choice who info)
    let := setup.exclusion_choice_nonempty who info
    PMF.uniformOfFintype _

theorem exclusionReference_fullyMixed (finite : setup.program.FiniteBindingTypes) :
    (setup.exclusionReference finite).IsFullyMixed := by
  intro who site choice
  let := setup.exclusion_finite_choice finite who site.1
  let := Fintype.ofFinite (setup.exclusionModel.Choice who site.1)
  let := setup.exclusion_choice_nonempty who site.1
  exact PMF.mem_support_uniformOfFintype choice

/-- The exclusion game has finitely many histories under finite fresh-binding
alphabets and a finite initial law. -/
theorem exclusion_finite_history [Finite Player] (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] : Finite setup.exclusionProtocol.History :=
  have := setup.finite_history finite (CommitmentInterface.forfeiture setup.program)
  Finite.of_injective restrictAvailable.history restrictAvailable.history_injective

theorem not_excludedState_of_intendedState {state : setup.ProtocolState}
    (intended : setup.IntendedState state) (who : Player) : ¬ setup.ExcludedState who state := by
  cases state with
  | none => exact id
  | some state => exact ProtocolState.not_excluded_of_intended who setup.program state intended

theorem excludedFlag_observe_eq_false {state : setup.ProtocolState} {who : Player}
    (included : ¬ setup.ExcludedState who state) :
    setup.excludedFlag who (setup.protocolObserve who state) = false := by
  simpa only [Bool.not_eq_true] using mt (setup.excludedFlag_observe_eq_true who state).mp included

/-- **The intended game inside the exclusion game.** No position of the
intended game excludes anyone, so intended views go to the exclusion game with
an unset flag, intended choices are full-menu choices, and intended histories
are exclusion histories. -/
def exclusionRestriction (wellFormed : setup.WellFormed) :
    setup.intendedModel.ActionRestriction setup.exclusionModel :=
  (setup.informationModel (CommitmentInterface.forfeiture setup.program)).flagRestriction
    setup.excludedFlag setup.exclusionMenu setup.exclusionMenu_adequate
    (small := setup.intendedAvailable)
    (smallIncluded := setup.intendedAvailable_subset _)
    (smallProgress := setup.intendedProgress _)
    setup.intendedMenu
    (by
      intro who state trace choice
      have adequate := setup.intendedMenu_adequate who trace choice
      rw [show (setup.informationModel (CommitmentInterface.values setup.program)).infoOf
        who (restrictAvailable.trace
          (E := setup.executionProtocol (CommitmentInterface.values setup.program))
          (included := setup.intendedAvailable_subset
            (CommitmentInterface.values setup.program))
          (progress := setup.intendedProgress (CommitmentInterface.values setup.program)) trace) =
            setup.protocolObserve who state from
          setup.protocol_info _ who _] at adequate
      rw [show (setup.informationModel (CommitmentInterface.forfeiture setup.program)).infoOf who
        (restrictAvailable.trace trace) = setup.protocolObserve who state from
          setup.protocol_info _ who _]
      exact adequate)
    (fun trace who _ offered =>
      ⟨setup.intendedAvailable_subset _ _ who offered, fun excluded =>
        (setup.not_excludedState_of_intendedState (setup.intendedState_trace wellFormed trace) who
          excluded).elim⟩)
    (by
      intro who state trace
      rw [show (setup.informationModel (CommitmentInterface.forfeiture setup.program)).infoOf who
        (restrictAvailable.trace trace) = setup.protocolObserve who state from
          setup.protocol_info _ who _]
      exact setup.excludedFlag_observe_eq_false
        (setup.not_excludedState_of_intendedState (setup.intendedState_trace wellFormed trace) who))
    (setup.intendedMenu_subset _)

@[simp] theorem exclusionRestriction_site (wellFormed : setup.WellFormed) (who : Player)
    (site : setup.intendedModel.InformationSite who) :
    ((setup.exclusionRestriction wellFormed).site who site).1 = (site.1, false) := rfl

/-- An exclusion history leaves a player its source view, flagged with whether
it is excluded. -/
theorem exclusion_info (who : Player) {state : setup.ProtocolState}
    (trace : setup.exclusionProtocol.Trace state) :
    setup.exclusionModel.infoOf who trace =
      (setup.protocolObserve who state,
        setup.excludedFlag who (setup.protocolObserve who state)) := by
  refine (InformationModel.flagMenu_infoOf
    (setup.informationModel (CommitmentInterface.forfeiture setup.program)) setup.excludedFlag
    setup.exclusionMenu setup.exclusionMenu_adequate who trace).trans ?_
  rw [show (setup.informationModel (CommitmentInterface.forfeiture setup.program)).infoOf who
      (restrictAvailable.trace trace) = setup.protocolObserve who state from
        setup.protocol_info _ who _]

/-- At an information value of the exclusion game with an unset flag, its
owner is not excluded. -/
theorem not_excludedState_of_unset (who : Player) {state : setup.ProtocolState}
    (trace : setup.exclusionProtocol.Trace state)
    (unset : (setup.exclusionModel.infoOf who trace).2 = false) :
    ¬ setup.ExcludedState who state := by
  intro excluded
  rw [setup.exclusion_info, (setup.excludedFlag_observe_eq_true who state).mpr excluded] at unset
  cases unset

/-- **Retained sites are honest.** At every exclusion history of an embedded
intended decision site, the owner is not excluded: no own binding failed and no
own publication failed. -/
theorem not_excludedState_of_retained (wellFormed : setup.WellFormed) (who : Player)
    (site : setup.intendedModel.InformationSite who)
    (history : setup.exclusionModel.InformationHistory who
      ((setup.exclusionRestriction wellFormed).site who site).1) :
    ¬ setup.ExcludedState who history.1.state :=
  setup.not_excludedState_of_unset who history.1.trace (by rw [history.2]; rfl)

/-- **Deviations are excluded.** After a source action that the intended game
does not offer at one of its decision sites, every terminal continuation of the
exclusion game records a failed reveal of the deviating player, whatever anyone
plays. -/
theorem exclusion_deviation_failedReveals_pos [Fintype Player] (wellFormed : setup.WellFormed)
    (certificate : setup.exclusionProtocol.WellFoundedHistories)
    [∀ who, DecidableEq (setup.exclusionModel.InfoState who)]
    (profile : ∀ who, setup.exclusionModel.BehavioralPolicy who)
    (who : Player) (site : setup.intendedModel.InformationSite who)
    (action : setup.exclusionModel.Choice who
      ((setup.exclusionRestriction wellFormed).site who site).1)
    (extra : action ∉ Set.range ((setup.exclusionRestriction wellFormed).choice who site.1))
    (history : setup.intendedModel.InformationHistory who site.1) :
    ∀ final ∈ (setup.exclusionModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.exclusionModel.behavioralSignature) profile who
          ((profile who).commit ((setup.exclusionRestriction wellFormed).site who site).1
            action))
        ((setup.exclusionRestriction wellFormed).history history.1)).support,
      ∃ terminal, setup.protocolReadout final.state = some terminal ∧
        1 ≤ failedReveals setup.program who (publicOutcome setup.program terminal) := by
  intro final supported
  let restriction := setup.exclusionRestriction wellFormed
  let model := setup.exclusionModel
  let deviating := Profile.update (sig := model.behavioralSignature) profile who
    ((profile who).commit (restriction.site who site).1 action)
  have active : setup.exclusionProtocol.active history.1.state who :=
    InformationModel.InformationSite.active (M := setup.intendedModel) site history
  have running : ¬ setup.exclusionProtocol.terminal (restriction.history history.1).state :=
    setup.not_terminal_of_active (CommitmentInterface.forfeiture setup.program) active
  change final ∈ (model.runBehavioralTerminalFrom certificate deviating
    (restriction.history history.1)).support at supported
  rw [InformationModel.runBehavioralTerminalFrom_of_not_terminal _ _ _ running,
    PMF.support_bind] at supported
  obtain ⟨draw, drawn, continued⟩ := Set.mem_iUnion₂.mp supported
  rw [PMF.mem_support_bindOnSupport_iff] at continued
  obtain ⟨target, realized, child⟩ := continued
  have chosen : draw.1 who = action.1 := by
    have marginal : draw.1 ∈ ((model.behavioralJoint deviating
        (restriction.history history.1).trace running).map Subtype.val).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨draw, drawn, rfl⟩
    rw [model.behavioralJoint_map_val, independentProduct_support_iff] at marginal
    have own := marginal who
    have info : model.infoOf who (restriction.history history.1).trace =
        (restriction.site who site).1 :=
      (restriction.observed who history.1).trans
        (congrArg (restriction.information who) history.2)
    rw [info] at own
    simpa [deviating, Profile.update_same, InformationModel.BehavioralPolicy.commit_self,
      PMF.pure_map] using own
  have siteView : site.1 = setup.protocolObserve who history.1.state :=
    history.2.symm.trans (setup.intended_info who history.1.trace)
  have notIntended : action.1 ∉ setup.intendedMenu who site.1 := by
    intro permitted
    apply extra
    exact ⟨⟨action.1, permitted⟩, Subtype.ext rfl⟩
  rw [siteView] at notIntended
  have permitted := draw.2.2 who
  rw [chosen] at permitted
  cases offered : action.1 with
  | none =>
      rw [offered] at permitted
      exact (permitted active).elim
  | some chosenAction =>
      rw [offered] at notIntended
      have owed := setup.owesFailureState_of_deviation
        (CommitmentInterface.forfeiture setup.program) who
        (setup.intendedState_trace wellFormed history.1.trace) draw.1
        (restrictAvailable.legal draw.2) (chosen.trans offered) notIntended target realized
      have finalOwed := model.runBehavioralTerminalFrom_support_closed certificate deviating
        (setup.OwesFailureState who) (fun state joint legal target owed reached =>
          setup.owesFailureState_step who _ state joint (restrictAvailable.legal legal) target
            owed reached)
        _ owed final child
      have stopped := model.runBehavioralTerminalFrom_support_terminal certificate deviating _
        final child
      cases finalState : final.state with
      | none =>
          rw [finalState] at finalOwed
          exact finalOwed.elim
      | some state =>
          rw [finalState] at finalOwed stopped
          obtain ⟨terminal, read⟩ :=
            ProtocolState.exists_readout_of_terminal setup.program state stopped
          exact ⟨terminal, read,
            ProtocolState.failedReveals_pos_of_owesFailure who setup.program state
              finalOwed read⟩

/-- **Intended equilibria extend to the exclusion game.** For a well-formed
setup with finite commitment payload types and a finite initial law, and an
exclusion payoff for each player no larger than any of its intended terminal
payoffs, every sequential equilibrium of the intended game extends to a
sequential equilibrium of the source game with exclusion. The extension plays
the intended laws and keeps the intended beliefs at every intended decision
site, and has the intended joint law of terminal store and payoff. -/
theorem intended_sequentialEquilibrium_extends_to_exclusion [Fintype Player]
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
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
              (fun state => utility (setup.parameterOutcome parameter state) who))) := by
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
  obtain ⟨target, sequential, agrees, beliefs, _, jointLaw⟩ :=
    restriction.sequentialEquilibrium_extends_of_comparator_unclocked
      setup.intended_decision_antichain intendedTerminates exclusionTerminates
      (setup.exclusionReference finite) (setup.exclusionReference_fullyMixed finite)
      setup.exclusion_decisionRecall intendedPayoff exclusionPayoff matching comparator
      (by
        intro sourceProfile targetProfile _ who site action extra history
        have deviation := setup.exclusion_deviation_failedReveals_pos wellFormed
          exclusionTerminates targetProfile who site action extra history
        calc _ = expect (setup.intendedModel.runBehavioralTerminalFrom intendedTerminates
                (Profile.update (sig := setup.intendedModel.behavioralSignature) sourceProfile who
                  ((sourceProfile who).withLaw site.1 (comparator who site action)))
                history.1)
              (fun _ => expect (setup.exclusionModel.runBehavioralTerminalFrom
                  exclusionTerminates
                  (Profile.update (sig := setup.exclusionModel.behavioralSignature)
                    targetProfile who
                    ((targetProfile who).commit (restriction.site who site).1 action))
                  (restriction.history history.1))
                  (exclusionPayoff who)) :=
              (expect_constant _ _).symm
          _ ≤ _ := by
            refine expect_mono (fun reached supported => ?_) (payoffIntegrable_constant _ _)
              (payoffIntegrable_of_finite _ _)
            obtain ⟨intendedTerminal, intendedRead⟩ :=
              setup.exists_protocolReadout_of_terminal (CommitmentInterface.values setup.program)
                (setup.intendedModel.runBehavioralTerminalFrom_support_terminal intendedTerminates
                  _ _ reached supported)
            refine expect_le_const _ _ (payoffIntegrable_of_finite _ _) _ (fun final deviated => ?_)
            obtain ⟨terminal, read, positive⟩ := deviation final deviated
            change (setup.protocolReadout final.state).elim 0 _ ≤
              (setup.protocolReadout reached.state).elim 0 _
            rw [read, intendedRead]
            change exclusionUtility setup.program excludedPayoff utility
              (setup.parameterOutcome parameter terminal) who ≤
                utility (setup.parameterOutcome parameter intendedTerminal) who
            rw [exclusionUtility_of_failedReveals_pos _ _ _ positive]
            exact below reached intendedTerminal intendedRead who)
      intended equilibrium
  refine ⟨target, sequential, agrees, beliefs, ?_⟩
  have readouts := congrArg (PMF.map fun pair => (setup.protocolReadout pair.1.state, pair.2))
    jointLaw
  simp only [PMF.map_comp] at readouts
  exact readouts.symm

end Vegas.SourceProgram.Setup
