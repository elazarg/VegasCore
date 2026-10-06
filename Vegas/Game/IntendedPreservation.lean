/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.IntendedPlay
import Vegas.Source.SetupProtocolRecall
import Vegas.Game.SourceInformation
import GameTheoryExtensions.Analysis.Protocol.PassageRestrictionExtension

/-! # Intended-game preservation

The intended game of a well-formed setup offers only predicted values at
commits and only opening at reveals (`Vegas.SourceProgram.Setup.intendedModel`).
The forfeit pass charges the owner of every failed reveal a forfeit above the
payoff range (`Vegas.SourceProgram.forfeitUtility`). Every sequential equilibrium
of the intended game then extends to a sequential equilibrium of the source
game under the forfeited utility, with the same joint law of terminal store and
payoff and no failed reveal on any path it reaches
(`Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_preserved`).

The extension is the action-restriction extension of the library. No reveal of
the intended game fails (`Vegas.SourceProgram.Setup.failedReveals_eq_zero_of_intendedState`),
so the two utilities agree on embedded histories. A source action the intended
game does not offer leaves its author indebted
(`Vegas.SourceProgram.ProtocolState.indebted_of_deviation`), and every terminal
continuation then records a failed reveal of that author, whatever anyone plays
(`Vegas.SourceProgram.Setup.deviation_failedReveals_pos`); the forfeit above the
payoff range makes every intended choice at least as good.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

section Support

variable {ι : Type*} [Fintype ι] {E : ExecutionProtocol ι}

/-- Terminal play stays in every set of states closed under legal steps. -/
private theorem runBehavioralTerminalFrom_support_closed (M : InformationModel E)
    (certificate : E.WellFoundedHistories) (policies : (i : ι) → M.BehavioralPolicy i)
    (closed : E.State → Prop)
    (step : ∀ state joint (legal : E.Legal state joint) target, closed state →
      target ∈ (E.step state ⟨joint, legal⟩).support → closed target)
    (history : E.History) (holds : closed history.state) :
    ∀ final ∈ (M.runBehavioralTerminalFrom certificate policies history).support,
      closed final.state := by
  induction history using certificate.induction with
  | _ current ih =>
      intro final supported
      by_cases stopped : E.terminal current.state
      · rw [InformationModel.runBehavioralTerminalFrom, E.randomizedBackwardLaw_of_terminal stopped,
          PMF.mem_support_pure_iff] at supported
        subst supported
        exact holds
      · rw [InformationModel.runBehavioralTerminalFrom,
          E.randomizedBackwardLaw_of_not_terminal stopped, PMF.support_bind] at supported
        obtain ⟨drawn, _, continued⟩ := Set.mem_iUnion₂.mp supported
        rw [PMF.mem_support_bindOnSupport_iff] at continued
        obtain ⟨target, realized, child⟩ := continued
        exact ih (current.extend drawn.2 realized) ⟨drawn.1, drawn.2, realized⟩
          (step _ _ drawn.2 _ holds realized) final child

end Support

variable (setup : Setup (Player := Player) (L := L))

/-- A setup protocol state the intended game can be in. -/
def IntendedState : setup.ProtocolState → Prop
  | none => True
  | some state => ProtocolState.Intended setup.program state

/-- A setup protocol state at which `who` owes a failed reveal. -/
def IndebtedState (who : Player) : setup.ProtocolState → Prop
  | none => False
  | some state => ProtocolState.Indebted who setup.program state

theorem initialConfig_intended (wellFormed : setup.WellFormed) {initial : State L setup.context}
    (supported : initial ∈ setup.initialLaw.support) :
    (setup.initialConfig initial).Intended setup.obligations where
  unique := setup.namesNodup
  accounted := by
    rw [setup.accounts]
    exact Accounted.initial setup.context
  bound := wellFormed.initialValues initial supported
  publishes _ _ _ _ revealed := by
    simp [initialConfig, Revelations.initial, Revelation.isRevealed] at revealed
  predicted _ member := by simp [initialConfig] at member

/-- Every history of the intended game ends in a state of the intended game. -/
theorem intendedState_trace (wellFormed : setup.WellFormed) :
    ∀ {state} (_ : setup.intendedProtocol.Trace state), setup.IntendedState state
  | _, .start => trivial
  | _, .extend (source := before) prior joint legal realized => by
      have earlier := intendedState_trace wellFormed prior
      cases before with
      | none =>
          change _ ∈ (setup.initialLaw.map fun initial =>
            some (ProtocolState.entry setup.program (setup.initialConfig initial))).support
              at realized
          rw [PMF.support_map] at realized
          obtain ⟨initial, supported, rfl⟩ := realized
          exact ProtocolState.intended_entry setup.program _
            (setup.initialConfig_intended wellFormed supported)
            (wellFormed.guardsSatisfiable initial supported)
      | some before =>
          change _ ∈ ((ProtocolState.step setup.program before joint).map some).support
            at realized
          rw [PMF.support_map] at realized
          obtain ⟨after, reached, rfl⟩ := realized
          refine ProtocolState.intended_step setup.program before joint after earlier
            (fun who => ?_) reached
          have permitted := legal.2 who
          revert permitted
          cases joint who <;> exact id

/-- No reveal of the intended game fails. -/
theorem failedReveals_eq_zero_of_intendedState {state : setup.ProtocolState}
    (intended : setup.IntendedState state) (who : Player)
    {terminal : State L setup.program.terminalCtx}
    (read : setup.protocolReadout state = some terminal) :
    failedReveals setup.program who (publicOutcome setup.program terminal) = 0 := by
  cases state with
  | none => cases read
  | some state =>
      exact ProtocolState.failedReveals_eq_zero_of_intended who setup.program state intended read

theorem indebtedState_step (who : Player) (admission : CommitmentInterface setup.program)
    (state : setup.ProtocolState) (joint : Player → Option (OwnAction Player L))
    (legal : (setup.executionProtocol admission).Legal state joint)
    (target : setup.ProtocolState) (indebted : setup.IndebtedState who state)
    (reached : target ∈ ((setup.executionProtocol admission).step state ⟨joint, legal⟩).support) :
    setup.IndebtedState who target := by
  cases state with
  | none => exact indebted.elim
  | some state =>
      change target ∈ ((ProtocolState.step setup.program state joint).map some).support
        at reached
      rw [PMF.support_map] at reached
      obtain ⟨after, supported, rfl⟩ := reached
      exact ProtocolState.indebted_step who setup.program state joint after indebted supported

/-- A step on which `who` takes a source action outside the intended menu
leaves `who` indebted. -/
theorem indebtedState_of_deviation (who : Player) {state : setup.ProtocolState}
    (intended : setup.IntendedState state) (joint : Player → Option (OwnAction Player L))
    (legal : (setup.executionProtocol (CommitmentInterface.values setup.program)).Legal state joint)
    {action : OwnAction Player L} (chosen : joint who = some action)
    (new : some action ∉ setup.intendedMenu who (setup.protocolObserve who state))
    (target : setup.ProtocolState)
    (reached : target ∈ ((setup.executionProtocol (CommitmentInterface.values setup.program)).step
      state ⟨joint, legal⟩).support) :
    setup.IndebtedState who target := by
  have permitted := legal.2 who
  rw [chosen] at permitted
  cases state with
  | none => exact permitted.1.elim
  | some state =>
      change target ∈ ((ProtocolState.step setup.program state joint).map some).support
        at reached
      rw [PMF.support_map] at reached
      obtain ⟨after, supported, rfl⟩ := reached
      exact ProtocolState.indebted_of_deviation who setup.program _ (fun _ => rfl) state
        intended joint action chosen permitted.1 permitted.2
        (fun offered => new ⟨permitted.1, offered⟩) after supported

theorem exists_protocolReadout_of_terminal (admission : CommitmentInterface setup.program)
    {state : setup.ProtocolState} (stopped : (setup.executionProtocol admission).terminal state) :
    ∃ terminal, setup.protocolReadout state = some terminal := by
  cases state with
  | none => exact stopped.elim
  | some state => exact ProtocolState.exists_readout_of_terminal setup.program state stopped

theorem not_terminal_of_active (admission : CommitmentInterface setup.program)
    {state : setup.ProtocolState} {who : Player}
    (active : (setup.executionProtocol admission).active state who) :
    ¬ (setup.executionProtocol admission).terminal state := by
  cases state with
  | none => exact active.elim
  | some state =>
      intro stopped
      have inactive := ProtocolState.terminal_actor_none who setup.program state stopped
      change ProtocolView.actor who setup.program (ProtocolState.observe who setup.program state) =
        some who at active
      rw [inactive] at active
      cases active

theorem intended_info (who : Player) {state : setup.ProtocolState}
    (trace : setup.intendedProtocol.Trace state) :
    setup.intendedModel.infoOf who trace = setup.protocolObserve who state :=
  ((setup.informationModel _).restrictMenu_infoOf _ _ who trace).trans
    (setup.protocol_info _ who _)

theorem intended_decision_antichain : setup.intendedModel.DecisionInformationAntichain :=
  (setup.informationModel _).restrictMenu_decisionInformationAntichain _ _
    (setup.protocol_perfectRecall _)

theorem intended_bounded :
    setup.intendedProtocol.BoundedHorizon (instructionCount setup.program + 1) :=
  restrictAvailable.boundedHorizon (setup.protocol_bounded _)

/-- **Deviations forfeit.** After a source action that the intended game does
not offer at one of its decision sites, every terminal continuation records a
failed reveal of the deviating player, whatever anyone plays. -/
theorem deviation_failedReveals_pos [Fintype Player] (wellFormed : setup.WellFormed)
    (certificate :
      (setup.executionProtocol (CommitmentInterface.values setup.program)).WellFoundedHistories)
    [∀ who, DecidableEq
      ((setup.informationModel (CommitmentInterface.values setup.program)).InfoState who)]
    (profile : ∀ who,
      (setup.informationModel (CommitmentInterface.values setup.program)).BehavioralPolicy who)
    (who : Player) (site : setup.intendedModel.InformationSite who)
    (action : (setup.informationModel (CommitmentInterface.values setup.program)).Choice who
      (setup.intendedRestriction.site who site).1)
    (extra : action ∉ Set.range (setup.intendedRestriction.choice who site.1))
    (history : setup.intendedModel.InformationHistory who site.1) :
    ∀ final ∈ ((setup.informationModel
        (CommitmentInterface.values setup.program)).runBehavioralTerminalFrom certificate
        (Profile.update
          (sig := (setup.informationModel
            (CommitmentInterface.values setup.program)).behavioralSignature) profile who
          ((profile who).commit (setup.intendedRestriction.site who site).1 action))
        (setup.intendedRestriction.history history.1)).support,
      ∃ terminal, setup.protocolReadout final.state = some terminal ∧
        1 ≤ failedReveals setup.program who (publicOutcome setup.program terminal) := by
  intro final supported
  let model := setup.informationModel (CommitmentInterface.values setup.program)
  let deviating := Profile.update (sig := model.behavioralSignature) profile who
    ((profile who).commit (setup.intendedRestriction.site who site).1 action)
  have active : (setup.executionProtocol
      (CommitmentInterface.values setup.program)).active history.1.state who :=
    InformationModel.InformationSite.active (M := setup.intendedModel) site history
  have running := setup.not_terminal_of_active _ active
  change final ∈ (model.runBehavioralTerminalFrom certificate deviating
    (restrictAvailable.history history.1)).support at supported
  rw [InformationModel.runBehavioralTerminalFrom_of_not_terminal _ _ _ running,
    PMF.support_bind] at supported
  obtain ⟨draw, drawn, continued⟩ := Set.mem_iUnion₂.mp supported
  rw [PMF.mem_support_bindOnSupport_iff] at continued
  obtain ⟨target, realized, child⟩ := continued
  have chosen : draw.1 who = action.1 := by
    have marginal : draw.1 ∈ ((model.behavioralJoint deviating
        (restrictAvailable.history history.1).trace running).map Subtype.val).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨draw, drawn, rfl⟩
    rw [model.behavioralJoint_map_val, independentProduct_support_iff] at marginal
    have own := marginal who
    have info : model.infoOf who (restrictAvailable.history history.1).trace =
        (setup.intendedRestriction.site who site).1 :=
      (setup.intendedRestriction.observed who history.1).trans
        (congrArg (setup.intendedRestriction.information who) history.2)
    rw [info] at own
    simpa [deviating, Profile.update_same, InformationModel.BehavioralPolicy.commit_self,
      PMF.pure_map] using own
  have siteView : site.1 = setup.protocolObserve who history.1.state :=
    history.2.symm.trans (setup.intended_info who history.1.trace)
  have notIntended : action.1 ∉ setup.intendedMenu who site.1 :=
    model.menuRestriction_extra_choice setup.intendedMenu setup.intendedMenu_adequate
      setup.intendedMenu_subset who site.1 action extra
  rw [siteView] at notIntended
  have permitted := draw.2.2 who
  rw [chosen] at permitted
  cases offered : action.1 with
  | none =>
      rw [offered] at permitted
      exact (permitted active).elim
  | some chosenAction =>
      rw [offered] at notIntended
      have indebted := setup.indebtedState_of_deviation who
        (setup.intendedState_trace wellFormed history.1.trace) draw.1 draw.2
        (chosen.trans offered) notIntended target realized
      have finalIndebted := runBehavioralTerminalFrom_support_closed model certificate deviating
        (setup.IndebtedState who) (fun state joint legal target indebted reached =>
          setup.indebtedState_step who _ state joint legal target indebted reached)
        _ indebted final child
      have stopped := model.runBehavioralTerminalFrom_support_terminal certificate deviating _
        final child
      cases finalState : final.state with
      | none =>
          rw [finalState] at finalIndebted
          exact finalIndebted.elim
      | some state =>
          rw [finalState] at finalIndebted stopped
          obtain ⟨terminal, read⟩ :=
            ProtocolState.exists_readout_of_terminal setup.program state stopped
          exact ⟨terminal, read,
            ProtocolState.failedReveals_pos_of_indebted who setup.program state finalIndebted read⟩

/-- **Intended-game preservation.** For a well-formed setup with finite
commitment payload types and a finite initial law, every sequential equilibrium
of the intended game has a sequential equilibrium of the source game under the
forfeit pass, with a forfeit no smaller than the payoff range. The source
equilibrium has the intended joint law of terminal store and payoff, and no
reveal fails on any history it reaches. -/
theorem intended_sequentialEquilibrium_preserved [Fintype Player]
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (forfeit : ℝ) (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (intendedTerminates : setup.intendedProtocol.WellFoundedHistories)
    (sourceTerminates :
      (setup.executionProtocol (CommitmentInterface.values setup.program)).WellFoundedHistories)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      intendedTerminates
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who))) :
    ∃ target : (setup.informationModel
        (CommitmentInterface.values setup.program)).BehavioralAssessment,
      target.IsSequentialEquilibrium (setup.decision_antichain _) sourceTerminates
        (fun who final => (setup.protocolReadout final.state).elim 0
          (fun state => forfeitUtility setup.program forfeit utility
            (setup.parameterOutcome parameter state) who)) ∧
      (∀ final ∈ ((setup.informationModel
          (CommitmentInterface.values setup.program)).runBehavioralTerminalFrom sourceTerminates
            target.strategy
            (setup.executionProtocol
              (CommitmentInterface.values setup.program)).initHistory).support,
        ∀ terminal, setup.protocolReadout final.state = some terminal →
          ∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0) ∧
      ((setup.informationModel
          (CommitmentInterface.values setup.program)).runBehavioralTerminalFrom sourceTerminates
            target.strategy
            (setup.executionProtocol (CommitmentInterface.values setup.program)).initHistory).map
          (fun final => (setup.protocolReadout final.state,
            fun who => (setup.protocolReadout final.state).elim 0
              (fun state => forfeitUtility setup.program forfeit utility
                (setup.parameterOutcome parameter state) who))) =
        (setup.intendedModel.runBehavioralTerminalFrom intendedTerminates intended.strategy
            setup.intendedProtocol.initHistory).map
          (fun final => (setup.protocolReadout final.state,
            fun who => (setup.protocolReadout final.state).elim 0
              (fun state => utility (setup.parameterOutcome parameter state) who))) := by
  classical
  have : Finite (setup.executionProtocol (CommitmentInterface.values setup.program)).History :=
    setup.finite_history finite _
  have : Finite setup.intendedProtocol.History :=
    Finite.of_injective setup.intendedRestriction.history
      setup.intendedRestriction.history.injective
  let intendedPayoff : Player → setup.intendedProtocol.History → ℝ :=
    fun who final => (setup.protocolReadout final.state).elim 0
      (fun state => utility (setup.parameterOutcome parameter state) who)
  let sourcePayoff : Player →
      (setup.executionProtocol (CommitmentInterface.values setup.program)).History → ℝ :=
    fun who final => (setup.protocolReadout final.state).elim 0
      (fun state => forfeitUtility setup.program forfeit utility
        (setup.parameterOutcome parameter state) who)
  have matching : ∀ who (history : setup.intendedProtocol.History),
      sourcePayoff who (setup.intendedRestriction.history history) =
        intendedPayoff who history := by
    intro who history
    change (setup.protocolReadout history.state).elim 0 _ =
      (setup.protocolReadout history.state).elim 0 _
    cases read : setup.protocolReadout history.state with
    | none => rfl
    | some terminal =>
        have zero := setup.failedReveals_eq_zero_of_intendedState
          (setup.intendedState_trace wellFormed history.trace) who read
        change forfeitUtility setup.program forfeit utility
          (setup.parameterOutcome parameter terminal) who =
            utility (setup.parameterOutcome parameter terminal) who
        simp only [forfeitUtility, parameterOutcome] at zero ⊢
        simp [zero]
  let comparator : ∀ who (site : setup.intendedModel.InformationSite who),
      (setup.informationModel (CommitmentInterface.values setup.program)).Choice who
        (setup.intendedRestriction.site who site).1 →
        PMF (setup.intendedModel.Choice who site.1) :=
    fun _ _ _ => PMF.pure (Classical.arbitrary _)
  obtain ⟨target, sequential, _, _, historyLaw, jointLaw⟩ :=
    setup.intendedRestriction.sequentialEquilibrium_extends_of_comparator_unclocked
      setup.intended_decision_antichain intendedTerminates sourceTerminates
      (setup.uniformReference finite _) (setup.uniformReference_fullyMixed finite _)
      (setup.protocol_decisionRecall _) intendedPayoff sourcePayoff matching comparator
      (by
        intro sourceProfile targetProfile _ who site action extra history
        have deviation := setup.deviation_failedReveals_pos wellFormed sourceTerminates
          targetProfile who site action extra history
        calc _ = expect (setup.intendedModel.runBehavioralTerminalFrom intendedTerminates
                (Profile.update (sig := setup.intendedModel.behavioralSignature) sourceProfile who
                  ((sourceProfile who).withLaw site.1 (comparator who site action)))
                history.1)
              (fun _ => expect ((setup.informationModel
                (CommitmentInterface.values setup.program)).runBehavioralTerminalFrom
                  sourceTerminates
                  (Profile.update (sig := (setup.informationModel
                    (CommitmentInterface.values setup.program)).behavioralSignature)
                    targetProfile who
                    ((targetProfile who).commit (setup.intendedRestriction.site who site).1
                      action))
                  (setup.intendedRestriction.history history.1)) (sourcePayoff who)) :=
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
            change forfeitUtility setup.program forfeit utility
              (setup.parameterOutcome parameter terminal) who ≤
                utility (setup.parameterOutcome parameter intendedTerminal) who
            have spread := range (setup.parameterOutcome parameter terminal)
              (setup.parameterOutcome parameter intendedTerminal) who
            have nonnegative := range (setup.parameterOutcome parameter terminal)
              (setup.parameterOutcome parameter terminal) who
            have count : (1 : ℝ) ≤ (failedReveals setup.program who
                (setup.parameterOutcome parameter terminal).2 : ℝ) :=
              Nat.one_le_cast.mpr positive
            simp only [forfeitUtility]
            nlinarith)
      intended equilibrium
  refine ⟨target, sequential, ?_, ?_⟩
  · intro final reached terminal read who
    rw [← historyLaw, PMF.support_map] at reached
    obtain ⟨intendedFinal, _, rfl⟩ := reached
    exact setup.failedReveals_eq_zero_of_intendedState
      (setup.intendedState_trace wellFormed intendedFinal.trace) who read
  · have readouts := congrArg (PMF.map fun pair => (setup.protocolReadout pair.1.state, pair.2))
      jointLaw
    simp only [PMF.map_comp] at readouts
    exact readouts.symm

end Vegas.SourceProgram.Setup
