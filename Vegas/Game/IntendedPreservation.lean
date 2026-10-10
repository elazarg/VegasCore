/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.IntendedPlay
import Vegas.Source.FailedBindingDeviation
import Vegas.Source.AdmissionRestriction
import Vegas.Source.SetupProtocolRecall
import Vegas.Game.SourceInformation
import GameTheoryExtensions.Analysis.Protocol.PassageRestrictionExtension
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Intended-game preservation

The intended game of a well-formed setup offers only predicted values at
commits and only opening at reveals (`Vegas.SourceProgram.Setup.intendedModel`).
The forfeit pass charges the owner of every failed reveal a forfeit above the
payoff range (`Vegas.SourceProgram.forfeitUtility`). Every sequential equilibrium
of the intended game then extends to a sequential equilibrium of the source
game under any sitewise commitment admission and the forfeited utility,
including immediate failed bindings, with the same joint law of terminal store and
payoff and no failed reveal on any path it reaches
(`Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_preserved`).

The extension is the action-restriction extension of the library. No reveal of
the intended game fails (`Vegas.SourceProgram.Setup.failedReveals_eq_zero_of_intendedState`),
so the two utilities agree on embedded histories. A source action the intended
game does not offer leaves its author owing a failed reveal
(`Vegas.SourceProgram.ProtocolState.owesFailure_of_deviation`), and every terminal
continuation then records a failed reveal of that author, whatever anyone plays
(`Vegas.SourceProgram.Setup.deviation_failedReveals_pos`); the forfeit above the
payoff range makes every intended choice at least as good.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable (setup : Setup (Player := Player) (L := L))

/-- A setup protocol state the intended game can be in. -/
def IntendedState : setup.ProtocolState → Prop
  | none => True
  | some state => ProtocolState.Intended setup.program state

/-- A setup protocol state at which `who` owes a failed reveal. -/
def IndebtedState (who : Player) : setup.ProtocolState → Prop
  | none => False
  | some state => ProtocolState.Indebted who setup.program state

/-- A source position whose continuation necessarily fails an own reveal,
through guard rejection, withholding or irrevocable failed binding. -/
def OwesFailureState (who : Player) : setup.ProtocolState → Prop
  | none => False
  | some state => ProtocolState.OwesFailure who setup.program state

theorem owesFailureState_step (who : Player) (admission : CommitmentInterface setup.program)
    (state : setup.ProtocolState) (joint : Player → Option (OwnAction Player L))
    (legal : (setup.executionProtocol admission).Legal state joint)
    (target : setup.ProtocolState) (owed : setup.OwesFailureState who state)
    (reached : target ∈ ((setup.executionProtocol admission).step state ⟨joint, legal⟩).support) :
    setup.OwesFailureState who target := by
  cases state with
  | none => exact owed.elim
  | some state =>
      change target ∈ ((ProtocolState.step setup.program state joint).map some).support at reached
      rw [PMF.support_map] at reached
      obtain ⟨after, supported, rfl⟩ := reached
      exact ProtocolState.owesFailure_step who setup.program state joint after owed supported

theorem owesFailureState_of_deviation (admission : CommitmentInterface setup.program)
    (who : Player) {state : setup.ProtocolState} (intended : setup.IntendedState state)
    (joint : Player → Option (OwnAction Player L))
    (legal : (setup.executionProtocol admission).Legal state joint)
    {action : OwnAction Player L} (chosen : joint who = some action)
    (new : some action ∉ setup.intendedMenu who (setup.protocolObserve who state))
    (target : setup.ProtocolState)
    (reached : target ∈ ((setup.executionProtocol admission).step state ⟨joint, legal⟩).support) :
    setup.OwesFailureState who target := by
  have permitted := legal.2 who
  rw [chosen] at permitted
  cases state with
  | none => exact permitted.1.elim
  | some state =>
      change target ∈ ((ProtocolState.step setup.program state joint).map some).support at reached
      rw [PMF.support_map] at reached
      obtain ⟨after, supported, rfl⟩ := reached
      exact ProtocolState.owesFailure_of_deviation who setup.program admission state intended
        joint action chosen permitted.1 permitted.2
        (fun offered => new ⟨permitted.1, offered⟩) after supported

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
theorem deviation_failedReveals_pos [Fintype Player]
    (admission : CommitmentInterface setup.program) (wellFormed : setup.WellFormed)
    (certificate :
      (setup.executionProtocol admission).WellFoundedHistories)
    [∀ who, DecidableEq
      ((setup.informationModel admission).InfoState who)]
    (profile : ∀ who,
      (setup.informationModel admission).BehavioralPolicy who)
    (who : Player) (site : setup.intendedModel.InformationSite who)
    (action : (setup.informationModel admission).Choice who
      ((setup.intendedRestriction admission).site who site).1)
    (extra : action ∉ Set.range ((setup.intendedRestriction admission).choice who site.1))
    (history : setup.intendedModel.InformationHistory who site.1) :
    ∀ final ∈ ((setup.informationModel
        admission).runBehavioralTerminalFrom certificate
        (Profile.update
          (sig := (setup.informationModel
            admission).behavioralSignature) profile who
          ((profile who).commit
            ((setup.intendedRestriction admission).site who site).1 action))
        ((setup.intendedRestriction admission).history history.1)).support,
      ∃ terminal, setup.protocolReadout final.state = some terminal ∧
        1 ≤ failedReveals setup.program who (publicOutcome setup.program terminal) := by
  intro final supported
  let model := setup.informationModel admission
  let deviating := Profile.update (sig := model.behavioralSignature) profile who
    ((profile who).commit ((setup.intendedRestriction admission).site who site).1 action)
  have active : (setup.executionProtocol
      admission).active history.1.state who :=
    InformationModel.InformationSite.active (M := setup.intendedModel) site history
  have running := setup.not_terminal_of_active _ active
  change final ∈ (model.runBehavioralTerminalFrom certificate deviating
    ((setup.intendedRestriction admission).history history.1)).support at supported
  rw [InformationModel.runBehavioralTerminalFrom_of_not_terminal _ _ _ running,
    PMF.support_bind] at supported
  obtain ⟨draw, drawn, continued⟩ := Set.mem_iUnion₂.mp supported
  rw [PMF.mem_support_bindOnSupport_iff] at continued
  obtain ⟨target, realized, child⟩ := continued
  have chosen : draw.1 who = action.1 := by
    have marginal : draw.1 ∈ ((model.behavioralJoint deviating
        ((setup.intendedRestriction admission).history history.1).trace running).map
          Subtype.val).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨draw, drawn, rfl⟩
    rw [model.behavioralJoint_map_val, independentProduct_support_iff] at marginal
    have own := marginal who
    have info : model.infoOf who
        ((setup.intendedRestriction admission).history history.1).trace =
        ((setup.intendedRestriction admission).site who site).1 :=
      ((setup.intendedRestriction admission).observed who history.1).trans
        (congrArg ((setup.intendedRestriction admission).information who) history.2)
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
      have indebted := setup.owesFailureState_of_deviation admission who
        (setup.intendedState_trace wellFormed history.1.trace) draw.1 draw.2
        (chosen.trans offered) notIntended target realized
      have finalIndebted := model.runBehavioralTerminalFrom_support_closed certificate deviating
        (setup.OwesFailureState who) (fun state joint legal target indebted reached =>
          setup.owesFailureState_step who _ state joint legal target indebted reached)
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
            ProtocolState.failedReveals_pos_of_owesFailure who setup.program state
              finalIndebted read⟩

/-- **Intended-game preservation.** For a well-formed setup with finite
commitment payload types and a finite initial law, every sequential equilibrium
of the intended game has a sequential equilibrium of the source game under any
sitewise commitment admission and the forfeit pass, with a forfeit no smaller
than the payoff range. The source
equilibrium has the intended joint law of terminal store and payoff, and no
reveal fails on any history it reaches. -/
theorem intended_sequentialEquilibrium_preserved [Fintype Player]
    (admission : CommitmentInterface setup.program)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (forfeit : ℝ) (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (intendedTerminates : setup.intendedProtocol.WellFoundedHistories)
    (sourceTerminates :
      (setup.executionProtocol admission).WellFoundedHistories)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      intendedTerminates
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who))) :
    ∃ target : (setup.informationModel
        admission).BehavioralAssessment,
      target.IsSequentialEquilibrium (setup.decision_antichain _) sourceTerminates
        (fun who final => (setup.protocolReadout final.state).elim 0
          (fun state => forfeitUtility setup.program forfeit utility
            (setup.parameterOutcome parameter state) who)) ∧
      (∀ final ∈ ((setup.informationModel
          admission).runBehavioralTerminalFrom sourceTerminates
            target.strategy
            (setup.executionProtocol
              admission).initHistory).support,
        ∀ terminal, setup.protocolReadout final.state = some terminal →
          ∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0) ∧
      ((setup.informationModel
          admission).runBehavioralTerminalFrom sourceTerminates
            target.strategy
            (setup.executionProtocol admission).initHistory).map
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
  let restriction := setup.intendedRestriction admission
  have : Finite (setup.executionProtocol admission).History :=
    setup.finite_history finite _
  have : Finite setup.intendedProtocol.History :=
    Finite.of_injective restriction.history
      restriction.history.injective
  let intendedPayoff : Player → setup.intendedProtocol.History → ℝ :=
    fun who final => (setup.protocolReadout final.state).elim 0
      (fun state => utility (setup.parameterOutcome parameter state) who)
  let sourcePayoff : Player →
      (setup.executionProtocol admission).History → ℝ :=
    fun who final => (setup.protocolReadout final.state).elim 0
      (fun state => forfeitUtility setup.program forfeit utility
        (setup.parameterOutcome parameter state) who)
  have matching : ∀ who (history : setup.intendedProtocol.History),
      sourcePayoff who (restriction.history history) =
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
      (setup.informationModel admission).Choice who
        (restriction.site who site).1 →
        PMF (setup.intendedModel.Choice who site.1) :=
    fun _ _ _ => PMF.pure (Classical.arbitrary _)
  obtain ⟨target, sequential, _, _, historyLaw, jointLaw⟩ :=
    restriction.sequentialEquilibrium_extends_of_comparator_unclocked
      setup.intended_decision_antichain intendedTerminates sourceTerminates
      (setup.uniformReference finite _) (setup.uniformReference_fullyMixed finite _)
      (setup.protocol_decisionRecall _) intendedPayoff sourcePayoff matching comparator
      (by
        intro sourceProfile targetProfile _ who site action extra history
        have deviation := setup.deviation_failedReveals_pos admission wellFormed sourceTerminates
          targetProfile who site action extra history
        calc _ = expect (setup.intendedModel.runBehavioralTerminalFrom intendedTerminates
                (Profile.update (sig := setup.intendedModel.behavioralSignature) sourceProfile who
                  ((sourceProfile who).withLaw site.1 (comparator who site action)))
                history.1)
              (fun _ => expect ((setup.informationModel
                admission).runBehavioralTerminalFrom
                  sourceTerminates
                  (Profile.update (sig := (setup.informationModel
                    admission).behavioralSignature)
                    targetProfile who
                    ((targetProfile who).commit
                      (restriction.site who site).1
                      action))
                  (restriction.history history.1))
                  (sourcePayoff who)) :=
              (expect_constant _ _).symm
          _ ≤ _ := by
            refine expect_mono (fun reached supported => ?_) (payoffIntegrable_constant _ _)
              (payoffIntegrable_of_finite _ _)
            obtain ⟨intendedTerminal, intendedRead⟩ :=
              setup.exists_protocolReadout_of_terminal admission
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
