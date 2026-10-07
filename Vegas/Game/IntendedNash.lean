/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.IntendedPreservation
import GameTheoryExtensions.Analysis.Protocol.RetainedDeviation

/-! # Approximate Nash equilibrium of the intended game

The intended game restricts the source game's menus (`Vegas.SourceProgram.Setup.intendedModel`).
Under the forfeit pass, with a forfeit no smaller than the payoff range, every
profile of the source game that plays an `ε`-Nash equilibrium of the intended
game at its decision sites is an `ε`-Nash equilibrium of the source game, with
the intended joint law of terminal store and payoff and no failed reveal on any
history it reaches
(`Vegas.SourceProgram.Setup.intended_isεNash_preserved`).

A source deviation is compared with its retained conditional, which plays the
deviation's law conditioned on intended choices at every intended information
value. Every intended history is at least as likely under it; every other
reached history carries the deviator's debt, whose forfeit makes its payoff no
larger than any intended terminal payoff
(`GameTheory.Protocol.InformationModel.ActionRestriction.isεNash_extends_of_debt`).
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable (setup : Setup (Player := Player) (L := L))

/-- The deviator's debt is absorbing in the source model. -/
theorem indebted_localStep (who : Player)
    (history : (setup.executionProtocol (CommitmentInterface.values setup.program)).History)
    (choices : ∀ i, (setup.informationModel (CommitmentInterface.values setup.program)).Choice i
      ((setup.informationModel (CommitmentInterface.values setup.program)).infoOf i
        history.trace))
    (next : (setup.executionProtocol (CommitmentInterface.values setup.program)).History)
    (indebted : setup.IndebtedState who history.state)
    (reached : next ∈ ((setup.informationModel
      (CommitmentInterface.values setup.program)).localStep history choices).support) :
    setup.IndebtedState who next.state := by
  by_cases stopped : (setup.executionProtocol
      (CommitmentInterface.values setup.program)).terminal history.state
  · simp only [InformationModel.localStep, dite_eq_left_of_eq_true (eq_true stopped),
      PMF.mem_support_pure_iff] at reached
    exact reached ▸ indebted
  · simp only [InformationModel.localStep, dite_eq_right_of_eq_false (eq_false stopped),
      PMF.mem_support_bindOnSupport_iff, PMF.mem_support_pure_iff] at reached
    obtain ⟨target, realized, rfl⟩ := reached
    exact setup.indebtedState_step who _ history.state _ _ target indebted realized

/-- An additional choice of the deviator from an intended history leaves it
indebted. -/
theorem indebted_of_extra (wellFormed : setup.WellFormed) (who : Player)
    (original : setup.intendedProtocol.History)
    (choices : ∀ i, (setup.informationModel (CommitmentInterface.values setup.program)).Choice i
      ((setup.informationModel (CommitmentInterface.values setup.program)).infoOf i
        (setup.intendedRestriction.history original).trace))
    (next : (setup.executionProtocol (CommitmentInterface.values setup.program)).History)
    (running : ¬ setup.intendedProtocol.terminal original.state)
    (extra : choices who ∉ Set.range (setup.intendedRestriction.choiceAt who original))
    (reached : next ∈ ((setup.informationModel
      (CommitmentInterface.values setup.program)).localStep
        (setup.intendedRestriction.history original) choices).support) :
    setup.IndebtedState who next.state := by
  obtain ⟨action, spelled, missing⟩ :=
    (setup.informationModel (CommitmentInterface.values setup.program)).menuRestriction_extraAt
      setup.intendedMenu setup.intendedMenu_adequate setup.intendedMenu_subset who original
      (choices who) extra
  have running' : ¬ (setup.executionProtocol (CommitmentInterface.values setup.program)).terminal
      (setup.intendedRestriction.history original).state := running
  simp only [InformationModel.localStep, dite_eq_right_of_eq_false (eq_false running'),
    PMF.mem_support_bindOnSupport_iff, PMF.mem_support_pure_iff] at reached
  obtain ⟨target, realized, rfl⟩ := reached
  have view : (setup.informationModel (CommitmentInterface.values setup.program)).infoOf who
      (restrictAvailable.trace original.trace) = setup.protocolObserve who original.state :=
    ((setup.informationModel _).restrictMenu_infoOf setup.intendedMenu
      setup.intendedMenu_adequate who original.trace).symm.trans
      (setup.intended_info who original.trace)
  rw [view] at missing
  exact setup.indebtedState_of_deviation who (setup.intendedState_trace wellFormed original.trace)
    _ _ spelled missing target realized

/-- **Approximate Nash preservation for the intended game.** For a well-formed
setup with finite commitment payload types and a finite initial law, and a
forfeit no smaller than the payoff range, every source profile that extends an
`ε`-Nash equilibrium of the intended game is an `ε`-Nash equilibrium of the
source game under the forfeit pass, with the same `ε`. It has the intended joint
law of terminal store and payoff, and no reveal fails on any history it
reaches. -/
theorem intended_isεNash_preserved [Fintype Player]
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (forfeit : ℝ) (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile
      (setup.informationModel (CommitmentInterface.values setup.program)).behavioralSignature)
    (agrees : setup.intendedRestriction.ExtendsProfile intended target) (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm
        (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)) ε intended) :
    IsεNash ((setup.informationModel
        (CommitmentInterface.values setup.program)).toBehavioralGameForm
          (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun state => forfeitUtility setup.program forfeit utility
          (setup.parameterOutcome parameter state) who)) ε target ∧
    (∀ final ∈ ((setup.informationModel (CommitmentInterface.values setup.program)).runBehavioral
        target (instructionCount setup.program + 1)).support,
      ∀ terminal, setup.protocolReadout final.state = some terminal →
        ∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0) ∧
    ((setup.informationModel (CommitmentInterface.values setup.program)).runBehavioral
        target (instructionCount setup.program + 1)).map
        (fun final => (setup.protocolReadout final.state,
          fun who => (setup.protocolReadout final.state).elim 0
            (fun state => forfeitUtility setup.program forfeit utility
              (setup.parameterOutcome parameter state) who))) =
      (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
        (fun final => (setup.protocolReadout final.state,
          fun who => (setup.protocolReadout final.state).elim 0
            (fun state => utility (setup.parameterOutcome parameter state) who))) := by
  classical
  have : Finite (setup.executionProtocol (CommitmentInterface.values setup.program)).History :=
    setup.finite_history finite _
  let sourcePayoff := fun (final : setup.intendedProtocol.History) (who : Player) =>
    (setup.protocolReadout final.state).elim 0
      (fun state => utility (setup.parameterOutcome parameter state) who)
  let targetPayoff := fun (final : (setup.executionProtocol
      (CommitmentInterface.values setup.program)).History) (who : Player) =>
    (setup.protocolReadout final.state).elim 0
      (fun state => forfeitUtility setup.program forfeit utility
        (setup.parameterOutcome parameter state) who)
  have matching : ∀ history who,
      targetPayoff (setup.intendedRestriction.history history) who =
        sourcePayoff history who := by
    intro history who
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
  have forfeits : ∀ who indebted (history : setup.intendedProtocol.History),
      setup.IndebtedState who indebted.state →
      (setup.executionProtocol (CommitmentInterface.values setup.program)).terminal
        indebted.state →
      setup.intendedProtocol.terminal history.state →
      targetPayoff indebted who ≤ sourcePayoff history who := by
    intro who indebted history owing stopped intendedStopped
    obtain ⟨intendedTerminal, intendedRead⟩ :=
      setup.exists_protocolReadout_of_terminal (CommitmentInterface.values setup.program)
        intendedStopped
    cases finalState : indebted.state with
    | none =>
        rw [finalState] at owing
        exact owing.elim
    | some state =>
        rw [finalState] at owing stopped
        obtain ⟨terminal, read⟩ :=
          ProtocolState.exists_readout_of_terminal setup.program state stopped
        have positive :=
          ProtocolState.failedReveals_pos_of_indebted who setup.program state owing read
        change (setup.protocolReadout indebted.state).elim 0 _ ≤
          (setup.protocolReadout history.state).elim 0 _
        have read' : setup.protocolReadout indebted.state = some terminal := by
          rw [finalState]
          exact read
        rw [read', intendedRead]
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
        nlinarith
  have law := setup.intendedRestriction.initialized_law intended target agrees
    (instructionCount setup.program + 1)
  refine ⟨?_, ?_, ?_⟩
  · exact setup.intendedRestriction.isεNash_extends_of_debt (setup.protocol_bounded _)
      ((setup.informationModel _).menuRestriction_reflecting _ _ setup.intendedMenu_subset)
      intended target agrees (fun who => setup.IndebtedState who)
      (fun who => setup.indebted_localStep who)
      (fun who original choices next running _ extra reached =>
        setup.indebted_of_extra wellFormed who original choices next running extra reached)
      sourcePayoff targetPayoff matching forfeits ε equilibrium
  · intro final reached terminal read who
    rw [← law, PMF.support_map] at reached
    obtain ⟨intendedFinal, _, rfl⟩ := reached
    exact setup.failedReveals_eq_zero_of_intendedState
      (setup.intendedState_trace wellFormed intendedFinal.trace) who read
  · rw [← law, PMF.map_comp]
    apply map_congr_on_support _
    intro final _
    exact Prod.ext rfl (funext fun who => matching final who)

end Vegas.SourceProgram.Setup
