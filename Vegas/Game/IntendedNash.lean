/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.IntendedPreservation
import GameTheoryExtensions.Analysis.Protocol.RetainedDeviation

/-! # Approximate Nash preservation under public default

Every source profile extending an intended ε-Nash equilibrium remains an
ε-Nash equilibrium under fixed exit utility, when the declared exit payoff
is below every actual intended terminal payoff. The source profile has the
intended joint readout/payoff law, with no public default or failed reveal.

The retained-deviation theorem compares a source deviation with its law
conditioned on intended actions. Every reached history outside the intended
game carries the deviator's owed failure. Actual trace provenance makes that
owner publicly default at every terminal continuation. An optional count-penalty
result instead compares the forfeit with the terminal legal-history payoff spread.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable (setup : Setup (Player := Player) (L := L))

/-- The deviator's debt is absorbing in the source model. -/
theorem owesFailure_localStep (admission : CommitmentInterface setup.program) (who : Player)
    (history : (setup.executionProtocol admission).History)
    (choices : ∀ i, (setup.informationModel admission).Choice i
      ((setup.informationModel admission).infoOf i
        history.trace))
    (next : (setup.executionProtocol admission).History)
    (indebted : setup.OwesFailureState who history.state)
    (reached : next ∈ ((setup.informationModel
      admission).localStep history choices).support) :
    setup.OwesFailureState who next.state := by
  by_cases stopped : (setup.executionProtocol
      admission).terminal history.state
  · simp only [InformationModel.localStep, dite_eq_left_of_eq_true (eq_true stopped),
      PMF.mem_support_pure_iff] at reached
    exact reached ▸ indebted
  · simp only [InformationModel.localStep, dite_eq_right_of_eq_false (eq_false stopped),
      PMF.mem_support_bindOnSupport_iff, PMF.mem_support_pure_iff] at reached
    obtain ⟨target, realized, rfl⟩ := reached
    exact setup.owesFailureState_step who _ history.state _ _ target indebted realized

/-- An additional choice of the deviator from an intended history leaves it
indebted. -/
theorem owesFailure_of_extra (admission : CommitmentInterface setup.program)
    (wellFormed : setup.WellFormed) (who : Player)
    (original : setup.intendedProtocol.History)
    (choices : ∀ i, (setup.informationModel admission).Choice i
      ((setup.informationModel admission).infoOf i
        ((setup.intendedRestriction admission).history
          original).trace))
    (next : (setup.executionProtocol admission).History)
    (running : ¬ setup.intendedProtocol.terminal original.state)
    (extra : choices who ∉ Set.range ((setup.intendedRestriction admission).choiceAt who original))
    (reached : next ∈ ((setup.informationModel
      admission).localStep
        ((setup.intendedRestriction admission).history
          original) choices).support) :
    setup.OwesFailureState who next.state := by
  obtain ⟨action, spelled, missing⟩ :=
    (setup.informationModel admission).menuRestriction_extraAt
      setup.intendedMenu (setup.intendedMenu_adequate admission)
      (setup.intendedMenu_subset
        admission) who original
      (choices who) extra
  have running' : ¬ (setup.executionProtocol admission).terminal
      ((setup.intendedRestriction admission).history
        original).state := running
  simp only [InformationModel.localStep, dite_eq_right_of_eq_false (eq_false running'),
    PMF.mem_support_bindOnSupport_iff, PMF.mem_support_pure_iff] at reached
  obtain ⟨target, realized, rfl⟩ := reached
  have view : (setup.informationModel admission).infoOf who
      (restrictAvailable.trace (E := setup.executionProtocol admission)
        (included := setup.intendedAvailable_subset admission)
        (progress := setup.intendedProgress admission) original.trace) =
          setup.protocolObserve who original.state := setup.protocol_info admission who _
  rw [view] at missing
  exact setup.owesFailureState_of_deviation admission who
    (setup.intendedState_trace wellFormed original.trace)
    _ _ spelled missing target realized

/-- **Approximate Nash preservation for the intended game.** For a well-formed
setup with finite commitment payload types and a finite initial law, and a
forfeit no smaller than the payoff range, every source profile that extends an
`ε`-Nash equilibrium of the intended game is an `ε`-Nash equilibrium of the
source game under the forfeit pass, with the same `ε`. It has the intended joint
law of terminal store and payoff, and no reveal fails on any history it
reaches. -/
theorem intended_forfeit_isεNash_preserved [Fintype Player]
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (forfeit : ℝ)
    (range : setup.TerminalPayoffSpread (CommitmentInterface.values setup.program)
      parameter utility forfeit)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile
      (setup.informationModel (CommitmentInterface.values setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction (CommitmentInterface.values
      setup.program)).ExtendsProfile intended target) (ε : ℝ)
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
  have : Finite setup.intendedProtocol.History :=
    Finite.of_injective _ (setup.intendedRestriction
      (CommitmentInterface.values setup.program)).history.injective
  let sourcePayoff := fun (final : setup.intendedProtocol.History) (who : Player) =>
    (setup.protocolReadout final.state).elim 0
      (fun state => utility (setup.parameterOutcome parameter state) who)
  let targetPayoff := fun (final : (setup.executionProtocol
      (CommitmentInterface.values setup.program)).History) (who : Player) =>
    (setup.protocolReadout final.state).elim 0
      (fun state => forfeitUtility setup.program forfeit utility
        (setup.parameterOutcome parameter state) who)
  have matching : ∀ history who,
      targetPayoff ((setup.intendedRestriction (CommitmentInterface.values
        setup.program)).history history) who =
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
      setup.OwesFailureState who indebted.state →
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
          ProtocolState.failedReveals_pos_of_owesFailure who setup.program state owing read
        change (setup.protocolReadout indebted.state).elim 0 _ ≤
          (setup.protocolReadout history.state).elim 0 _
        have read' : setup.protocolReadout indebted.state = some terminal := by
          rw [finalState]
          exact read
        rw [read', intendedRead]
        change forfeitUtility setup.program forfeit utility
          (setup.parameterOutcome parameter terminal) who ≤
            utility (setup.parameterOutcome parameter intendedTerminal) who
        have fullyStopped :
            (setup.executionProtocol (CommitmentInterface.values setup.program)).terminal
              indebted.state := by
          rw [finalState]
          exact stopped
        have spread := range indebted
          ((setup.intendedRestriction (CommitmentInterface.values setup.program)).history history)
          fullyStopped intendedStopped who
        have nonnegative := range indebted indebted fullyStopped fullyStopped who
        have lowerRead : setup.protocolReadout
            ((setup.intendedRestriction (CommitmentInterface.values setup.program)).history
              history).state = some intendedTerminal := intendedRead
        simp only [read', lowerRead, Option.elim_some] at spread
        simp only [read', Option.elim_some, sub_self] at nonnegative
        have count : (1 : ℝ) ≤ (failedReveals setup.program who
            (setup.parameterOutcome parameter terminal).2 : ℝ) :=
          Nat.one_le_cast.mpr positive
        simp only [forfeitUtility]
        nlinarith
  have law := (setup.intendedRestriction (CommitmentInterface.values
    setup.program)).initialized_law intended target agrees
    (instructionCount setup.program + 1)
  refine ⟨?_, ?_, ?_⟩
  · exact (setup.intendedRestriction (CommitmentInterface.values
    setup.program)).isεNash_extends_of_debt (setup.protocol_bounded _)
      ((setup.informationModel _).menuRestriction_reflecting _ _ (setup.intendedMenu_subset
        (CommitmentInterface.values setup.program)))
      intended target agrees (fun who => setup.OwesFailureState who)
      (fun who => setup.owesFailure_localStep (CommitmentInterface.values setup.program) who)
      (fun who original choices next running _ extra reached =>
        setup.owesFailure_of_extra (CommitmentInterface.values setup.program) wellFormed who
          original choices next running extra reached)
      sourcePayoff targetPayoff (fun _ _ => payoffIntegrable_of_finite _ _)
      (fun _ _ => payoffIntegrable_of_finite _ _) matching forfeits ε equilibrium
  · intro final reached terminal read who
    rw [← law, PMF.support_map] at reached
    obtain ⟨intendedFinal, _, rfl⟩ := reached
    exact setup.failedReveals_eq_zero_of_intendedState
      (setup.intendedState_trace wellFormed intendedFinal.trace) who read
  · rw [← law, PMF.map_comp]
    apply map_congr_on_support _
    intro final _
    exact Prod.ext rfl (funext fun who => matching final who)

/-- Every source profile extending an intended ε-Nash equilibrium is an ε-Nash
source profile with fixed exit utility, under any binding admission interface.
The exit payoff is compared only with intended terminal readouts; equilibrium
paths preserve the joint typed-readout/payoff law and have no public defaults
or failed reveals. -/
theorem intended_isεNash_preserved [Fintype Player]
    (admission : CommitmentInterface setup.program)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (target : Profile
      (setup.informationModel admission).behavioralSignature)
    (agrees : (setup.intendedRestriction admission).ExtendsProfile intended target) (ε : ℝ)
    (equilibrium : IsεNash (setup.intendedModel.toBehavioralGameForm
        (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)) ε intended) :
    IsεNash ((setup.informationModel
        admission).toBehavioralGameForm
          (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun state => exclusionUtility setup.program excludedPayoff utility
          (setup.parameterOutcome parameter state) who)) ε target ∧
    (∀ final ∈ ((setup.informationModel admission).runBehavioral
        target (instructionCount setup.program + 1)).support,
      ∀ terminal, setup.protocolReadout final.state = some terminal →
        terminal.defaulted = ∅ ∧
          ∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0) ∧
    ((setup.informationModel admission).runBehavioral
        target (instructionCount setup.program + 1)).map
        (fun final => (setup.protocolReadout final.state,
          fun who => (setup.protocolReadout final.state).elim 0
            (fun state => exclusionUtility setup.program excludedPayoff utility
              (setup.parameterOutcome parameter state) who))) =
      (setup.intendedModel.runBehavioral intended (instructionCount setup.program + 1)).map
        (fun final => (setup.protocolReadout final.state,
          fun who => (setup.protocolReadout final.state).elim 0
            (fun state => utility (setup.parameterOutcome parameter state) who))) := by
  classical
  have : Finite (setup.executionProtocol admission).History :=
    setup.finite_history finite _
  have : Finite setup.intendedProtocol.History :=
    Finite.of_injective _ (setup.intendedRestriction
      admission).history.injective
  let sourcePayoff := fun (final : setup.intendedProtocol.History) (who : Player) =>
    (setup.protocolReadout final.state).elim 0
      (fun state => utility (setup.parameterOutcome parameter state) who)
  let targetPayoff := fun (final : (setup.executionProtocol
      admission).History) (who : Player) =>
    (setup.protocolReadout final.state).elim 0
      (fun state => exclusionUtility setup.program excludedPayoff utility
        (setup.parameterOutcome parameter state) who)
  have matching : ∀ history who,
      targetPayoff ((setup.intendedRestriction admission).history history) who =
        sourcePayoff history who := by
    intro history who
    change (setup.protocolReadout history.state).elim 0 _ =
      (setup.protocolReadout history.state).elim 0 _
    cases read : setup.protocolReadout history.state with
    | none => rfl
    | some terminal =>
        exact exclusionUtility_of_not_defaulted setup.program excludedPayoff utility
          (setup.not_defaulted_of_intendedState
            (setup.intendedState_trace wellFormed history.trace) who read)
  have forfeits : ∀ who indebted (history : setup.intendedProtocol.History),
      setup.OwesFailureState who indebted.state →
      (setup.executionProtocol admission).terminal
        indebted.state →
      setup.intendedProtocol.terminal history.state →
      targetPayoff indebted who ≤ sourcePayoff history who := by
    intro who indebted history owing stopped intendedStopped
    obtain ⟨intendedTerminal, intendedRead⟩ :=
      setup.exists_protocolReadout_of_terminal admission
        intendedStopped
    cases finalState : indebted.state with
    | none =>
        rw [finalState] at owing
        exact owing.elim
    | some state =>
        rw [finalState] at owing stopped
        obtain ⟨terminal, read⟩ :=
          ProtocolState.exists_readout_of_terminal setup.program state stopped
        have trace := indebted.trace
        rw [finalState] at trace
        have defaulted := setup.defaulted_of_owesFailure_trace admission trace who owing read
        change (setup.protocolReadout indebted.state).elim 0 _ ≤
          (setup.protocolReadout history.state).elim 0 _
        have read' : setup.protocolReadout indebted.state = some terminal := by
          rw [finalState]
          exact read
        rw [read', intendedRead]
        calc
          exclusionUtility setup.program excludedPayoff utility
              (setup.parameterOutcome parameter terminal) who = excludedPayoff who :=
            exclusionUtility_of_defaulted setup.program excludedPayoff utility defaulted
          _ ≤ utility (setup.parameterOutcome parameter intendedTerminal) who :=
            below history intendedTerminal intendedRead who
  have law := (setup.intendedRestriction admission).initialized_law intended target agrees
    (instructionCount setup.program + 1)
  refine ⟨?_, ?_, ?_⟩
  · exact (setup.intendedRestriction admission).isεNash_extends_of_debt (setup.protocol_bounded _)
      ((setup.informationModel admission).menuRestriction_reflecting setup.intendedMenu
        (setup.intendedMenu_adequate admission) (setup.intendedMenu_subset admission))
      intended target agrees (fun who => setup.OwesFailureState who)
      (fun who => setup.owesFailure_localStep admission who)
      (fun who original choices next running _ extra reached =>
        setup.owesFailure_of_extra admission wellFormed who original choices next running extra
          reached)
      sourcePayoff targetPayoff (fun _ _ => payoffIntegrable_of_finite _ _)
      (fun _ _ => payoffIntegrable_of_finite _ _) matching forfeits ε equilibrium
  · intro final reached terminal read
    rw [← law, PMF.support_map] at reached
    obtain ⟨intendedFinal, _, rfl⟩ := reached
    have known := setup.intendedState_trace wellFormed intendedFinal.trace
    refine ⟨Finset.eq_empty_iff_forall_notMem.mpr (fun who =>
      setup.not_defaulted_of_intendedState known who read), ?_⟩
    intro who
    exact setup.failedReveals_eq_zero_of_intendedState known who read
  · rw [← law, PMF.map_comp]
    apply map_congr_on_support _
    intro final _
    exact Prod.ext rfl (funext fun who => matching final who)

end Vegas.SourceProgram.Setup
