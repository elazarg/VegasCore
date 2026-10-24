/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProgramPayoffs
import Vegas.Game.RecoveryExclusionPayoff
import Vegas.Game.PhaseExclusionPayoff

/-! # Valuation assumptions behind permanent-exclusion utility

A constant exit receipt gives constant exit utility only when exit valuation is
also constant. These adapters separate the two components of the existing
exclusion payoff. They neither implement an exit payment nor change any
failure, unfinished-readout or exclusion branch of the runtime.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}

/-- Exclusion clips valuation and monetary receipts separately. Their sum is
exactly the existing constant-utility exclusion convention. -/
theorem exclusionUtility_add (program : SourceProgram Player L Γ O) {Parameter : Type}
    (first second : Parameter × PublicOutcome program → Player → ℝ)
    (firstExit secondExit : Player → ℝ) (outcome : Parameter × PublicOutcome program)
    (who : Player) :
    program.exclusionUtility (fun owner => firstExit owner + secondExit owner)
        (fun result owner => first result owner + second result owner) outcome who =
      program.exclusionUtility firstExit first outcome who +
        program.exclusionUtility secondExit second outcome who := by
  unfold exclusionUtility
  split_ifs <;> rfl

/-- Program payments and an independently declared valuation agree with the
forced-exit utility convention when both exit components are constant on failure. -/
theorem exclusionUtility_parameterPaymentUtility {Parameter : Type}
    (program : SourceProgram Player L Γ O)
    (valuation : Parameter × PublicOutcome program → Player → ℝ)
    (exitValuation exitTransfer : Player → ℝ)
    (valuationOnFailure : ∀ outcome who, 1 ≤ program.failedReveals who outcome.2 →
      valuation outcome who = exitValuation who)
    (transferOnFailure : ∀ outcome who, 1 ≤ program.failedReveals who outcome →
      program.publicTransfers outcome who = exitTransfer who)
    (outcome : Parameter × PublicOutcome program) (who : Player) :
    program.exclusionUtility (fun owner => exitValuation owner + exitTransfer owner)
        (program.parameterPaymentUtility valuation) outcome who =
      program.parameterPaymentUtility valuation outcome who := by
  by_cases noFailure : program.failedReveals who outcome.2 = 0
  · exact exclusionUtility_of_failedReveals_eq_zero program _ _ noFailure
  · have failed := Nat.one_le_iff_ne_zero.mpr noFailure
    rw [exclusionUtility_of_failedReveals_pos program _ _ failed,
      parameterPaymentUtility_eq, valuationOnFailure outcome who failed,
      transferOnFailure outcome.2 who failed]

/-- With constant executable exit cash, constant failed-outcome utility is
equivalent to constant failed-outcome valuation. Cash constancy alone is insufficient. -/
theorem parameterPaymentUtility_exit_iff {Parameter : Type}
    (program : SourceProgram Player L Γ O)
    (valuation : Parameter × PublicOutcome program → Player → ℝ)
    (exitValuation exitTransfer : Player → ℝ)
    (outcome : Parameter × PublicOutcome program) (who : Player)
    (transferOnFailure : program.publicTransfers outcome.2 who = exitTransfer who) :
    program.parameterPaymentUtility valuation outcome who =
        exitValuation who + exitTransfer who ↔ valuation outcome who = exitValuation who := by
  rw [parameterPaymentUtility_eq, transferOnFailure, add_right_cancel_iff]

end Vegas.SourceProgram

namespace Vegas

open SourceProgram GameTheory GameTheory.Enforcement Interaction EventGraphRuntime
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The phase base is additive in both ordinary utility and exit utility. The
zero fallback for absent terminal readout is retained in both components. -/
theorem phaseExclusionBase_add (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode) (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (valuation transfer : State L setup.program.terminalCtx → Player → ℝ)
    (exitValuation exitTransfer : Player → ℝ)
    (state : (phaseApplication runtime leaks).ProtocolState) (who : Player) :
    phaseExclusionBase setup mode runtime leaks
        (fun terminal owner => valuation terminal owner + transfer terminal owner)
        (fun owner => exitValuation owner + exitTransfer owner) state who =
      phaseExclusionBase setup mode runtime leaks valuation exitValuation state who +
        phaseExclusionBase setup mode runtime leaks transfer exitTransfer state who := by
  cases state with
  | none => simp only [phaseExclusionBase, add_zero]
  | some control =>
    unfold phaseExclusionBase
    dsimp only
    split_ifs
    · rfl
    · cases phaseSourceReadout setup mode runtime leaks (some control) <;>
        simp only [Option.elim_none, Option.elim_some, add_zero]

/-- The nonconcurrent recovery base also separates into valuation and cash,
including runtime exclusion before a terminal store and failed source reveals. -/
theorem recoveryExclusionBase_add {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (valuation transfer : Parameter × PublicOutcome setup.program → Player → ℝ)
    (exitValuation exitTransfer : Player → ℝ)
    (state : (recoveryApplication (runtime setup) leaks).ProtocolState) (who : Player) :
    recoveryExclusionBase parameter
        (fun outcome owner => valuation outcome owner + transfer outcome owner)
        (fun owner => exitValuation owner + exitTransfer owner) state who =
      recoveryExclusionBase parameter valuation exitValuation state who +
        recoveryExclusionBase parameter transfer exitTransfer state who := by
  cases state with
  | none => simp only [recoveryExclusionBase, add_zero]
  | some control =>
    unfold recoveryExclusionBase
    dsimp only
    split_ifs
    · rfl
    · rw [exclusionBase_eq_readout, exclusionBase_eq_readout, exclusionBase_eq_readout]
      unfold exclusionReadoutUtility
      cases sourceReadout setup leaks
          (some (RecoveryProjection.control (runtime setup) leaks control)) with
      | none => simp only [Option.elim_none, add_zero]
      | some terminal =>
        exact exclusionUtility_add setup.program valuation transfer exitValuation exitTransfer
          (setup.parameterOutcome parameter terminal) who

/-- Expected utility of the actual monetary audit settlement instantiates the
existing phase utility with a sum, rather than charging valuation itself. -/
theorem phaseExclusionBase_expect_monetaryUtility
    (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (valuation : State L setup.program.terminalCtx → Player → ℝ)
    (exitValuation exitTransfer : Player → ℝ)
    {Observation : Type}
    (observe : (phaseApplication runtime leaks).ProtocolState → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    (state : (phaseApplication runtime leaks).ProtocolState) (who : Player) :
    expect (TerminalAudit.settlement
        (phaseExclusionBase setup mode runtime leaks
          (fun terminal owner => setup.program.publicTransfers
            (setup.program.publicOutcome terminal) owner) exitTransfer)
        observe audit deposit state)
      (fun receipts => monetaryUtility
        (phaseExclusionBase setup mode runtime leaks valuation exitValuation)
        (state, receipts) who) =
      TerminalAudit.utility
        (phaseExclusionBase setup mode runtime leaks
          (fun terminal owner => valuation terminal owner + setup.program.publicTransfers
            (setup.program.publicOutcome terminal) owner)
          (fun owner => exitValuation owner + exitTransfer owner))
        observe audit deposit state who := by
  rw [TerminalAudit.settlement_expect_monetaryUtility]
  congr 1
  funext current owner
  exact (phaseExclusionBase_add setup mode runtime leaks valuation _
    exitValuation exitTransfer current owner).symm

/-- The forced-exit recovery utility is also the expectation of declared
valuation plus actual audited cash, including its existing exclusion branches. -/
theorem recoveryExclusionBase_expect_monetaryUtility
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (valuation : Parameter × PublicOutcome setup.program → Player → ℝ)
    (exitValuation exitTransfer : Player → ℝ) {Observation : Type}
    (observe : (recoveryApplication (runtime setup) leaks).ProtocolState → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    (state : (recoveryApplication (runtime setup) leaks).ProtocolState) (who : Player) :
    expect (TerminalAudit.settlement
        (recoveryExclusionBase parameter
          (fun outcome owner => setup.program.publicTransfers outcome.2 owner) exitTransfer)
        observe audit deposit state)
      (fun receipts => monetaryUtility
        (recoveryExclusionBase parameter valuation exitValuation) (state, receipts) who) =
      TerminalAudit.utility
        (recoveryExclusionBase parameter (setup.program.parameterPaymentUtility valuation)
          (fun owner => exitValuation owner + exitTransfer owner))
        observe audit deposit state who := by
  rw [TerminalAudit.settlement_expect_monetaryUtility]
  congr 1
  funext current owner
  exact (recoveryExclusionBase_add parameter valuation _
    exitValuation exitTransfer current owner).symm

end Vegas
