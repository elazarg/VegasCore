/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ConcurrentRawEquilibrium
import Vegas.Game.SequentialPaymentValuation

/-! # Concurrent sequential preservation with declared valuation and cash

Ordinary cash is computed by the source program. Exit cash and exit valuation
are separate fixed inputs: this is an adapter for the existing constant-exit
utility contract, not an implementation of monetary exit settlement. The
unchanged concurrent theorem supplies an equilibrium, and its full joint law
also preserves actual audit cash after subtracting terminal valuation.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace ConcurrentPayoffs

/-- Valuation and program-computed receipts determine ordinary utility. Constant
exit valuation and exit cash determine the existing constant exit utility. -/
def programPayments (setup : Setup (Player := Player) (L := L))
    (valuation : State L setup.program.terminalCtx → Player → ℝ)
    (exitValuation exitTransfer lowerValuation upperValuation lowerTransfer upperTransfer :
      Player → ℝ) : ConcurrentPayoffs setup where
  utility terminal who := valuation terminal who +
    setup.program.publicTransfers (setup.program.publicOutcome terminal) who
  excludedPayoff who := exitValuation who + exitTransfer who
  lowerUtility who := lowerValuation who + lowerTransfer who
  upperUtility who := upperValuation who + upperTransfer who

omit [Fintype Player] in
/-- Separate valuation and payment bounds give the exact utility bounds needed
by the original concurrent theorem. The exit floor remains a utility condition. -/
theorem programPayments_bounded (setup : Setup (Player := Player) (L := L))
    (valuation : State L setup.program.terminalCtx → Player → ℝ)
    (exitValuation exitTransfer lowerValuation upperValuation lowerTransfer upperTransfer :
      Player → ℝ)
    (valuationLower : ∀ terminal who, lowerValuation who ≤ valuation terminal who)
    (valuationUpper : ∀ terminal who, valuation terminal who ≤ upperValuation who)
    (transferLower : ∀ outcome who,
      lowerTransfer who ≤ setup.program.publicTransfers outcome who)
    (transferUpper : ∀ outcome who,
      setup.program.publicTransfers outcome who ≤ upperTransfer who)
    (exitNonpositive : ∀ who, exitValuation who + exitTransfer who ≤ 0)
    (exitBelow : ∀ terminal who, exitValuation who + exitTransfer who ≤
      valuation terminal who +
        setup.program.publicTransfers (setup.program.publicOutcome terminal) who) :
    (programPayments setup valuation exitValuation exitTransfer
      lowerValuation upperValuation lowerTransfer upperTransfer).Bounded where
  lower_le terminal who := add_le_add (valuationLower terminal who)
    (transferLower (setup.program.publicOutcome terminal) who)
  le_upper terminal who := add_le_add (valuationUpper terminal who)
    (transferUpper (setup.program.publicOutcome terminal) who)
  excluded_nonpositive := exitNonpositive
  excluded_le := exitBelow

end ConcurrentPayoffs



/-- The intended joint law with program-computed cash in place of utility. -/
def concurrentSourceCashLaw (setup : Setup (Player := Player) (L := L))
    (source : setup.intendedModel.BehavioralAssessment) :
    PMF (TerminalObservation setup) :=
  (setup.intendedModel.runBehavioralTerminalFrom
    setup.intended_bounded.wellFoundedHistories source.strategy
    setup.intendedProtocol.initHistory).map fun final =>
      let terminal := setup.protocolReadout final.state
      TerminalObservation.read setup terminal
        (fun who => terminal.elim 0 (fun state =>
          setup.program.publicTransfers (setup.program.publicOutcome state) who))

namespace ReservedConcurrentImplementation

variable {setup : Setup (Player := Player) (L := L)}
  (implementation : ReservedConcurrentImplementation setup)

/-- Cash uses program payments on a completed unexcluded state and the declared
fixed exit receipt on exclusion, retaining the existing zero fallback. -/
def cashBase (exitTransfer : Player → ℝ) :=
  phaseExclusionBase setup .concurrent implementation.runtime implementation.leaks
    (fun terminal who => setup.program.publicTransfers (setup.program.publicOutcome terminal) who)
    exitTransfer

/-- Actual correlated audit receipts, jointly with all original outcome data. -/
def jointCashLaw (exitTransfer : Player → ℝ) (countAudit : ConcurrentCountAudit setup)
    (target : implementation.model.BehavioralAssessment) :
    PMF (TerminalObservation setup) :=
  (implementation.terminalLaw target).bind fun final =>
    (TerminalAudit.settlement (implementation.cashBase exitTransfer)
      implementation.application.stateTraffic (implementation.audit countAudit)
      countAudit.deposit final.state).map fun receipts =>
        TerminalObservation.read setup
          (phaseSourceReadout setup .concurrent implementation.runtime implementation.leaks
            final.state) receipts

omit [Fintype Player] in
/-- The equilibrium utility is the expectation of valuation plus actual cash
settlement. Exit valuation is explicitly constant and absent readout has zero value. -/
theorem auditedUtility_programPayments_eq_expect
    (valuation : State L setup.program.terminalCtx → Player → ℝ)
    (exitValuation exitTransfer lowerValuation upperValuation lowerTransfer upperTransfer :
      Player → ℝ) (countAudit : ConcurrentCountAudit setup)
    (state : implementation.application.ProtocolState) (who : Player) :
    implementation.auditedUtility
        (ConcurrentPayoffs.programPayments setup valuation exitValuation exitTransfer
          lowerValuation upperValuation lowerTransfer upperTransfer) countAudit state who =
      expect (TerminalAudit.settlement (implementation.cashBase exitTransfer)
          implementation.application.stateTraffic (implementation.audit countAudit)
          countAudit.deposit state)
        (fun receipts => monetaryUtility
          (phaseExclusionBase setup .concurrent implementation.runtime implementation.leaks
            valuation exitValuation) (state, receipts) who) := by
  exact (phaseExclusionBase_expect_monetaryUtility setup .concurrent implementation.runtime
    implementation.leaks valuation exitValuation exitTransfer
    implementation.application.stateTraffic (implementation.audit countAudit)
    countAudit.deposit state who).symm

end ReservedConcurrentImplementation

/-- Removing terminal valuation from the source utility law recovers the exact
program-cash law, including the optional readout and every original coordinate. -/
theorem concurrent_programPayments_source_cash_law
    (setup : Setup (Player := Player) (L := L))
    (valuation : State L setup.program.terminalCtx → Player → ℝ)
    (exitValuation exitTransfer lowerValuation upperValuation lowerTransfer upperTransfer :
      Player → ℝ) (source : setup.intendedModel.BehavioralAssessment) :
    ((ConcurrentPayoffs.programPayments setup valuation exitValuation exitTransfer
        lowerValuation upperValuation lowerTransfer upperTransfer).jointLaw source).map
        (TerminalObservation.cashReadout setup valuation) =
      concurrentSourceCashLaw setup source := by
  unfold ConcurrentPayoffs.jointLaw concurrentSourceCashLaw
  rw [PMF.map_comp]
  congr 1
  funext final
  rw [Function.comp_apply, TerminalObservation.cashReadout_read]
  apply congrArg (TerminalObservation.read setup (setup.protocolReadout final.state))
  funext who
  cases setup.protocolReadout final.state <;>
    simp [ConcurrentPayoffs.programPayments]

/-- On unexcluded support, inverse valuation recovers actual audited cash,
including any correlated charges. Audit cleanliness is unnecessary. -/
theorem concurrent_programPayments_target_cash_law
    (setup : Setup (Player := Player) (L := L))
    (implementation : ReservedConcurrentImplementation setup)
    (valuation : State L setup.program.terminalCtx → Player → ℝ)
    (exitValuation exitTransfer lowerValuation upperValuation lowerTransfer upperTransfer :
      Player → ℝ)
    (countAudit : ConcurrentCountAudit setup)
    (target : implementation.model.BehavioralAssessment)
    (noExclusions : ∀ final ∈ (implementation.terminalLaw target).support, ∀ who,
      ¬ PhaseExcluded setup .concurrent implementation.runtime implementation.leaks who final.state)
 :
    (implementation.jointLaw
        (ConcurrentPayoffs.programPayments setup valuation exitValuation exitTransfer
          lowerValuation upperValuation lowerTransfer upperTransfer) countAudit target).map
        (TerminalObservation.cashReadout setup valuation) =
      implementation.jointCashLaw exitTransfer countAudit target := by
  unfold ReservedConcurrentImplementation.jointLaw ReservedConcurrentImplementation.jointCashLaw
  rw [PMF.map_bind]
  apply bind_congr_on_support _
  intro final supported
  have baseAdd : implementation.base
      (ConcurrentPayoffs.programPayments setup valuation exitValuation exitTransfer
        lowerValuation upperValuation lowerTransfer upperTransfer) =
      fun state who =>
        phaseExclusionBase setup .concurrent implementation.runtime implementation.leaks
          valuation exitValuation state who + implementation.cashBase exitTransfer state who := by
    funext state who
    exact phaseExclusionBase_add setup .concurrent implementation.runtime implementation.leaks
      valuation _ exitValuation exitTransfer state who
  rw [baseAdd, ← TerminalAudit.settlement_add_valuation
    (phaseExclusionBase setup .concurrent implementation.runtime implementation.leaks
      valuation exitValuation) (implementation.cashBase exitTransfer)]
  simp only [PMF.map_comp, Function.comp_def]
  congr 1
  funext receipts
  rw [TerminalObservation.cashReadout_read]
  apply congrArg (TerminalObservation.read setup _)
  funext who
  have clear := noExclusions final supported who
  cases current : final.state with
  | none =>
    simp only [phaseExclusionBase, phaseSourceReadout,
      Option.bind_none, Option.elim_none, zero_add, sub_zero]
  | some control =>
    have excluded : who ∉ control.execution.application.current.excluded := by
      simpa only [current, PhaseExcluded] using clear
    simp only [phaseExclusionBase, excluded, ite_false]
    cases phaseSourceReadout setup .concurrent implementation.runtime implementation.leaks
        (some control) <;> simp


/-- Separate valuation/payment bounds and a constant exit valuation instantiate
the original concurrent SE theorem. Every original assumption and quantifier is
retained, and the conclusion additionally preserves the entire joint cash law. -/
theorem concurrent_programPayments_sequential_preservation
    (setup : Setup (Player := Player) (L := L))
    (implementation : ReservedConcurrentImplementation setup)
    (valuation : State L setup.program.terminalCtx → Player → ℝ)
    (exitValuation exitTransfer lowerValuation upperValuation lowerTransfer upperTransfer :
      Player → ℝ)
    (valuationLower : ∀ terminal who, lowerValuation who ≤ valuation terminal who)
    (valuationUpper : ∀ terminal who, valuation terminal who ≤ upperValuation who)
    (transferLower : ∀ outcome who,
      lowerTransfer who ≤ setup.program.publicTransfers outcome who)
    (transferUpper : ∀ outcome who,
      setup.program.publicTransfers outcome who ≤ upperTransfer who)
    (exitNonpositive : ∀ who, exitValuation who + exitTransfer who ≤ 0)
    (exitBelow : ∀ terminal who, exitValuation who + exitTransfer who ≤
      valuation terminal who +
        setup.program.publicTransfers (setup.program.publicOutcome terminal) who)
    (countAudit : ConcurrentCountAudit setup)
    (operational : implementation.Operational)
    (funded : countAudit.Funded (ConcurrentPayoffs.programPayments setup valuation
      exitValuation exitTransfer lowerValuation upperValuation lowerTransfer upperTransfer)) :
    ∀ source : setup.intendedModel.BehavioralAssessment,
      (ConcurrentPayoffs.programPayments setup valuation exitValuation exitTransfer
        lowerValuation upperValuation lowerTransfer upperTransfer).SourceEquilibrium source →
      ∃ target : implementation.model.BehavioralAssessment,
        implementation.PreservesAssessment
          (ConcurrentPayoffs.programPayments setup valuation exitValuation exitTransfer
            lowerValuation upperValuation lowerTransfer upperTransfer) countAudit source target ∧
        concurrentSourceCashLaw setup source =
          implementation.jointCashLaw exitTransfer countAudit target := by
  intro source equilibrium
  let payoffs := ConcurrentPayoffs.programPayments setup valuation exitValuation exitTransfer
    lowerValuation upperValuation lowerTransfer upperTransfer
  have bounded : payoffs.Bounded := ConcurrentPayoffs.programPayments_bounded setup valuation
    exitValuation exitTransfer lowerValuation upperValuation lowerTransfer upperTransfer
    valuationLower valuationUpper transferLower transferUpper exitNonpositive exitBelow
  obtain ⟨target, preserved⟩ := concurrentRawSequentialPreservation setup implementation payoffs
    countAudit ⟨operational, bounded, funded⟩ source equilibrium
  refine ⟨target, preserved, ?_⟩
  have cashLaw := congrArg (PMF.map (TerminalObservation.cashReadout setup valuation))
    preserved.jointLaw
  rw [concurrent_programPayments_source_cash_law,
    concurrent_programPayments_target_cash_law setup implementation valuation exitValuation
      exitTransfer lowerValuation upperValuation lowerTransfer upperTransfer countAudit target
      preserved.noExclusions] at cashLaw
  exact cashLaw

end Vegas
