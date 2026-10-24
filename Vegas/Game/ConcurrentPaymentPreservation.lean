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

namespace ConcurrentTerminalObservation

/-- Change only the monetary coordinate: every original input, typed terminal
state and public-result coordinate is retained. Absent readout keeps zero valuation. -/
def cashReadout (setup : Setup (Player := Player) (L := L))
    (valuation : State L setup.program.terminalCtx → Player → ℝ)
    (observation : ConcurrentTerminalObservation setup) : ConcurrentTerminalObservation setup :=
  { observation with netPayoffs := fun who => observation.netPayoffs who -
      observation.terminalState.elim 0 (fun terminal => valuation terminal who) }

omit [Fintype Player] in
theorem cashReadout_read (setup : Setup (Player := Player) (L := L))
    (valuation : State L setup.program.terminalCtx → Player → ℝ)
    (terminal : Option (State L setup.program.terminalCtx)) (payoffs : Player → ℝ) :
    cashReadout setup valuation (read setup terminal payoffs) =
      read setup terminal (fun who => payoffs who -
        terminal.elim 0 (fun state => valuation state who)) := rfl

end ConcurrentTerminalObservation

/-- The intended joint law with program-computed cash in place of utility. -/
def concurrentSourceCashLaw (setup : Setup (Player := Player) (L := L))
    (source : setup.intendedModel.BehavioralAssessment) :
    PMF (ConcurrentTerminalObservation setup) :=
  (setup.intendedModel.runBehavioralTerminalFrom
    setup.intended_bounded.wellFoundedHistories source.strategy
    setup.intendedProtocol.initHistory).map fun final =>
      let terminal := setup.protocolReadout final.state
      ConcurrentTerminalObservation.read setup terminal
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
    PMF (ConcurrentTerminalObservation setup) :=
  (implementation.terminalLaw target).bind fun final =>
    (TerminalAudit.settlement (implementation.cashBase exitTransfer)
      implementation.application.stateTraffic (implementation.audit countAudit)
      countAudit.deposit final.state).map fun receipts =>
        ConcurrentTerminalObservation.read setup
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
        (ConcurrentTerminalObservation.cashReadout setup valuation) =
      concurrentSourceCashLaw setup source := by
  unfold ConcurrentPayoffs.jointLaw concurrentSourceCashLaw
  rw [PMF.map_comp]
  congr 1
  funext final
  rw [Function.comp_apply, ConcurrentTerminalObservation.cashReadout_read]
  apply congrArg (ConcurrentTerminalObservation.read setup (setup.protocolReadout final.state))
  funext who
  cases setup.protocolReadout final.state <;>
    simp [ConcurrentPayoffs.programPayments]

/-- On the clean, unexcluded support delivered by the original theorem, the
inverse valuation readout is the law of actual audited monetary receipts. -/
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
    (noCharges : ∀ final ∈ (implementation.terminalLaw target).support, ∀ who,
      TerminalAudit.charge implementation.application.stateTraffic
        (implementation.audit countAudit) final.state who = 0) :
    (implementation.jointLaw
        (ConcurrentPayoffs.programPayments setup valuation exitValuation exitTransfer
          lowerValuation upperValuation lowerTransfer upperTransfer) countAudit target).map
        (ConcurrentTerminalObservation.cashReadout setup valuation) =
      implementation.jointCashLaw exitTransfer countAudit target := by
  unfold ReservedConcurrentImplementation.jointLaw ReservedConcurrentImplementation.jointCashLaw
  rw [PMF.map_bind]
  apply bind_congr_on_support _
  intro final supported
  rw [TerminalAudit.settlement_clean _ _ _ _ _ (noCharges final supported),
    TerminalAudit.settlement_clean _ _ _ _ _ (noCharges final supported)]
  simp only [PMF.pure_map]
  congr 1
  rw [ConcurrentTerminalObservation.cashReadout_read]
  apply congrArg (ConcurrentTerminalObservation.read setup _)
  funext who
  have clear := noExclusions final supported who
  cases current : final.state with
  | none =>
    simp only [ReservedConcurrentImplementation.base,
      ReservedConcurrentImplementation.cashBase, phaseExclusionBase, phaseSourceReadout,
      Option.bind_none, Option.elim_none, sub_zero]
  | some control =>
    have excluded : who ∉ control.execution.application.current.excluded := by
      simpa only [current, PhaseExcluded] using clear
    simp only [ReservedConcurrentImplementation.base,
      ReservedConcurrentImplementation.cashBase, phaseExclusionBase, excluded,
      ↓reduceIte, ConcurrentPayoffs.programPayments]
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
  have cashLaw := congrArg (PMF.map (ConcurrentTerminalObservation.cashReadout setup valuation))
    preserved.jointLaw
  rw [concurrent_programPayments_source_cash_law,
    concurrent_programPayments_target_cash_law setup implementation valuation exitValuation
      exitTransfer lowerValuation upperValuation lowerTransfer upperTransfer countAudit target
      preserved.noExclusions preserved.noCharges] at cashLaw
  exact cashLaw

end Vegas
