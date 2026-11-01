/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.AsyncServiceRawNash
import Vegas.Game.ProgramPayoffs

/-! # Program payments on the audited asynchronous service

Monetary settlement evaluates the program's payment expressions on the
typed terminal readout and subtracts collectible deposits. Valuation is separate
analysis data. An unfinished readout gives both components zero before any audit
deduction.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

variable (service : AsyncServiceSpec Player L)

/-- Program-determined receipts on the runtime's typed source readout. -/
def paymentTransfers :=
  serviceBaseUtility service.setup service.mode service.deadline service.leaks
    (fun terminal who => (transferAmount
      (service.setup.program.evaluatePayoffs terminal.state) who : ℝ))

/-- Private valuation uses the same readout, independently of the money reader. -/
def paymentValuation {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (valuation : Parameter × PublicOutcome service.setup.program → Player → ℝ) :=
  serviceBaseUtility service.setup service.mode service.deadline service.leaks
    (fun terminal => valuation (service.setup.parameterOutcome parameter terminal))

/-- Actual randomized receipts after the evidence-based deposit audit. -/
def paymentSettlement
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode))) (deposit : Player → ℝ) :=
  TerminalAudit.settlement service.paymentTransfers
    ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
      service.leaks)
    (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit

/-- Expected valuation plus actual monetary settlement, conditional on a runtime state. -/
def paymentExpectedUtility {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (valuation : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode))) (deposit : Player → ℝ)
    (state : (serviceApplication service.setup service.mode service.deadline
      service.leaks).ProtocolState) (who : Player) : ℝ :=
  expect (service.paymentSettlement sample deposit state)
    (fun receipts => service.paymentValuation parameter valuation state who + receipts who)

/-- Audit utility is obtained by integrating the monetary settlement. The identity
holds on every runtime state, including unfinished states and deviations. -/
theorem paymentExpectedUtility_eq {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (valuation : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode))) (deposit : Player → ℝ) :
    service.paymentExpectedUtility parameter valuation sample deposit =
      TerminalAudit.utility
        (serviceBaseUtility service.setup service.mode service.deadline service.leaks
          (fun terminal => service.setup.program.parameterPaymentUtility valuation
            (service.setup.parameterOutcome parameter terminal)))
        ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
          service.leaks)
        (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample)
        deposit := by
  have combined :
      (fun state who => service.paymentValuation parameter valuation state who +
        service.paymentTransfers state who) =
      serviceBaseUtility service.setup service.mode service.deadline service.leaks
        (fun terminal => service.setup.program.parameterPaymentUtility valuation
          (service.setup.parameterOutcome parameter terminal)) := by
    funext state who
    simp only [paymentValuation, paymentTransfers, serviceBaseUtility]
    cases serviceSourceReadout service.setup service.mode service.deadline service.leaks state
      <;> simp only [Option.elim_none, Option.elim_some, zero_add,
        Setup.parameterPaymentUtility_parameterOutcome]
  funext state who
  exact (TerminalAudit.settlement_expect_monetaryUtility
    (service.paymentValuation parameter valuation) service.paymentTransfers
    ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
      service.leaks)
    (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample)
    deposit state who).trans (by rw [combined])

/-- Declared bounds on valuation, executable receipts, and deposits provide the
runtime Nash theorem's interval at actual initialized histories, including
unfinished readouts. Its width is
`max 0 (valuationHigh + transferHigh) - min 0 (valuationLow + transferLow) +
depositBound`, so callers need no separate case analysis of audit verdicts. -/
theorem payment_within_of_bounds {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (valuation : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (valuationLow valuationHigh transferLow transferHigh depositBound : ℝ)
    (valuation_bounds : ∀ control,
      ((serviceApplication service.setup service.mode service.deadline service.leaks).protocol
        (serviceInitialLaw service.setup service.mode) service.horizon service.scheduler).Trace
          (some control) →
      ∀ terminal, serviceSourceReadout service.setup service.mode service.deadline service.leaks
        (some control) = some terminal → ∀ who,
      valuationLow ≤ valuation (service.setup.parameterOutcome parameter terminal) who ∧
        valuation (service.setup.parameterOutcome parameter terminal) who ≤ valuationHigh)
    (transfer_bounds : ∀ control,
      ((serviceApplication service.setup service.mode service.deadline service.leaks).protocol
        (serviceInitialLaw service.setup service.mode) service.horizon service.scheduler).Trace
          (some control) →
      ∀ terminal, serviceSourceReadout service.setup service.mode service.deadline service.leaks
        (some control) = some terminal → ∀ who,
      transferLow ≤ (transferAmount (service.setup.program.evaluatePayoffs terminal.state)
        who : ℝ) ∧
        (transferAmount (service.setup.program.evaluatePayoffs terminal.state) who : ℝ) ≤
          transferHigh)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (deposit : Player → ℝ)
    (deposit_bounds : ∀ who, 0 ≤ deposit who ∧ deposit who ≤ depositBound) :
    service.SettlementRange parameter (service.setup.program.parameterPaymentUtility valuation)
      sample deposit (fun _ => min 0 (valuationLow + transferLow) - depositBound)
      (fun _ => max 0 (valuationHigh + transferHigh) - min 0 (valuationLow + transferLow) +
        depositBound) := by
  intro control trace payoffs supported who
  rw [TerminalAudit.settlement, PMF.support_map] at supported
  obtain ⟨verdict, _, rfl⟩ := supported
  let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
    (fun terminal => service.setup.program.parameterPaymentUtility valuation
      (service.setup.parameterOutcome parameter terminal))
  have baseBounds : min 0 (valuationLow + transferLow) ≤ base (some control) who ∧
      base (some control) who ≤ max 0 (valuationHigh + transferHigh) := by
    unfold base serviceBaseUtility
    cases readout : serviceSourceReadout service.setup service.mode service.deadline
        service.leaks (some control) with
    | none => exact ⟨min_le_left _ _, le_max_left _ _⟩
    | some terminal =>
        simp only [Option.elim_some, Setup.parameterPaymentUtility_parameterOutcome]
        exact ⟨(min_le_right _ _).trans
          (add_le_add (valuation_bounds control trace terminal readout who).1
            (transfer_bounds control trace terminal readout who).1),
          (add_le_add (valuation_bounds control trace terminal readout who).2
            (transfer_bounds control trace terminal readout who).2).trans (le_max_right _ _)⟩
  have chargeBounds : 0 ≤ (if verdict who then deposit who else 0) ∧
      (if verdict who then deposit who else 0) ≤ depositBound := by
    cases verdict who
    · exact ⟨le_rfl, (deposit_bounds who).1.trans (deposit_bounds who).2⟩
    · exact deposit_bounds who
  change _ ≤ base (some control) who - (if verdict who then deposit who else 0) ∧
    base (some control) who - (if verdict who then deposit who else 0) ≤ _
  constructor <;> linarith [baseBounds.1, baseBounds.2, chargeBounds.1, chargeBounds.2]

variable [Fintype Player]

/-- Deferring clients preserve and reflect approximate Nash for valuation plus
the actual audited monetary settlement. Each direction has the existing loss
`2 * timing.deferralError * range`, against all bounded raw-menu deviations. -/
theorem payment_rawClientProfile_isεNash_approximate {Parameter : Type}
    (admission : CommitmentInterface service.setup.program)
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (valuation : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (low : Player → ℝ) (range : ℝ)
    (within : service.SettlementRange parameter
      (service.setup.program.parameterPaymentUtility valuation) sample deposit low
      (fun _ => range))
    (ε : ℝ) (source : Profile (service.sourceModel admission).behavioralSignature) :
    (IsεNash ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun terminal => service.setup.program.parameterPaymentUtility valuation
            (service.setup.parameterOutcome parameter terminal) who)) ε source →
      IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
          service.horizon service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => service.paymentExpectedUtility parameter valuation sample deposit
          history.state who) (ε + 2 * timing.deferralError * range)
        (service.clientProfile admission service.rawMenu timing source)) ∧
    (IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
          service.horizon service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => service.paymentExpectedUtility parameter valuation sample deposit
          history.state who) ε
        (service.clientProfile admission service.rawMenu timing source) →
      IsεNash ((service.sourceModel admission).toBehavioralGameForm
          (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun terminal => service.setup.program.parameterPaymentUtility valuation
            (service.setup.parameterOutcome parameter terminal) who))
        (ε + 2 * timing.deferralError * range) source) := by
  rw [service.paymentExpectedUtility_eq]
  exact service.isεNash_rawClientProfile_approximate admission ordered parameter
    (service.setup.program.parameterPaymentUtility valuation) sample authentic deposit
    nonnegative timing low range within ε source

/-- For every timely contract builder, first-opportunity clients preserve and
reflect the same Nash error for valuation plus the actual monetary settlement.
Bounds include the existing unfinished outcome and both possible audit charges. -/
theorem payment_firstTurnClientProfile_isεNash_iff {Parameter : Type}
    (admission : CommitmentInterface service.setup.program)
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (valuation : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    (turns : Nat) (low : Player → ℝ) (range : ℝ)
    (within : service.SettlementRange parameter
      (service.setup.program.parameterPaymentUtility valuation) sample deposit low
      (fun _ => range))
    (ε : ℝ) (source : Profile (service.sourceModel admission).behavioralSignature) :
    IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
        service.horizon service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
      (fun history who => service.paymentExpectedUtility parameter valuation sample deposit
        history.state who) ε
      (service.clientProfile admission service.rawMenu
        (firstTurnTiming service.setup turns service.mode) source) ↔
    IsεNash ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
      (fun final who => (service.setup.protocolReadout final.state).elim 0
        (fun terminal => service.setup.program.parameterPaymentUtility valuation
          (service.setup.parameterOutcome parameter terminal) who)) ε source := by
  rw [service.paymentExpectedUtility_eq]
  exact service.isεNash_firstTurnClientProfile_iff admission ordered parameter
    (service.setup.program.parameterPaymentUtility valuation) sample authentic deposit
    nonnegative turns low range within ε source

/-- For every admitted source profile, the runtime preserves the joint typed
terminal cells, public default history and monetary receipt vector. This cash law
precedes valuation
and does not assume equilibrium or independent audit verdicts. -/
theorem payment_firstTurnClientProfile_settlement_law
    (admission : CommitmentInterface service.setup.program)
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (turns : Nat)
    (source : Profile (service.sourceModel admission).behavioralSignature) :
    (((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
        service.horizon service.scheduler).runBehavioral
      (service.clientProfile admission service.rawMenu
        (firstTurnTiming service.setup turns service.mode) source)
      (2 * service.horizon + 1)).bind fun final =>
        (service.paymentSettlement sample deposit final.state).map fun receipts =>
          ((serviceSourceReadout service.setup service.mode service.deadline service.leaks
            final.state).map (fun config => (config.state, config.defaults)), receipts)) =
      (service.setup.run (service.setup.decodeBehavioralProfile admission source)).map
        (fun terminal => (some (terminal.state, terminal.defaults), fun who =>
          (transferAmount (service.setup.program.evaluatePayoffs terminal.state) who : ℝ))) := by
  exact service.firstTurnClientProfile_settlement_law admission ordered
    (fun _ => ()) (fun outcome => service.setup.program.publicTransfers outcome.2)
    sample authentic deposit turns source

end Vegas.AsyncServiceSpec
