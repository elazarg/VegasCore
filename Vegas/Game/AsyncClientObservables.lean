/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.AsyncServiceRawNash
import Vegas.Game.TerminalObservationLaws

/-! # Client laws and observable guarantees under asynchronous service

The common terminal observation retains the typed state, its original inputs
and public result, and the entire realized settlement vector. Its joint law is
within the product deferral error of the source law for every source profile.
Equilibrium assumptions are unnecessary. Event probabilities and bounded
observable expectations inherit lower bounds with the same law error.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
  GameTheory.Enforcement Interaction Vegas.EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)
  (admission : CommitmentInterface service.setup.program)

/-- The actual raw client's common terminal observation, including realized audit settlement. -/
def clientSettlementLaw {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (source : Profile (service.sourceModel admission).behavioralSignature)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (deposit : Player → ℝ) :
    PMF (TerminalObservation service.setup) :=
  let settle := TerminalAudit.settlement
    (serviceBaseUtility service.setup service.mode service.deadline service.leaks utility)
    ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
      service.leaks)
    (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
  ((service.rawMenu.information (serviceInitialLaw service.setup service.mode) service.horizon
    service.scheduler).runBehavioral
      (service.clientProfile admission service.rawMenu timing source)
      (2 * service.horizon + 1)).bind fun final =>
        (settle final.state).map fun payoffs =>
          TerminalObservation.read service.setup
            (serviceSourceReadout service.setup service.mode service.deadline service.leaks
              final.state) payoffs

/-- The source law uses the same fixed terminal-input and public-result reader. -/
def sourceSettlementLaw
    (source : Profile (service.sourceModel admission).behavioralSignature)
    (utility : State L service.setup.program.terminalCtx → Player → ℝ) :
    PMF (TerminalObservation service.setup) :=
  (service.setup.run (service.setup.decodeBehavioralProfile admission source)).map
    (fun state => TerminalObservation.read service.setup (some state) (utility state))

/-- Every source profile's raw clients reproduce its joint law within the
product deferral error. Neither rationality nor a payoff-range premise is needed. -/
theorem clientSettlementLaw_withinTV
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (source : Profile (service.sourceModel admission).behavioralSignature)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (deposit : Player → ℝ) :
    PMF.WithinTV timing.deferralError
      (service.clientSettlementLaw admission timing source sample utility deposit)
      (service.sourceSettlementLaw admission source utility) := by
  have close := sourceServiceClients_clientPolicy_settlement_lawError service.contract
    service.timely timing
    (service.setup.decodeBehavioralProfile admission source)
    (firstTurn_readout_law service.setup service.leaks ordered service.contract service.timely
      turns _ (sourceServiceClientProfile_effective _)) service.rawMenu
    (service.rawMenu_admits admission timing source) sample authentic utility deposit
  convert close.map (Function.uncurry (TerminalObservation.read service.setup)) using 1 <;>
    simp only [clientSettlementLaw, sourceSettlementLaw, PMF.map_bind, PMF.map_comp,
      Function.comp_def, Function.uncurry]
  rfl

/-- A source event's probability lower bound loses at most the deferral error
under the actual raw client law, including the realized settlement. -/
theorem clientSettlementLaw_event_lower_bound
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (source : Profile (service.sourceModel admission).behavioralSignature)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (deposit : Player → ℝ)
    (event : Set (TerminalObservation service.setup))
    (lower : ℝ)
    (sourceLower : lower ≤
      ((service.sourceSettlementLaw admission source utility).toOuterMeasure event).toReal) :
    lower - timing.deferralError ≤
      ((service.clientSettlementLaw admission timing source sample utility deposit).toOuterMeasure
        event).toReal := by
  have close := service.clientSettlementLaw_withinTV admission ordered timing source sample
    authentic utility deposit
  have gap := (abs_le.mp (close event)).1
  linarith

/-- A bounded observable's source expectation lower bound transfers with error
equal to the deferral probability times its range width. Integration is explicit. -/
theorem clientSettlementLaw_expect_lower_bound
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (source : Profile (service.sourceModel admission).behavioralSignature)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (deposit : Player → ℝ)
    (observable : TerminalObservation service.setup → ℝ)
    (low width lower : ℝ)
    (bounded : ∀ result,
      result ∈ (service.clientSettlementLaw admission timing source sample utility deposit).support
        ∨
        result ∈ (service.sourceSettlementLaw admission source utility).support →
      low ≤ observable result ∧ observable result ≤ low + width)
    (sourceLower : lower ≤
      expect (service.sourceSettlementLaw admission source utility) observable) :
    PayoffIntegrable (service.clientSettlementLaw admission timing source sample utility deposit)
        observable ∧
      PayoffIntegrable (service.sourceSettlementLaw admission source utility) observable ∧
      lower - timing.deferralError * width ≤
        expect (service.clientSettlementLaw admission timing source sample utility deposit)
          observable := by
  have absolute (result) (member :
      result ∈ (service.clientSettlementLaw admission timing source sample utility deposit).support
        ∨
        result ∈ (service.sourceSettlementLaw admission source utility).support) :
      |observable result| ≤ |low| + |width| := by
    obtain ⟨below, above⟩ := bounded result member
    exact abs_le.mpr ⟨by linarith [neg_abs_le low, abs_nonneg width],
      by linarith [le_abs_self low, le_abs_self width]⟩
  refine ⟨payoffIntegrable_of_bounded_on_support _ _
    (fun result member => absolute result (Or.inl member)),
    payoffIntegrable_of_bounded_on_support _ _
      (fun result member => absolute result (Or.inr member)), ?_⟩
  have close := service.clientSettlementLaw_withinTV admission ordered timing source sample
    authentic utility deposit
  have gap := close.symm.expect_sub_le observable low width
    (fun result member => bounded result member.symm)
  linarith

end Vegas.AsyncServiceSpec
