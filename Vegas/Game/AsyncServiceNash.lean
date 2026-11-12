/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.AsyncServiceSpec
import Vegas.Game.SourceServiceTurnSettlement
import Vegas.Game.SourceServiceClientPolicy
import Vegas.Game.SourceServiceChoiceSupport
import Vegas.Game.ServiceHonestLaw
import Interaction.ReactiveRawRoundTrace
import GameTheory.Core.Approximate
import Vegas.Game.SourceInformation

/-! # Player-specific best-response errors under asynchronous timing

The turn-counted clients of a source profile use the canonical source model
and an admitting response menu. Under the asynchronous contract, their joint
law of typed outcome and realized settlement is within product deferral error
`δ` of the first-turn law in total variation. A realized audited payoff range
`R` for a given player therefore gives that player an expectation error `δ * R`.

A native approximate Nash equilibrium reflects to source approximate best
responses with each player's own audited payoff range. Conversely, a source
approximate Nash equilibrium yields client approximate best responses when
every first-turn native deviation is bounded by a source deviation. Both
bounds retain the same actual clients, full deviations, and expectation guards.
The payoff interval is required only for supported realized settlements at
initialized raw protocol histories.
-/

noncomputable section
namespace Vegas
open SourceProgram
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime
variable {Player : Type} [DecidableEq Player] [Finite Player]
  {L : IExpr} [IExpr.ResultTypes L]
namespace AsyncServiceSpec
omit [Finite Player] in
private theorem bestResponse_self_iff (form : GameForm Player)
    (utility : form.sig.Outcome → Player → ℝ) (error : ℝ)
    (profile : Profile form.sig) (who : Player) :
    IsεBestResponse form utility error who profile (profile who) ↔
      ∀ replacement,
        UtilityHasExpectation utility who (form.play profile) ∧
        UtilityHasExpectation utility who (form.play (Profile.update profile who replacement)) ∧
        extendedExpectedUtility utility who (form.play (Profile.update profile who replacement)) ≤
          extendedExpectedUtility utility who (form.play profile) + error := by
  unfold IsεBestResponse IsBestResponse
  simp only [Profile.update, Function.update_eq_self]
  rfl

variable (service : AsyncServiceSpec Player L)

/-- Supported realized settlement payoffs at initialized raw protocol histories
lie in the declared player-specific intervals. -/
def SettlementRange {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (deposit : Player → ℝ) (low width : Player → ℝ) : Prop :=
  let app := serviceApplication service.setup service.mode service.duration service.leaks
  let base := serviceBaseUtility service.setup service.mode service.duration service.leaks
    (fun config => utility (service.setup.parameterOutcome parameter config))
  let settle := TerminalAudit.settlement base
    ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
      service.leaks)
    (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
  ∀ control, (app.protocol (serviceInitialLaw service.setup service.mode) service.horizon
    service.scheduler).Trace (some control) →
    ∀ payoffs ∈ (settle (some control)).support, ∀ who,
      low who ≤ payoffs who ∧ payoffs who ≤ low who + width who

/-- Supported realized settlement payoffs at initialized raw protocol histories
lie, through the supplied reader, in the declared player-specific intervals. -/
def ReadoutSettlementRange {Parameter : Type}
    (reader : (serviceApplication service.setup service.mode service.duration
      service.leaks).ProtocolState → Option (Config Player L service.setup.program.terminalCtx))
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (deposit : Player → ℝ) (low width : Player → ℝ) : Prop :=
  let app := serviceApplication service.setup service.mode service.duration service.leaks
  let base := readoutBaseUtility reader
    (fun config => utility (service.setup.parameterOutcome parameter config))
  let settle := TerminalAudit.settlement base
    ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
      service.leaks)
    (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
  ∀ control, (app.protocol (serviceInitialLaw service.setup service.mode) service.horizon
    service.scheduler).Trace (some control) →
    ∀ payoffs ∈ (settle (some control)).support, ∀ who,
      low who ≤ payoffs who ∧ payoffs who ≤ low who + width who

omit [Finite Player] in
private theorem ReadoutSettlementRange.expected {Parameter : Type}
    (reader : (serviceApplication service.setup service.mode service.duration
      service.leaks).ProtocolState → Option (Config Player L service.setup.program.terminalCtx))
    {parameter : State L service.setup.context → Parameter}
    {utility : Parameter × PublicOutcome service.setup.program → Player → ℝ}
    {sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode))}
    {deposit low width : Player → ℝ}
    (within : service.ReadoutSettlementRange reader parameter utility sample deposit low width)
    (control : (serviceApplication service.setup service.mode service.duration
      service.leaks).Control)
    (trace : ((serviceApplication service.setup service.mode service.duration
      service.leaks).protocol
      (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).Trace (some control)) (who : Player) :
    let base := readoutBaseUtility reader
      (fun config => utility (service.setup.parameterOutcome parameter config))
    let payoff := TerminalAudit.utility base
      ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
    low who ≤ payoff (some control) who ∧
      payoff (some control) who ≤ low who + width who := by
  intro base payoff
  let settle := TerminalAudit.settlement base
    ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
      service.leaks)
    (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
  have integrable : PayoffIntegrable (settle (some control)) (fun payoffs => payoffs who) := by
    apply payoffIntegrable_of_bounded_on_support _ _ (C := |low who| + |width who|)
    intro payoffs supported
    obtain ⟨lower, upper⟩ := within control trace payoffs supported who
    exact abs_le.mpr ⟨by linarith [neg_abs_le (low who), abs_nonneg (width who)],
      by linarith [le_abs_self (low who), le_abs_self (width who)]⟩
  have lower := expect_mono
    (fun payoffs supported => (within control trace payoffs supported who).1)
    (payoffIntegrable_constant (settle (some control)) (low who)) integrable
  have upper := expect_le_const (settle (some control)) _ integrable (low who + width who)
    (fun payoffs supported => (within control trace payoffs supported who).2)
  simpa only [expect_constant, settle, TerminalAudit.settlement_expect] using And.intro lower upper


variable (admission : CommitmentInterface service.setup.program)

private theorem clientProfile_value_close {Parameter : Type}
    (reader : (serviceApplication service.setup service.mode service.duration
      service.leaks).ProtocolState → Option (Config Player L service.setup.program.terminalCtx))
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (menu : (serviceApplication service.setup service.mode service.duration
      service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (covered : ∀ (source : Profile (service.sourceModel admission).behavioralSignature) who,
      menu.Admissible (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler who
        (serviceClientPolicy service.setup service.mode service.duration service.leaks
          service.bound turns timing
          (normalizeDisclosureProfile service.setup.program (service.setup.decodeBehavioralProfile
            admission source)) who))
    (low : Player → ℝ) (range : Player → ℝ)
    (within : service.ReadoutSettlementRange reader parameter utility sample deposit low range)
    (source : Profile (service.sourceModel admission).behavioralSignature)
    (terminal : FirstTurnReadoutLaw service.setup service.mode service.duration service.leaks reader
      service.horizon service.scheduler service.bound turns
      (normalizeDisclosureProfile service.setup.program (service.setup.decodeBehavioralProfile
        admission source))) (who : Player) :
    let base := readoutBaseUtility reader
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
    let native := (menu.information (serviceInitialLaw service.setup service.mode) service.horizon
      service.scheduler).runBehavioral (service.clientProfile admission menu timing source)
        (2 * service.horizon + 1)
    let original := (service.sourceModel admission).runBehavioral source
      (instructionCount service.setup.program + 1)
    let sourcePayoff := fun final : (service.setup.executionProtocol
        admission).History =>
      (service.setup.protocolReadout final.state).elim 0
        (fun state => utility (service.setup.parameterOutcome parameter state) who)
    PayoffIntegrable native (fun final => payoff final.state who) ∧
      PayoffIntegrable original sourcePayoff ∧
      expect native (fun final => payoff final.state who) - expect original sourcePayoff ≤
        timing.deferralError * range who ∧
      expect original sourcePayoff - expect native (fun final => payoff final.state who) ≤
        timing.deferralError * range who := by
  let : Fintype Player := Fintype.ofFinite Player
  intro base payoff native original sourcePayoff
  classical
  let app := serviceApplication service.setup service.mode service.duration service.leaks
  let decoded := service.setup.decodeBehavioralProfile admission source
  let normalized := normalizeDisclosureProfile service.setup.program decoded
  let pairUtility := fun result : State L service.setup.program.terminalCtx ×
      DefaultHistory Player =>
    utility (parameter (initialState service.setup.program result.1),
      ⟨sourcePublicEnv result.1, result.2⟩)
  let settle := TerminalAudit.settlement base
    ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
      service.leaks)
    (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
  let readPair := fun state : app.ProtocolState =>
    (reader state).map
      (fun config => (config.state, config.defaults))
  let nativeJoint := native.bind fun final =>
    (settle final.state).map fun payoffs => (readPair final.state, payoffs)
  let sourceJoint := (service.setup.run decoded).map fun config =>
    (some (config.state, config.defaults), pairUtility (config.state, config.defaults))
  have close : PMF.WithinTV timing.deferralError nativeJoint sourceJoint :=
    sourceServiceClients_clientPolicy_settlement_lawError_readout reader service.contract timing
      decoded terminal
      menu (covered source) sample authentic pairUtility deposit
  have rawRange (players : Player → app.Policy) (execution : app.Execution)
      (reached : execution ∈ (app.roundsFrom (serviceInitialLaw service.setup service.mode)
        service.scheduler players service.horizon).support) :
      ∀ payoffs ∈ (settle (app.finished execution)).support,
        low who ≤ payoffs who ∧ payoffs who ≤ low who + range who := by
    obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw service.setup service.mode)
      service.horizon service.scheduler players service.horizon le_rfl execution reached
    exact fun payoffs drawn => within ⟨0, none, execution⟩
      (by simpa only [Nat.sub_self] using trace)
      payoffs drawn who
  have states : native.map (fun final => final.state) =
      (app.roundsFrom (serviceInitialLaw service.setup service.mode) service.scheduler
        (serviceClientPolicy service.setup service.mode service.duration service.leaks
          service.bound turns timing normalized) service.horizon).map app.finished := by
    have physical := menu.run_restrict_eq_finish (serviceInitialLaw service.setup service.mode)
      service.horizon service.scheduler
      (serviceClientPolicy service.setup service.mode service.duration service.leaks
        service.bound turns timing normalized) (covered source) (2 * service.horizon + 1)
      (menu.protocol (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).initHistory le_rfl
    refine physical.trans ?_
    unfold ReactiveApplication.finish ReactiveApplication.roundsFrom
    simp only [PMF.map_bind]
    rfl
  have initialized (final) (supported : final ∈ native.support) :
      ∃ execution, execution ∈ (app.roundsFrom (serviceInitialLaw service.setup service.mode)
        service.scheduler (serviceClientPolicy service.setup service.mode service.duration
          service.leaks service.bound turns timing normalized) service.horizon).support ∧
        app.finished execution = final.state := by
    have mapped : final.state ∈ (native.map (fun current => current.state)).support := by
      rw [PMF.support_map]
      exact ⟨final, supported, rfl⟩
    rw [states, PMF.support_map] at mapped
    exact mapped
  have realized : (app.roundsFrom (serviceInitialLaw service.setup service.mode) service.scheduler
      (serviceTurnPolicy service.setup service.mode service.duration service.leaks service.bound
        turns (firstTurnTiming service.setup turns service.mode) normalized) service.horizon).bind
        (fun execution => (settle (app.finished execution)).map fun payoffs =>
          (readPair (app.finished execution), payoffs)) = sourceJoint := by
    have exactLaw := sourceServiceFirstTurn_settlement_law_readout reader service.contract
      normalized terminal
      sample authentic (fun config => pairUtility (config.state, config.defaults)) deposit
    have mapped := congrArg (PMF.map fun outcome =>
      (outcome.1.map (fun config => (config.state, config.defaults)), outcome.2)) exactLaw
    have normalizedLaw := congrArg
      (PMF.map fun result => (some result, pairUtility result))
      (service.setup.run_normalizeDisclosures_eq decoded)
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def,
      Option.map_some] at mapped normalizedLaw
    exact mapped.trans normalizedLaw
  have bounded : ∀ pair, pair ∈ nativeJoint.support ∨ pair ∈ sourceJoint.support →
      low who ≤ pair.2 who ∧ pair.2 who ≤ low who + range who := by
    rintro pair (member | member)
    · obtain ⟨final, supported, drawn⟩ := PMF.mem_support_bind_iff _ _ _ |>.mp member
      obtain ⟨execution, reached, same⟩ := initialized final supported
      obtain ⟨payoffs, selected, rfl⟩ := PMF.support_map .. ▸ drawn
      rw [← same] at selected
      exact rawRange _ execution reached payoffs selected
    · rw [← realized] at member
      obtain ⟨execution, reached, drawn⟩ := PMF.mem_support_bind_iff _ _ _ |>.mp member
      obtain ⟨payoffs, selected, rfl⟩ := PMF.support_map .. ▸ drawn
      exact rawRange _ execution reached payoffs selected
  have jointIntegrable : PayoffIntegrable nativeJoint (fun pair => pair.2 who) :=
    payoffIntegrable_of_bounded_on_support nativeJoint _ (C := |low who| + |range who|)
      fun pair member => by
        obtain ⟨lower, upper⟩ := bounded pair (Or.inl member)
        exact abs_le.mpr ⟨by linarith [neg_abs_le (low who), abs_nonneg (range who)],
          by linarith [le_abs_self (low who), le_abs_self (range who)]⟩
  have nativeIntegrable : PayoffIntegrable native (fun final => payoff final.state who) := by
    apply payoffIntegrable_of_bounded_on_support native _ (C := |low who| + |range who|)
    intro final supported
    obtain ⟨execution, reached, same⟩ := initialized final supported
    obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw service.setup service.mode)
      service.horizon service.scheduler _ service.horizon le_rfl execution reached
    have bounds := ReadoutSettlementRange.expected service reader within ⟨0, none, execution⟩
      (by simpa only [Nat.sub_self] using trace) who
    change low who ≤ payoff (app.finished execution) who ∧
      payoff (app.finished execution) who ≤ low who + range who at bounds
    rw [same] at bounds
    exact abs_le.mpr ⟨by linarith [bounds.1, neg_abs_le (low who), abs_nonneg (range who)],
      by linarith [bounds.2, le_abs_self (low who), le_abs_self (range who)]⟩
  have nativeValue : expect native (fun final => payoff final.state who) =
      expect nativeJoint (fun pair => pair.2 who) := by
    rw [expect_bind_tower _ _ _ jointIntegrable]
    apply expect_congr_on_support
    intro final _
    rw [expect_map]
    exact (TerminalAudit.settlement_expect base _ _ deposit final.state who).symm
  have readoutLaw : original.map (fun final => service.setup.protocolReadout final.state) =
      (service.setup.run decoded).map some :=
    service.setup.runBehavioralFrom_readout admission source
      (instructionCount service.setup.program + 1)
      (service.setup.executionProtocol admission).initHistory (Nat.le_refl _)
  have sourceValue : expect original sourcePayoff =
      expect sourceJoint (fun pair => pair.2 who) := by
    have mapped := congrArg (fun law => expect law (fun output => output.elim 0
      (fun config => pairUtility (config.state, config.defaults) who))) readoutLaw
    simp only [expect_map] at mapped
    refine mapped.trans ?_
    rw [expect_map]
    rfl
  have := service.setup.finite_history
    (sourceService_finiteBindingTypes service.setup service.bounds service.values) admission
  refine ⟨nativeIntegrable, payoffIntegrable_of_finite _ _, ?_, ?_⟩
  · rw [nativeValue, sourceValue]
    exact close.expect_sub_le _ (low who) (range who) bounded
  · rw [nativeValue, sourceValue]
    exact close.symm.expect_sub_le _ (low who) (range who) fun pair member =>
      bounded pair member.symm

theorem isεBestResponse_of_clientProfile {Parameter : Type}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (menu : (serviceApplication service.setup service.mode service.duration
      service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (covered : ∀ (source : Profile (service.sourceModel admission).behavioralSignature) who,
      menu.Admissible (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler who
        (serviceClientPolicy service.setup service.mode service.duration service.leaks
          service.bound turns timing
          (normalizeDisclosureProfile service.setup.program (service.setup.decodeBehavioralProfile
            admission source)) who))
    (low : Player → ℝ) (range : Player → ℝ)
    (within : service.SettlementRange parameter utility sample deposit low range)
    (ε : ℝ) (source : Profile (service.sourceModel admission).behavioralSignature) :
    let base := serviceBaseUtility service.setup service.mode service.duration service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
    IsεNash (service.gameForm menu)
        (fun history who => payoff history.state who) ε
        (service.clientProfile admission menu timing source) →
      ∀ who, IsεBestResponse ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final player => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) player))
        (ε + 2 * timing.deferralError * range who) who source (source who) := by
  let : Fintype Player := Fintype.ofFinite Player
  intro base payoff native
  rw [isεNash_iff] at native
  intro who
  rw [bestResponse_self_iff]
  intro alternative
  obtain ⟨_, _, compared⟩ :=
    native who (service.clientProfile admission menu timing (Profile.update source who
      alternative) who)
  rw [service.clientProfile_update admission] at compared
  obtain ⟨honestNative, honestSource, honestAbove, honestBelow⟩ :=
    service.clientProfile_value_close admission
    (serviceSourceReadout service.setup service.mode service.duration service.leaks)
    parameter utility sample authentic deposit menu timing covered low range within source
    (firstTurn_readout_law service.setup service.leaks ordered service.contract service.timely
      turns _ (fun who => BehavioralPolicy.normalizeDisclosures_authentic _ _)) who
  obtain ⟨deviationNative, deviationSource, deviationAbove, deviationBelow⟩ :=
    service.clientProfile_value_close admission
    (serviceSourceReadout service.setup service.mode service.duration service.leaks) parameter
      utility sample authentic deposit menu
      timing
      covered low range within (Profile.update source who alternative)
      (firstTurn_readout_law service.setup service.leaks ordered service.contract service.timely
        turns _ (fun who => BehavioralPolicy.normalizeDisclosures_authentic _ _)) who
  let nativeUtility := fun (history : (menu.protocol (serviceInitialLaw service.setup service.mode)
    service.horizon
      service.scheduler).History) (who : Player) => payoff history.state who
  let sourceUtility := fun (final : (service.setup.executionProtocol
      admission).History) (who : Player) =>
    (service.setup.protocolReadout final.state).elim 0
      (fun state => utility (service.setup.parameterOutcome parameter state) who)
  change expect _ (fun final => nativeUtility final who) - _ ≤ _ at honestAbove deviationAbove
  change _ - expect _ (fun final => nativeUtility final who) ≤ _ at honestBelow deviationBelow
  have honestNative': UtilityIntegrable nativeUtility who
      (service.run menu
        (service.clientProfile admission menu timing source)) :=
          honestNative
  have deviationNative' : UtilityIntegrable nativeUtility who
      (service.run menu
        (service.clientProfile admission menu timing (Profile.update source who alternative))) :=
    deviationNative
  have honestSource' : UtilityIntegrable sourceUtility who
      ((service.sourceModel admission).runBehavioral source (instructionCount
        service.setup.program + 1)) :=
    honestSource
  have deviationSource' : UtilityIntegrable sourceUtility who
      ((service.sourceModel admission).runBehavioral (Profile.update source who alternative)
        (instructionCount service.setup.program + 1)) := deviationSource
  change extendedExpectedUtility nativeUtility who
      (service.run menu
        (service.clientProfile admission menu timing (Profile.update source who alternative))) ≤
    extendedExpectedUtility nativeUtility who
      (service.run menu (service.clientProfile admission menu timing source)) + _
    at compared
  rw [extendedExpectedUtility_eq deviationNative', extendedExpectedUtility_eq honestNative',
    ← EReal.coe_add, EReal.coe_le_coe_iff] at compared
  refine ⟨honestSource'.hasExpectation, deviationSource'.hasExpectation, ?_⟩
  change extendedExpectedUtility sourceUtility who _ ≤
    extendedExpectedUtility sourceUtility who _ + _
  rw [extendedExpectedUtility_eq deviationSource', extendedExpectedUtility_eq honestSource',
    ← EReal.coe_add, EReal.coe_le_coe_iff]
  change expect _ _ ≤ expect _ _ + _ at compared
  change expect _ _ ≤ expect _ _ + _
  simp only [AsyncServiceSpec.run, ReactiveApplication.ResponseMenu.run,
    ReactiveApplication.ResponseMenu.runFrom, InformationModel.runBehavioral,
    nativeUtility] at compared honestAbove honestBelow deviationAbove deviationBelow ⊢
  linarith

theorem isεBestResponse_clientProfile_of_firstTurn_bounds_readout {Parameter : Type}
    (reader : (serviceApplication service.setup service.mode service.duration
      service.leaks).ProtocolState → Option (Config Player L service.setup.program.terminalCtx))
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (menu : (serviceApplication service.setup service.mode service.duration
      service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (covered : ∀ (source : Profile (service.sourceModel admission).behavioralSignature) who,
      menu.Admissible (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler who
        (serviceClientPolicy service.setup service.mode service.duration service.leaks
          service.bound turns timing
          (normalizeDisclosureProfile service.setup.program (service.setup.decodeBehavioralProfile
            admission source)) who))
    (low : Player → ℝ) (range : Player → ℝ)
    (within : service.ReadoutSettlementRange reader parameter utility sample deposit low range)
    (ε : ℝ) (source : Profile (service.sourceModel admission).behavioralSignature)
    (terminal : FirstTurnReadoutLaw service.setup service.mode service.duration service.leaks reader
      service.horizon service.scheduler service.bound turns
      (normalizeDisclosureProfile service.setup.program (service.setup.decodeBehavioralProfile
        admission source))) :
    let base := readoutBaseUtility reader
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
    let clients := normalizeDisclosureProfile service.setup.program
      (service.setup.decodeBehavioralProfile admission
        source)
    (∀ who (alternative : (serviceApplication service.setup service.mode service.duration
      service.leaks).Policy),
      ∃ deviation : (service.sourceModel admission).BehavioralPolicy who,
        expect (((serviceApplication service.setup service.mode service.duration
          service.leaks).roundsFrom (serviceInitialLaw service.setup service.mode)
            service.scheduler (deviatedTurnProfile service.bound turns
              (firstTurnTiming service.setup turns service.mode) clients who alternative)
            service.horizon).map (serviceApplication service.setup service.mode service.duration
              service.leaks).finished)
          (fun final => payoff final who) ≤
        expect ((service.sourceModel admission).runBehavioral (Profile.update source who deviation)
          (instructionCount service.setup.program + 1))
          (fun final => (service.setup.protocolReadout final.state).elim 0
            (fun state => utility (service.setup.parameterOutcome parameter state) who))) →
    IsεNash ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source →
      ∀ who, IsεBestResponse
        (service.gameForm menu)
        (fun history player => payoff history.state player)
        (ε + 2 * timing.deferralError * range who) who
        (service.clientProfile admission menu timing source)
        (service.clientProfile admission menu timing source who) := by
  let : Fintype Player := Fintype.ofFinite Player
  intro base payoff clients firstTurn equilibrium
  classical
  let app := serviceApplication service.setup service.mode service.duration service.leaks
  let model := menu.information (serviceInitialLaw service.setup service.mode) service.horizon
    service.scheduler
  let sourceUtility := fun (final : (service.setup.executionProtocol
      admission).History) (who : Player) =>
    (service.setup.protocolReadout final.state).elim 0
      (fun state => utility (service.setup.parameterOutcome parameter state) who)
  let nativeUtility := fun (history : (menu.protocol (serviceInitialLaw service.setup service.mode)
    service.horizon
      service.scheduler).History) (who : Player) => payoff history.state who
  have rawWithin (players : Player → app.Policy) (execution : app.Execution)
      (supported : execution ∈ (app.roundsFrom (serviceInitialLaw service.setup service.mode)
        service.scheduler players service.horizon).support) (player : Player) :
      low player ≤ payoff (app.finished execution) player ∧
        payoff (app.finished execution) player ≤ low player + range player := by
    obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw service.setup service.mode)
      service.horizon service.scheduler players service.horizon le_rfl execution supported
    exact ReadoutSettlementRange.expected service reader within ⟨0, none, execution⟩
      (by simpa only [Nat.sub_self] using trace) player
  rw [isεNash_iff] at equilibrium
  intro who
  rw [bestResponse_self_iff]
  intro replacement
  let alternative := app.decodePolicy (menu.embedPolicy (serviceInitialLaw service.setup
    service.mode)
    service.horizon service.scheduler who replacement)
  let players := Function.update (serviceClientPolicy service.setup service.mode service.duration
    service.leaks
    service.bound turns timing clients) who alternative
  let turnPlayers := deviatedTurnProfile service.bound turns timing clients who alternative
  have completed : app.roundsFrom (serviceInitialLaw service.setup service.mode) service.scheduler
    players
      service.horizon =
      app.roundsFrom (serviceInitialLaw service.setup service.mode) service.scheduler turnPlayers
        service.horizon :=
    sourceServiceClientPolicy_deviation_roundsFrom service.scheduler service.bound turns timing
      clients who alternative service.horizon
  have admissible : ∀ player, menu.Admissible (serviceInitialLaw service.setup service.mode)
    service.horizon
      service.scheduler player (players player) := by
    intro player
    by_cases same : player = who
    · subst same
      intro control _ _ action member
      simp only [players, Function.update_self] at member
      exact menu.decode_embedPolicy_covered (serviceInitialLaw service.setup service.mode)
        service.horizon
        service.scheduler player replacement _ _ action member
    · simp only [players, Function.update_of_ne same]
      exact covered source player
  have restricted : (fun player => menu.restrictPolicy (serviceInitialLaw service.setup
    service.mode)
      service.horizon service.scheduler player (players player)) =
      Profile.update (service.clientProfile admission menu timing source) who replacement := by
    funext player
    by_cases same : player = who
    · subst same
      simp only [players, Function.update_self, Profile.update]
      exact menu.restrict_decode_embedPolicy (serviceInitialLaw service.setup service.mode)
        service.horizon
        service.scheduler player replacement
    · simp only [players, Function.update_of_ne same, Profile.update]
      rfl
  have physical := menu.run_restrict_eq_finish (serviceInitialLaw service.setup service.mode)
    service.horizon
    service.scheduler players admissible (2 * service.horizon + 1)
    (menu.protocol (serviceInitialLaw service.setup service.mode) service.horizon
      service.scheduler).initHistory le_rfl
  rw [restricted] at physical
  have deviationLaw : (model.runBehavioral
      (Profile.update (service.clientProfile admission menu timing source) who replacement)
      (2 * service.horizon + 1)).map History.state =
      (app.roundsFrom (serviceInitialLaw service.setup service.mode) service.scheduler players
        service.horizon).map app.finished := by
    refine physical.trans ?_
    unfold ReactiveApplication.roundsFrom
    simp only [ReactiveApplication.finish, PMF.map_bind]
    rfl
  rw [completed] at deviationLaw
  -- The turn-counted and first-turn deviations are close.
  have coupled := deviatedTurnProfile_roundsFrom_bind_within
    (serviceInitialLaw service.setup service.mode) service.scheduler service.horizon service.bound
    timing clients who alternative (fun execution => PMF.pure execution)
  simp only [PMF.bind_pure] at coupled
  let limit := deviatedTurnProfile service.bound turns (firstTurnTiming service.setup turns
    service.mode)
    clients who alternative
  have deviationGap : expect (app.roundsFrom (serviceInitialLaw service.setup service.mode)
    service.scheduler
        turnPlayers service.horizon) (fun execution => payoff (app.finished execution) who) -
      expect (app.roundsFrom (serviceInitialLaw service.setup service.mode) service.scheduler limit
        service.horizon)
        (fun execution => payoff (app.finished execution) who) ≤
      timing.deferralError * range who :=
    by
      apply coupled.expect_sub_le (fun execution => payoff (app.finished execution) who)
        (low who) (range who)
      intro execution supported
      rcases supported with supported | supported
      · exact rawWithin turnPlayers execution supported who
      · exact rawWithin limit execution supported who
  obtain ⟨deviation, firstBound⟩ := firstTurn who alternative
  rw [expect_map] at firstBound
  have firstBound' : expect (app.roundsFrom (serviceInitialLaw service.setup service.mode)
    service.scheduler limit
        service.horizon) (fun execution => payoff (app.finished execution) who) ≤
      expect ((service.sourceModel admission).runBehavioral (Profile.update source who deviation)
        (instructionCount service.setup.program + 1)) (fun final => sourceUtility final who) :=
    firstBound
  obtain ⟨sourceHonest, sourceDeviation, sourceCompared⟩ := equilibrium who deviation
  -- Honest closeness.
  have honestClose := service.clientProfile_value_close admission reader parameter utility sample
    authentic
    deposit menu timing covered low range within source terminal who
  obtain ⟨honestIntegrable, sourceIntegrable, _, honestBelow⟩ := honestClose
  have finiteHistory := service.setup.finite_history
    (sourceService_finiteBindingTypes service.setup service.bounds service.values)
    admission
  have deviationIntegrable : UtilityIntegrable sourceUtility who
      ((service.sourceModel admission).runBehavioral (Profile.update source who deviation)
        (instructionCount service.setup.program + 1)) := payoffIntegrable_of_finite _ _
  have sourceIntegrable' : UtilityIntegrable sourceUtility who
      ((service.sourceModel admission).runBehavioral source (instructionCount
        service.setup.program + 1)) :=
    sourceIntegrable
  change extendedExpectedUtility sourceUtility who _ ≤
    extendedExpectedUtility sourceUtility who _ + _ at sourceCompared
  rw [extendedExpectedUtility_eq deviationIntegrable, extendedExpectedUtility_eq sourceIntegrable',
    ← EReal.coe_add, EReal.coe_le_coe_iff] at sourceCompared
  have nativeDeviationIntegrable : UtilityIntegrable nativeUtility who
      (model.runBehavioral (Profile.update (service.clientProfile admission menu timing source) who
        replacement) (2 * service.horizon + 1)) :=
    by
      apply payoffIntegrable_of_bounded_on_support _ _ (C := |low who| + |range who|)
      intro history supported
      have mapped : history.state ∈ ((model.runBehavioral
          (Profile.update (service.clientProfile admission menu timing source) who replacement)
          (2 * service.horizon + 1)).map History.state).support := by
        rw [PMF.support_map]
        exact ⟨history, supported, rfl⟩
      rw [deviationLaw, PMF.support_map] at mapped
      obtain ⟨execution, reached, same⟩ := mapped
      obtain ⟨lower, upper⟩ := rawWithin turnPlayers execution reached who
      change |payoff history.state who| ≤ _
      rw [← same]
      exact abs_le.mpr ⟨by linarith [neg_abs_le (low who), abs_nonneg (range who)],
        by linarith [le_abs_self (low who), le_abs_self (range who)]⟩
  have nativeHonestIntegrable : UtilityIntegrable nativeUtility who
      (model.runBehavioral (service.clientProfile admission menu timing source)
        (2 * service.horizon + 1)) := honestIntegrable
  refine ⟨nativeHonestIntegrable.hasExpectation, nativeDeviationIntegrable.hasExpectation, ?_⟩
  change extendedExpectedUtility nativeUtility who _ ≤
    extendedExpectedUtility nativeUtility who _ + _
  rw [extendedExpectedUtility_eq nativeDeviationIntegrable,
    extendedExpectedUtility_eq nativeHonestIntegrable, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have deviationValue : expectedUtility nativeUtility who
      (model.runBehavioral (Profile.update (service.clientProfile admission menu timing source) who
        replacement) (2 * service.horizon + 1)) =
      expect (app.roundsFrom (serviceInitialLaw service.setup service.mode) service.scheduler
        turnPlayers
        service.horizon) (fun execution => payoff (app.finished execution) who) := by
    unfold expectedUtility
    have mapped := congrArg (fun law => expect law (fun state => payoff state who)) deviationLaw
    simp only [expect_map] at mapped
    exact mapped
  change expect _ _ - expect _ _ ≤ _ at honestBelow
  change expect ((service.sourceModel admission).runBehavioral source _) (fun final =>
    sourceUtility final who)
    - expect (model.runBehavioral (service.clientProfile admission menu timing source) _)
      (fun history => nativeUtility history who) ≤ _ at honestBelow
  change expectedUtility nativeUtility who _ ≤ expectedUtility nativeUtility who _ + _
  rw [deviationValue]
  unfold expectedUtility
  change expect _ (fun final => sourceUtility final who) ≤
    expect _ (fun final => sourceUtility final who) + ε at sourceCompared
  linarith

/-- The service-reader instance of `isεBestResponse_clientProfile_of_firstTurn_bounds_readout`. -/
theorem isεBestResponse_clientProfile_of_firstTurn_bounds {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (menu : (serviceApplication service.setup service.mode service.duration
      service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (covered : ∀ (source : Profile (service.sourceModel admission).behavioralSignature) who,
      menu.Admissible (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler who
        (serviceClientPolicy service.setup service.mode service.duration service.leaks
          service.bound turns timing
          (normalizeDisclosureProfile service.setup.program (service.setup.decodeBehavioralProfile
            admission source)) who))
    (low : Player → ℝ) (range : Player → ℝ)
    (within : service.SettlementRange parameter utility sample deposit low range)
    (ε : ℝ) (source : Profile (service.sourceModel admission).behavioralSignature)
    (terminal : FirstTurnSourceLaw service.setup service.mode service.duration service.leaks
      service.horizon service.scheduler service.bound turns
      (normalizeDisclosureProfile service.setup.program (service.setup.decodeBehavioralProfile
        admission source))) :
    let base := serviceBaseUtility service.setup service.mode service.duration service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
    let clients := normalizeDisclosureProfile service.setup.program
      (service.setup.decodeBehavioralProfile admission
        source)
    (∀ who (alternative : (serviceApplication service.setup service.mode service.duration
      service.leaks).Policy),
      ∃ deviation : (service.sourceModel admission).BehavioralPolicy who,
        expect (((serviceApplication service.setup service.mode service.duration
          service.leaks).roundsFrom (serviceInitialLaw service.setup service.mode)
            service.scheduler (deviatedTurnProfile service.bound turns
              (firstTurnTiming service.setup turns service.mode) clients who alternative)
            service.horizon).map (serviceApplication service.setup service.mode service.duration
              service.leaks).finished)
          (fun final => payoff final who) ≤
        expect ((service.sourceModel admission).runBehavioral (Profile.update source who deviation)
          (instructionCount service.setup.program + 1))
          (fun final => (service.setup.protocolReadout final.state).elim 0
            (fun state => utility (service.setup.parameterOutcome parameter state) who))) →
    IsεNash ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source →
      ∀ who, IsεBestResponse
        (service.gameForm menu)
        (fun history player => payoff history.state player)
        (ε + 2 * timing.deferralError * range who) who
        (service.clientProfile admission menu timing source)
        (service.clientProfile admission menu timing source who) :=
  service.isεBestResponse_clientProfile_of_firstTurn_bounds_readout admission
    (serviceSourceReadout service.setup service.mode service.duration service.leaks)
    parameter utility sample authentic deposit menu timing covered low range within ε source
      terminal

end AsyncServiceSpec
end Vegas
