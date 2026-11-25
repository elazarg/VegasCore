module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.CommonInitialSignal
public import Vegas.Game.ConditionedLedgerPath
public import Vegas.Game.ConditionedClientCompiler
public import Vegas.Game.ConditionedClientSpecification
public import Vegas.Game.ConditionedLedgerConsistency
public import Vegas.Game.ConditionedLedgerRationality
public import Vegas.Game.ClientAssessmentFidelity

@[expose] public section

/-! # Sequential preservation across privately observed initial components -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime
  GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
    {setup : Setup (Player := Player) (L := L)}
    {Signal : Type*} (signal : State L setup.context → Signal)
    (supported : ∀ key, key ∈ (setup.initialDistribution.map signal).support)
    (inside : ∀ key who (site : (setup.conditionInitial signal key).intendedModel.InformationSite
      who) (history : setup.intendedModel.InformationHistory who site.1),
      setup.initialComponent signal key history.1.state)
    {timeouts : EventTimeouts setup.informationGraph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
    {bounds : MessageBounds setup.informationGraph} {horizon : Nat}
    {scheduler : (application setup timeouts leaks).Scheduler}
    {Parameter : Type} {parameter : State L setup.context → Parameter}
    {utility : Parameter × PublicOutcome setup.program → Player → ℝ} {exit : Player → ℝ}
    (spec : ∀ key, ClientSpec (setup.conditionInitial signal key) timeouts leaks bounds horizon
      scheduler parameter utility exit)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended)
    (baseKey : Signal) (read : Player → (application setup timeouts leaks).PlayerView → Signal)
    (observed : ∀ draw ∈ setup.initialDistribution.support,
      ∀ execution : (application setup timeouts leaks).Execution,
      State.Invariant (graph := setup.informationGraph) (setup.eventInputs draw)
        execution.application → ∀ who,
      read who (execution.observe (application setup timeouts leaks) who) = signal draw)

local notation "raw" => bounds.rawMenu timeouts leaks
local notation "globalLaw" => Vegas.initialDistribution setup
local notation "compiled" => compileComponent signal supported inside spec intended equilibrium
/-- A decision callback reads its current view; the inactive information state
has a unique legal action and may use any component. -/
def callbackSignal (who : Player) (info : (application setup timeouts leaks).Info) : Signal :=
  info.elim baseKey (fun entry => read who entry.2)

local notation "infoRead" => callbackSignal (setup := setup) (timeouts := timeouts)
  (leaks := leaks) baseKey read

/-- The single raw assessment implementing the compiled components, with its actual
history beliefs at every information set including those of zero reach. -/
def compiledComponentAssessment :=
  ledger_componentAssessment (raw) supported infoRead observed
    (fun key => (compiled key).assessment)

/-- When the signal is identified at source decisions and readable in each ledger
view, component compilation with the same audit and deposits yields a sequential
equilibrium of the original raw ledger game with its exact intended joint law. -/
theorem compileComponent_sequentialEquilibrium
    (formed : setup.WellFormed)
    (audit : ∀ key, (spec key).evidenceService = (spec baseKey).evidenceService)
    (deposits : ∀ key, (spec key).deposit = (spec baseKey).deposit) :
    let A := compiledComponentAssessment signal supported inside spec intended equilibrium
      baseKey read observed
    A.IsSequentialEquilibrium ((raw).decisionInformationAntichain globalLaw horizon scheduler)
        ((raw).bounded globalLaw horizon scheduler).wellFoundedHistories
        (fun who h => (spec baseKey).payoff who h.state) ∧
      (((raw).run globalLaw horizon scheduler A.strategy).bind fun h =>
        (spec baseKey).observation h.state) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility exit) := by
  let assessments := fun key => (compiled key).assessment
  let A := compiledComponentAssessment signal supported inside spec intended equilibrium
    baseKey read observed
  constructor
  · constructor
    · apply ledger_componentAssessment_rational (raw) read assessments supported infoRead
        observed (fun _ _ _ => rfl)
      intro key
      have eq := conditionInitial_payoff_eq (setup := setup) (signal := signal)
        (spec key) (spec baseKey) (audit key) (deposits key)
      rw [← eq]
      exact (compiled key).equilibrium.1
    · exact ledger_componentAssessment_consistent (raw) supported infoRead observed assessments
        (fun key => (compiled key).equilibrium.2)
  · have decoded := decodeProfile_componentAssessment (raw) supported infoRead observed
      read (fun _ _ _ => rfl) assessments
    have law := (raw).runFrom_stateDistribution globalLaw horizon scheduler A.strategy
      ((raw).protocol globalLaw horizon scheduler).initHistory
    change ((raw).run globalLaw horizon scheduler A.strategy).map _ = _ at law
    change ((raw).run globalLaw horizon scheduler A.strategy).bind
      ((spec baseKey).observation ∘ ExecutionProtocol.History.state) = _
    rw [← PMF.bind_map, law]
    change (((application setup timeouts leaks).finish globalLaw horizon scheduler
      ((raw).decodeProfile globalLaw horizon scheduler A.strategy) none).bind _) = _
    rw [show (raw).decodeProfile globalLaw horizon scheduler A.strategy = _ from decoded]
    exact compileComponent_outcomeDistribution signal supported inside spec intended equilibrium
      read
      observed formed (spec baseKey).observation (fun key => conditionInitial_observation_eq
        (setup := setup) (signal := signal) (spec key) (spec baseKey) (audit key) (deposits key))

local notation "app" => application setup timeouts leaks
local notation "one" => bounds.onePacketMenu timeouts leaks
local notation "component" key => setup.conditionInitial signal key
local notation "componentLaw" key => Vegas.initialDistribution (component key)
local notation "globalAssessment" => compiledComponentAssessment signal supported inside spec
  intended equilibrium baseKey read observed

/-- Any global start at the control of a legal initialized component history has
the complete terminal state law of that component's compiled clients. -/
theorem compiledComponent_runFrom_stateDistribution
    (key : Signal)
    (localStart : ((raw).protocol (componentLaw key) horizon scheduler).History)
    (globalStart : ((raw).protocol globalLaw horizon scheduler).History)
    (control : (app).Control) (started : localStart.state = some control)
    (sameState : globalStart.state = localStart.state) :
    ((raw).runFrom globalLaw horizon scheduler (globalAssessment).strategy globalStart).map
        ExecutionProtocol.History.state =
      (app).finish (componentLaw key) horizon scheduler (compiled key).clients
        localStart.state := by
  rw [(raw).runFrom_stateDistribution, sameState, started]
  have decoded := decodeProfile_componentAssessment (raw) supported infoRead observed read
    (fun _ _ _ => rfl) (fun k => (compiled k).assessment)
  rw [show (raw).decodeProfile globalLaw horizon scheduler (globalAssessment).strategy = _
    from decoded]
  have trace := (raw).toRawTrace (componentLaw key) horizon scheduler localStart.trace
  rw [started] at trace
  change ((app).protocol (serviceInitialDistribution (component key) setup.informationDependencies)
    horizon scheduler).Trace (some control) at trace
  rw [serviceInitialDistribution_eq_inputs (component key)] at trace
  have invariant := reactive_history_invariant timeouts leaks
    ((component key).initialDistribution.map setup.eventInputs) horizon scheduler trace
  obtain ⟨inputs, member, valid⟩ := invariant
  obtain ⟨draw, supportedDraw, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  obtain ⟨selected, globalMember⟩ := mem_support_fiberPosterior (supported key) supportedDraw
  have continuation := finish_signalClients read observed (fun k => (compiled k).clients)
    draw globalMember control valid horizon globalLaw (componentLaw key) (scheduler := scheduler)
  rwa [selected] at continuation

/-- At a represented clean component boundary, the glued raw assessment has
the original intended continuation's full configuration and realized payoff
law. Every supported continuation has a complete readout, no defaults or
failed reveals, and zero audit charges. -/
theorem compiledComponent_continuation_at_sourceBoundary
    (audit : ∀ key, (spec key).evidenceService = (spec baseKey).evidenceService)
    (deposits : ∀ key, (spec key).deposit = (spec baseKey).deposit)
    (key : Signal) (rank : Nat)
    (nativeStart : ((one).protocol (componentLaw key) horizon scheduler).History)
    (localStart : ((raw).protocol (componentLaw key) horizon scheduler).History)
    (globalStart : ((raw).protocol globalLaw horizon scheduler).History)
    (matched : ((reactiveNormalization timeouts) leaks).history (raw)
      (bounds.rawMenu_recall timeouts leaks) (componentLaw key) horizon scheduler localStart =
      (bounds.onePacketRestriction timeouts leaks (componentLaw key) horizon scheduler).history
        nativeStart)
    (sameState : globalStart.state = localStart.state)
    (anchor : (app).Execution)
    (state : nativeStart.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary (component key) timeouts leaks horizon scheduler rank anchor)
    (point : SourceProgram.ProtocolState setup.program)
    (decoded : sourceServicePrefix? (component key) rank anchor.application.config = some point)
    (valid : SourceProgram.ProtocolState.Intended setup.program point) :
    ((raw).runFrom globalLaw horizon scheduler (globalAssessment).strategy globalStart).bind
        (fun final => (spec baseKey).observation final.state) =
      (setup.continuationDistribution (setup.intendedOpeningProfile intended.strategy)
        (some point)).map
        (fun terminal => (some terminal, utility (setup.parameterOutcome parameter terminal))) ∧
    ∀ final ∈ ((raw).runFrom globalLaw horizon scheduler (globalAssessment).strategy
        globalStart).support,
      ∃ (control : (app).Control) (terminal : Config Player L setup.program.terminalCtx),
        final.state = some control ∧
        sourceReadout setup timeouts leaks final.state = some terminal ∧
        control.execution.application.config.defaulted = ∅ ∧
        (∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0) ∧
        ∀ who, TerminalAudit.charge (app).stateTraffic
          ((countAudit timeouts) leaks (spec baseKey).evidenceService.sample)
          final.state who = 0 := by
  have normState := congrArg ExecutionProtocol.History.state matched
  change ((reactiveNormalization timeouts) leaks).state localStart.state = nativeStart.state
    at normState
  rw [state] at normState
  obtain ⟨control, started⟩ : ∃ control, localStart.state = some control := by
    cases current : localStart.state with
    | none =>
        rw [current] at normState
        change none = some _ at normState
        cases normState
    | some control => exact ⟨control, rfl⟩
  have transported := compiledComponent_runFrom_stateDistribution signal supported inside spec
    intended
    equilibrium baseKey read observed key localStart globalStart control started sameState
  obtain ⟨settles, clean⟩ := (compiled key).clients_continuation_at_sourceBoundary rank
    nativeStart localStart matched anchor state boundary point decoded valid
  constructor
  · have sameObservation := conditionInitial_observation_eq (setup := setup) (signal := signal)
      (spec key) (spec baseKey) (audit key) (deposits key)
    change ((raw).runFrom globalLaw horizon scheduler (globalAssessment).strategy globalStart).bind
      ((spec baseKey).observation ∘ ExecutionProtocol.History.state) = _
    rw [← PMF.bind_map, transported, ← sameObservation]
    refine settles.trans ?_
    have profile := setup.conditionInitial_openingProfile signal key intended.strategy
    change (SourceProgram.ProtocolState.continuationDistribution setup.program
      ((component key).intendedOpeningProfile
        (fun who => setup.conditionInitial_policy signal key who (intended.strategy who)))
      point).map _ = _
    rw [profile]
    rfl
  · intro final reached
    have member := (PMF.mem_support_map_iff
      (fun h : ((raw).protocol globalLaw horizon scheduler).History => h.state) _ final.state).mpr
      ⟨final, reached, rfl⟩
    rw [transported] at member
    obtain ⟨outcome, terminal, current, readout, defaults, reveals, charges⟩ := clean _ member
    refine ⟨outcome, terminal, current, ?_, defaults, reveals, ?_⟩
    · rw [current] at readout ⊢
      exact readout
    · simpa only [audit key] using charges

include supported equilibrium in
/-- A single source-observation premise suffices for every player to select its
component. Every supported ledger outcome of the resulting equilibrium is clean. -/
theorem SharesInitialSignal.preservesSequentialEquilibrium
    (common : setup.SharesInitialSignal signal) (formed : setup.WellFormed)
    (audit : ∀ key, (spec key).evidenceService = (spec baseKey).evidenceService)
    (deposits : ∀ key, (spec key).deposit = (spec baseKey).deposit) :
    ∃ A : ((raw).information globalLaw horizon scheduler).BehavioralAssessment,
      A.IsSequentialEquilibrium ((raw).decisionInformationAntichain globalLaw horizon scheduler)
        ((raw).bounded globalLaw horizon scheduler).wellFoundedHistories
        (fun who h => (spec baseKey).payoff who h.state) ∧
      (((raw).run globalLaw horizon scheduler A.strategy).bind fun h =>
        (spec baseKey).observation h.state) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility exit) ∧
      ∀ h ∈ ((raw).run globalLaw horizon scheduler A.strategy).support,
        (∀ control, h.state = some control → control.execution.application.config.defaulted = ∅) ∧
        ∀ who, TerminalAudit.charge (application setup timeouts leaks).stateTraffic
          ((countAudit timeouts) leaks (spec baseKey).evidenceService.sample) h.state who = 0 := by
  let fibers := fun k => common.sourceFiber k (supported k)
  let reader := nativeInitialSignal (setup := setup) (timeouts := timeouts) (leaks := leaks) signal
  let A := compiledComponentAssessment signal supported fibers spec intended equilibrium
    baseKey reader common.native
  obtain ⟨se, outcome⟩ := compileComponent_sequentialEquilibrium signal supported fibers spec
    intended equilibrium baseKey reader common.native formed audit deposits
  refine ⟨A, se, outcome, ?_⟩
  intro h reached
  exact ledger_componentCompilation_clean supported
    (callbackSignal (setup := setup) (timeouts := timeouts) (leaks := leaks) baseKey reader)
    common.native reader (fun _ _ _ => rfl)
    (compileComponent signal supported fibers spec intended equilibrium)
    (spec baseKey).evidenceService audit h reached

end Vegas.SourceProgram.Setup
