module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.CommonInitialSignal
public import Vegas.Game.ConditionedLedgerPath
public import Vegas.Game.ConditionedClientCompiler
public import Vegas.Game.ConditionedClientSpecification
public import Vegas.Game.ConditionedLedgerConsistency
public import Vegas.Game.ConditionedLedgerRationality

@[expose] public section

/-! # Sequential preservation across privately observed initial components -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol Interaction EventGraphRuntime GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
    {setup : Setup (Player := Player) (L := L)}
    {Signal : Type*} (signal : State L setup.context → Signal)
    (supported : ∀ key, key ∈ (setup.initialLaw.map signal).support)
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
    (observed : ∀ draw ∈ setup.initialLaw.support,
      ∀ execution : (application setup timeouts leaks).Execution,
      State.Invariant (graph := setup.informationGraph) (setup.eventInputs draw)
        execution.application → ∀ who,
      read who (execution.observe (application setup timeouts leaks) who) = signal draw)

local notation "raw" => bounds.rawMenu timeouts leaks
local notation "globalLaw" => Vegas.initialLaw setup
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
    have law := (raw).runFrom_stateLaw globalLaw horizon scheduler A.strategy
      ((raw).protocol globalLaw horizon scheduler).initHistory
    change ((raw).run globalLaw horizon scheduler A.strategy).map _ = _ at law
    change ((raw).run globalLaw horizon scheduler A.strategy).bind
      ((spec baseKey).observation ∘ ExecutionProtocol.History.state) = _
    rw [← PMF.bind_map, law]
    change (((application setup timeouts leaks).finish globalLaw horizon scheduler
      ((raw).decodeProfile globalLaw horizon scheduler A.strategy) none).bind _) = _
    rw [show (raw).decodeProfile globalLaw horizon scheduler A.strategy = _ from decoded]
    exact compileComponent_outcomeLaw signal supported inside spec intended equilibrium read
      observed formed (spec baseKey).observation (fun key => conditionInitial_observation_eq
        (setup := setup) (signal := signal) (spec key) (spec baseKey) (audit key) (deposits key))

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
