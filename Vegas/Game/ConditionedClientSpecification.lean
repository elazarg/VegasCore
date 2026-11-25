module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveConditionedMenu
public import Vegas.Game.ConditionedCompilationDistribution

@[expose] public section

/-! # Restricting the compiler's service and funding hypotheses to an initial component -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
    {setup : Setup (Player := Player) (L := L)}
    {Signal : Type*} (signal : State L setup.context → Signal)
    {timeouts : EventTimeouts setup.informationGraph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
    {bounds : MessageBounds setup.informationGraph} {horizon : Nat}
    {scheduler : (application setup timeouts leaks).Scheduler}
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ) (exit : Player → ℝ)

local notation "app" => application setup timeouts leaks
local notation "raw" => bounds.rawMenu timeouts leaks
local notation "one" => bounds.onePacketMenu timeouts leaks
local notation "initial" => Vegas.initialDistribution setup

omit [Fintype Player] in
/-- Before audit deductions, a player's utility at a fixed native state is independent of
the initial-law component used to reach that state. -/
theorem conditionInitial_exclusionBase (key : Signal) :
    exclusionBase (setup.conditionInitial signal key) timeouts parameter utility exit leaks =
      exclusionBase setup timeouts parameter utility exit leaks := by
  funext state who
  cases state <;> rfl

/-- A common service, menu and pairwise funding certificate supplies each supported
component's specification once that component's prior condition is proved. -/
def conditionInitial_clientSpec
    (nature : (app).FiniteNature initial scheduler)
    (formed : setup.WellFormed)
    {delay bound : setup.informationGraph.EventId → Nat}
    (service : AsyncContract timeouts leaks initial horizon scheduler delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (exitBelow : ∀ h : setup.intendedProtocol.History,
      ∀ result, setup.protocolReadout h.state = some result → ∀ who,
        exit who ≤ utility (setup.parameterOutcome parameter result) who)
    (outputs : bounds.CoversOutputValues) (inputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount setup.informationGraph who < bounds.candidateCount)
    (evidence : EvidenceReportService (CountEvidence setup.informationGraph))
    (capture delivery deposit : Player → ℝ) (deliveryNonneg : ∀ who, 0 ≤ delivery who)
    (coverage : CountEvidenceCoverage evidence capture delivery)
    (depositNonneg : ∀ who, 0 ≤ deposit who)
    (funded : ∀ (compliant : ((one).protocol initial horizon scheduler).TerminalHistory)
      (deviating : ((raw).protocol initial horizon scheduler).TerminalHistory) who,
      exclusionBase setup timeouts parameter utility exit leaks deviating.1.state who -
        exclusionBase setup timeouts parameter utility exit leaks compliant.1.state who ≤
          capture who * delivery who * deposit who)
    (key : Signal) (supported : key ∈ (setup.initialDistribution.map signal).support)
    (prior : SequentialPriorCondition (setup.conditionInitial signal key) timeouts leaks
      bounds horizon scheduler) :
    ClientSpec (setup.conditionInitial signal key) timeouts leaks bounds horizon scheduler
      parameter utility exit where
  finiteNature := setup.conditionInitial_finiteNature signal key supported nature
  wellFormed := setup.conditionInitial_wellFormed signal key supported formed
  prior := prior
  delay := delay
  bound := bound
  opportunity := (setup.conditionInitial_asyncContract signal key supported service).opportunity
  inclusion := (setup.conditionInitial_asyncContract signal key supported service).inclusion
  completes := (setup.conditionInitial_asyncContract signal key supported service).completes
  timely := timely
  exitBelow h result same who := exitBelow (setup.conditionInitial_history signal key supported h)
    result same who
  outputValues := outputs
  inputValues := inputs
  capacity := capacity
  evidenceService := evidence
  observationRate := capture
  deliveryRate := delivery
  delivery_nonnegative := deliveryNonneg
  coverage := coverage
  deposit := deposit
  deposit_nonnegative := depositNonneg
  funded compliant deviating who := by
    have included := setup.conditionInitial_ledgerSupport signal key supported
    rw [conditionInitial_exclusionBase signal parameter utility exit key]
    exact funded
      ⟨(one).historyOfInitialSupportSubset included compliant.1, compliant.2⟩
      ⟨(raw).historyOfInitialSupportSubset included deviating.1, deviating.2⟩ who

variable {signal parameter utility exit} {first second : Signal}
    (spec₁ : ClientSpec (setup.conditionInitial signal first) timeouts leaks bounds horizon
      scheduler parameter utility exit)
    (spec₂ : ClientSpec (setup.conditionInitial signal second) timeouts leaks bounds horizon
      scheduler parameter utility exit)

/-- Components using the same deposit and report service have identical physical observations,
including the joint distribution of all realized payoffs. -/
theorem conditionInitial_observation_eq
    (evidence : spec₁.evidenceService = spec₂.evidenceService)
    (deposit : spec₁.deposit = spec₂.deposit) : spec₁.observation = spec₂.observation := by
  funext state
  unfold ClientSpec.observation ClientSpec.settlement
  simp only [conditionInitial_exclusionBase, evidence, deposit]
  rfl

/-- With the same audit service and deposits, expected native utilities also agree off path. -/
theorem conditionInitial_payoff_eq
    (evidence : spec₁.evidenceService = spec₂.evidenceService)
    (deposit : spec₁.deposit = spec₂.deposit) : spec₁.payoff = spec₂.payoff := by
  funext who state
  unfold ClientSpec.payoff
  simp only [conditionInitial_exclusionBase, evidence, deposit]

end Vegas.SourceProgram.Setup
