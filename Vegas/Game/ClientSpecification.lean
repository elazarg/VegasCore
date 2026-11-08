/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketExclusionPayoff
import Vegas.Game.OnePacketPublicInitialSignal
import Vegas.Game.OnePacketRetention
import Vegas.Game.OnePacketSwapFiberSum
import Vegas.Pending.ReactiveAsyncContract
import Vegas.Pending.ReactiveOnePacketMenu
import Vegas.Source.PrivateInputsIndependent

/-! # Specifications and artifacts for native sequential compilation

One specification states the source, bounded raw-menu service and audit obligations.
Its utility bounds concern legal raw-history readouts. A compiled artifact records
native sequential equilibrium and the complete source-configuration/payoff law.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

local notation "Initial" => initialLaw setup
local notation "app" => application setup timeouts leaks
local notation "raw" => bounds.rawMenu timeouts leaks
local notation "model" => ReactiveApplication.ResponseMenu.information
  (bounds.rawMenu timeouts leaks) Initial horizon scheduler

/-- The checked source, service and enforcement obligations of compilation.
The source assessment is supplied separately, so one specification serves
every intended equilibrium of the game. Catalogue coverage includes every
off-path payload value and therefore entails finite binding and publication
value carriers. -/
structure ClientSpec where
  /-- Every physical nature kernel has finite support. -/
  finiteNature : (app).FiniteNature Initial scheduler
  /-- The intended source game has finitely many legal histories. -/
  finiteSource : Finite setup.intendedProtocol.History
  Public : Type
  signal : State L setup.context → Public
  wellFormed : setup.WellFormed
  independent : setup.PrivateInputsIndependentGiven signal
  observable : setup.PublicInitialSignal signal
  delay : (graph setup).EventId → Nat
  bound : (graph setup).EventId → Nat
  opportunity : Opportunity timeouts leaks Initial horizon scheduler delay
  inclusion : ProtectedInclusion timeouts leaks Initial horizon scheduler bound
  completes : CompletesPlay timeouts leaks Initial horizon scheduler
  timely : AsyncTimely timeouts delay bound
  lowerUtility : Player → ℝ
  upperUtility : Player → ℝ
  /-- Bounds cover exactly readouts of legal histories in the supplied raw menu. -/
  lower_le : ∀ history : ((raw).protocol Initial horizon scheduler).History,
    ∀ terminal, sourceReadout setup timeouts leaks history.state = some terminal →
      ∀ who, lowerUtility who ≤ utility (setup.parameterOutcome parameter terminal) who
  le_upper : ∀ history : ((raw).protocol Initial horizon scheduler).History,
    ∀ terminal, sourceReadout setup timeouts leaks history.state = some terminal →
      ∀ who, utility (setup.parameterOutcome parameter terminal) who ≤ upperUtility who
  exitBelow : ∀ (final : setup.intendedProtocol.History) terminal,
    setup.protocolReadout final.state = some terminal →
      ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who
  /-- The finite wire catalogue contains every value of each binding and
  publication payload type, including off-equilibrium values. -/
  outputValues : bounds.CoversOutputValues
  /-- Every value of each initial binding input type belongs to the catalogue. -/
  inputValues : bounds.CoversInputValues
  capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount
  evidenceService : EvidenceReportService (CountEvidence (graph setup))
  observationRate : Player → ℝ
  deliveryRate : Player → ℝ
  delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who
  coverage : CountEvidenceCoverage evidenceService observationRate deliveryRate
  deposit : Player → ℝ
  deposit_nonnegative : ∀ who, 0 ≤ deposit who
  funded : ∀ who,
    max 0 (max (excludedPayoff who) (upperUtility who)) -
        min 0 (min (excludedPayoff who) (lowerUtility who)) ≤
      observationRate who * deliveryRate who * deposit who

variable {setup timeouts leaks bounds horizon scheduler parameter utility excludedPayoff}

variable (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
  parameter utility excludedPayoff)

namespace ClientSpec

/-- The distribution of base utilities after the terminal count-audit deduction. -/
def settlement : (app).ProtocolState → PMF (Player → ℝ) :=
  TerminalAudit.settlement
    (exclusionBase setup timeouts parameter utility excludedPayoff leaks)
    (app).stateTraffic ((countAudit timeouts) leaks spec.evidenceService.sample) spec.deposit

/-- The complete source configuration, including default history, jointly with
the settled-payoff vector of a physical state. -/
def observation (state : (app).ProtocolState) :
    PMF (Option (Config Player L setup.program.terminalCtx) × (Player → ℝ)) :=
  (spec.settlement state).map fun payoffs =>
    (sourceReadout setup timeouts leaks state, payoffs)

/-- A player's expected audited utility at a physical protocol state. -/
def payoff (who : Player) (state : (app).ProtocolState) : ℝ :=
  TerminalAudit.utility
    (exclusionBase setup timeouts parameter utility excludedPayoff leaks)
    (app).stateTraffic ((countAudit timeouts) leaks spec.evidenceService.sample)
    spec.deposit state who

end ClientSpec

/-- A semantic artifact certifying equilibrium in the bounded raw response-menu
game and preserving its source readout and settled payoff law. -/
structure ClientCompilation (intended : setup.intendedModel.BehavioralAssessment) where
  assessment : (model).BehavioralAssessment
  equilibrium : assessment.IsSequentialEquilibriumFor
    ((raw).decisionInformationAntichain Initial horizon scheduler)
    (fun who site => assessment.truncatedContinuationContext site
      (fun final => spec.payoff who final.state) (2 * horizon + 1))
  noDefaults : ∀ final ∈ ((model).runBehavioral assessment.strategy (2 * horizon + 1)).support,
    ∀ control, final.state = some control → control.execution.application.config.defaulted = ∅
  noCharges : ∀ final ∈ ((model).runBehavioral assessment.strategy (2 * horizon + 1)).support,
    ∀ who, TerminalAudit.charge (app).stateTraffic
      ((countAudit timeouts) leaks spec.evidenceService.sample) final.state who = 0
  outcomeLaw : ((model).runBehavioral assessment.strategy (2 * horizon + 1)).bind
      (fun final => spec.observation final.state) =
    (setup.intendedModel.runBehavioral intended.strategy
      (instructionCount setup.program + 1)).map
      (intendedReadoutExclusion setup parameter utility excludedPayoff)


end Vegas
