/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoverySequentialCompilation
import Interaction.ReactiveLedgerAssessment
import Interaction.ReactiveMenuRationality

/-! # A uniform semantic compiler for intended equilibrium clients

The compiler selects a consistent recovery completion at compile time.
Its output certifies equilibrium within the bounded raw response menu and
uniformly decodes its strategies to physical clients. Deviations leaving that
menu are outside the equilibrium certificate. Ledger clients realize those
decision laws when pending observations are not delivered. The completion
backend is nonconstructive.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "app" => recoveryApplication runtime leaks
local notation "raw" => Recovery.rawMenu runtime leaks bounds
local notation "model" => ReactiveApplication.ResponseMenu.information
  (Recovery.rawMenu runtime leaks bounds) Initial horizon scheduler

/-- The checked source, service and enforcement obligations of compilation.
The source assessment is supplied separately, so one specification serves
every intended equilibrium of the game. -/
structure RecoveryClientSpec where
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
  opportunity : Recovery.Opportunity runtime leaks Initial horizon scheduler delay
  inclusion : Recovery.ProtectedInclusion runtime leaks Initial horizon scheduler bound
  completes : Recovery.CompletesPlay runtime leaks Initial horizon scheduler
  timely : AsyncTimely runtime delay bound
  lowerUtility : Player → ℝ
  upperUtility : Player → ℝ
  lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who
  le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who
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

variable {setup runtime leaks bounds horizon scheduler parameter utility excludedPayoff}

variable (spec : RecoveryClientSpec setup runtime leaks bounds horizon scheduler
  parameter utility excludedPayoff)

namespace RecoveryClientSpec

/-- The distribution of base utilities after the terminal count-audit deduction. -/
def settlement : (app).ProtocolState → PMF (Player → ℝ) :=
  TerminalAudit.settlement
    (recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff)
    (app).stateTraffic (Recovery.countAudit runtime leaks spec.evidenceService.sample) spec.deposit

/-- The joint typed-source readout and settled-payoff vector of a physical state. -/
def observation (state : (app).ProtocolState) :
    PMF (Option (State L setup.program.terminalCtx) × (Player → ℝ)) :=
  (spec.settlement state).map fun payoffs =>
    (sourceReadout setup runtime leaks (RecoveryProjection.protocolState runtime leaks state),
      payoffs)

/-- A player's expected audited utility at a physical protocol state. -/
def payoff (who : Player) (state : (app).ProtocolState) : ℝ :=
  TerminalAudit.utility
    (recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff)
    (app).stateTraffic (Recovery.countAudit runtime leaks spec.evidenceService.sample)
    spec.deposit state who

end RecoveryClientSpec

/-- A semantic artifact certifying equilibrium in the bounded raw response-menu
game and preserving its source readout and settled payoff law. -/
structure RecoveryClientCompilation (intended : setup.intendedModel.BehavioralAssessment) where
  assessment : (model).BehavioralAssessment
  equilibrium : assessment.IsSequentialEquilibriumFor
    ((raw).decisionInformationAntichain Initial horizon scheduler)
    (fun who site => assessment.truncatedContinuationContext site
      (fun final => spec.payoff who final.state) (2 * horizon + 1))
  noExclusions : ∀ final ∈ ((model).runBehavioral assessment.strategy (2 * horizon + 1)).support,
    ∀ control, final.state = some control → control.execution.application.excluded = ∅
  noCharges : ∀ final ∈ ((model).runBehavioral assessment.strategy (2 * horizon + 1)).support,
    ∀ who, TerminalAudit.charge (app).stateTraffic
      (Recovery.countAudit runtime leaks spec.evidenceService.sample) final.state who = 0
  outcomeLaw : ((model).runBehavioral assessment.strategy (2 * horizon + 1)).bind
      (fun final => spec.observation final.state) =
    (setup.intendedModel.runBehavioral intended.strategy
      (instructionCount setup.program + 1)).map
      (intendedReadoutExclusion setup parameter utility excludedPayoff)

namespace RecoveryClientSpec

/-- Select a common consistent bounded-menu completion as part of the semantic
artifact. Runtime clients decode this selected strategy. -/
def compile (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended) :
    RecoveryClientCompilation spec intended := by
  classical
  letI := spec.finiteNature
  letI := spec.finiteSource
  have existsTarget := recovery_intended_raw_sequentialEquilibrium_preserved
    (setup := setup) (runtime := runtime) (leaks := leaks) (bounds := bounds)
    (horizon := horizon) (scheduler := scheduler) parameter utility excludedPayoff
    spec.wellFormed spec.independent spec.observable spec.opportunity spec.inclusion spec.completes
    spec.timely spec.lowerUtility spec.upperUtility spec.lower_le spec.le_upper spec.exitBelow
    intended equilibrium spec.outputValues spec.inputValues spec.capacity spec.evidenceService
    spec.observationRate spec.deliveryRate spec.delivery_nonnegative spec.coverage spec.deposit
    spec.deposit_nonnegative spec.funded
  have chosen := Classical.choose_spec existsTarget
  exact ⟨Classical.choose existsTarget, chosen.1, chosen.2.1, chosen.2.2.1, chosen.2.2.2⟩

end RecoveryClientSpec

namespace RecoveryClientCompilation

variable {spec} {intended : setup.intendedModel.BehavioralAssessment}
  (compiled : RecoveryClientCompilation spec intended)

/-- Physical clients for every source game and supplied intended equilibrium. -/
def clients : Player → (app).Policy :=
  (raw).decodeProfile Initial horizon scheduler compiled.assessment.strategy

/-- The same uniform translation with all pending observations erased. -/
def ledgerClients : Player → (app).Policy :=
  (raw).ledgerProfile Initial horizon scheduler compiled.assessment.strategy

/-- Pending observations in the current view and recall do not affect ledger clients. -/
theorem ledgerClients_useLedgerOnly (who : Player) :
    ReactiveApplication.Policy.UsesLedgerOnly (app) (compiled.ledgerClients who) :=
  (raw).ledgerProfile_usesLedgerOnly Initial horizon scheduler compiled.assessment.strategy who

/-- Decoding and restriction recover the complete selected strategy. -/
theorem clients_strategy (who : Player) :
    (raw).restrictPolicy Initial horizon scheduler who (compiled.clients who) =
      compiled.assessment.strategy who :=
  (raw).restrict_decode_embedPolicy Initial horizon scheduler who
    (compiled.assessment.strategy who)

/-- Ordinary clients remain inside the response menu at every legal decision. -/
theorem clients_admissible (who : Player) :
    (raw).Admissible Initial horizon scheduler who (compiled.clients who) :=
  (raw).decodeProfile_admissible Initial horizon scheduler compiled.assessment.strategy who

/-- Every ordinary callback law has finite support in its bounded response menu. -/
theorem clients_support_finite (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) : (compiled.clients who past view).support.Finite := by
  apply ((raw).actions who past view).finite_toSet.subset
  intro response supported
  exact (raw).decode_embedPolicy_covered Initial horizon scheduler who
    (compiled.assessment.strategy who) past view response supported

/-- Erasing pending observations retains finite callback support. -/
theorem ledgerClients_support_finite (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) : (compiled.ledgerClients who past view).support.Finite :=
  compiled.clients_support_finite who
    (past.map (ReactiveApplication.PlayerEntry.ledgerOnly (app))) (view.ledgerOnly (app))

/-- Without pending delivery, ledger clients agree at every legal raw history. -/
theorem ledgerClients_agree
    (unobserved : leaks.DeliversNothing)
    (control : (app).Control)
    (trace : ((app).protocol Initial horizon scheduler).Trace (some control)) (who : Player) :
    compiled.ledgerClients who (control.execution.recall who)
      (control.execution.observe (app) who) =
      compiled.clients who (control.execution.recall who) (control.execution.observe (app) who) :=
  (raw).ledgerProfile_agrees Initial horizon scheduler unobserved
    compiled.assessment.strategy control trace who

/-- The actual ledger client's represented strategy is the selected assessment
at every legal decision input, including zero-probability histories. -/
theorem ledgerClients_strategy_at_history
    (unobserved : leaks.DeliversNothing)
    (history : ((raw).protocol Initial horizon scheduler).History) (who : Player) :
    (raw).restrictPolicy Initial horizon scheduler who (compiled.ledgerClients who)
      ((model).infoOf who history.trace) =
    compiled.assessment.strategy who ((model).infoOf who history.trace) :=
  (raw).restrict_ledgerProfile_history Initial horizon scheduler unobserved
    compiled.assessment.strategy history who

/-- Every menu-admissible physical continuation is unprofitable under the
compiled assessment's belief, at on-path and off-path information sets. -/
theorem clients_sequentiallyRational (who : Player) (site : (model).InformationSite who)
    (alternative : (app).Policy)
    (covered : (raw).Admissible Initial horizon scheduler who alternative) :
    expect ((compiled.assessment.belief who site).bind fun history =>
      (app).finish Initial horizon scheduler (Function.update compiled.clients who alternative)
        history.1.state) (spec.payoff who) ≤
      expect ((compiled.assessment.belief who site).bind fun history =>
        (app).finish Initial horizon scheduler compiled.clients history.1.state)
        (spec.payoff who) := by
  let := spec.finiteNature
  exact (raw).sequentiallyRational_finish Initial horizon scheduler compiled.assessment
    compiled.clients compiled.clients_admissible
    (fun history other =>
      congrFun (compiled.clients_strategy other) ((model).infoOf other history.trace))
    spec.payoff compiled.equilibrium.1 who site alternative covered

/-- Ledger clients are rational against every menu-admissible physical
continuation, with no pending access required of the prescribed clients. -/
theorem ledgerClients_sequentiallyRational (unobserved : leaks.DeliversNothing)
    (who : Player) (site : (model).InformationSite who) (alternative : (app).Policy)
    (covered : (raw).Admissible Initial horizon scheduler who alternative) :
    expect ((compiled.assessment.belief who site).bind fun history =>
      (app).finish Initial horizon scheduler
        (Function.update compiled.ledgerClients who alternative) history.1.state)
        (spec.payoff who) ≤
      expect ((compiled.assessment.belief who site).bind fun history =>
        (app).finish Initial horizon scheduler compiled.ledgerClients history.1.state)
        (spec.payoff who) := by
  let := spec.finiteNature
  exact (raw).sequentiallyRational_finish Initial horizon scheduler compiled.assessment
    compiled.ledgerClients
    ((raw).ledgerProfile_admissible Initial horizon scheduler unobserved
      compiled.assessment.strategy)
    (fun history other => compiled.ledgerClients_strategy_at_history unobserved history other)
    spec.payoff compiled.equilibrium.1 who site alternative covered

/-- Complete physical-state correctness, before applying any outcome reader. -/
theorem clients_stateLaw :
    ((model).runBehavioral compiled.assessment.strategy (2 * horizon + 1)).map History.state =
      (app).finish Initial horizon scheduler compiled.clients none :=
  (raw).run_eq_finish Initial horizon scheduler compiled.assessment.strategy
    (2 * horizon + 1) ((raw).protocol Initial horizon scheduler).initHistory (by rfl)

/-- Correctness of the physical clients, including joint typed readout and settled payoff. -/
theorem clients_outcomeLaw :
    ((app).finish Initial horizon scheduler compiled.clients none).bind (spec.observation) =
    (setup.intendedModel.runBehavioral intended.strategy
      (instructionCount setup.program + 1)).map
      (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  have same := congrArg (fun law => law.bind (spec.observation)) compiled.clients_stateLaw
  rw [PMF.bind_map] at same
  exact same.symm.trans compiled.outcomeLaw

/-- No player is excluded in a supported ordinary-client execution, with any
pending-observation rule satisfying the compilation specification. -/
theorem clients_noExclusions (state : (app).ProtocolState)
    (supported : state ∈ ((app).finish Initial horizon scheduler compiled.clients none).support)
    (control : (app).Control) (current : state = some control) :
    control.execution.application.excluded = ∅ := by
  rw [← compiled.clients_stateLaw] at supported
  obtain ⟨history, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact compiled.noExclusions history reached control (same.trans current)

/-- Supported ordinary-client executions incur no count-audit charge. -/
theorem clients_noCharges (state : (app).ProtocolState)
    (supported : state ∈ ((app).finish Initial horizon scheduler compiled.clients none).support)
    (who : Player) :
    TerminalAudit.charge (app).stateTraffic
      (Recovery.countAudit runtime leaks spec.evidenceService.sample) state who = 0 := by
  rw [← compiled.clients_stateLaw] at supported
  obtain ⟨history, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact compiled.noCharges history reached who

/-- Ledger clients have the same complete continuation law at every legal history. -/
theorem ledgerClients_continuation
    (unobserved : leaks.DeliversNothing)
    (fuel : Nat) (history : ((raw).protocol Initial horizon scheduler).History)
    (enough : (app).rank horizon history.state ≤ fuel) :
    ((model).runBehavioralFrom compiled.assessment.strategy fuel history).map History.state =
      (app).finish Initial horizon scheduler compiled.ledgerClients history.state :=
  (raw).run_ledgerProfile_eq_finish Initial horizon scheduler unobserved
    compiled.assessment.strategy fuel history enough

/-- The initialized physical ledger run has the selected assessment's complete state law. -/
theorem ledgerClients_stateLaw
    (unobserved : leaks.DeliversNothing) :
    ((model).runBehavioral compiled.assessment.strategy (2 * horizon + 1)).map History.state =
      (app).finish Initial horizon scheduler compiled.ledgerClients none :=
  compiled.ledgerClients_continuation unobserved (2 * horizon + 1)
    ((raw).protocol Initial horizon scheduler).initHistory (by rfl)

/-- Ledger and ordinary clients have identical initialized physical execution laws. -/
theorem ledgerClients_finish_eq_clients (unobserved : leaks.DeliversNothing) :
    (app).finish Initial horizon scheduler compiled.ledgerClients none =
      (app).finish Initial horizon scheduler compiled.clients none :=
  (compiled.ledgerClients_stateLaw unobserved).symm.trans compiled.clients_stateLaw

/-- The ledger clients preserve the joint typed-source readout and settled payoff law. -/
theorem ledgerClients_outcomeLaw
    (unobserved : leaks.DeliversNothing) :
    ((app).finish Initial horizon scheduler compiled.ledgerClients none).bind (spec.observation) =
    (setup.intendedModel.runBehavioral intended.strategy
      (instructionCount setup.program + 1)).map
      (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  rw [compiled.ledgerClients_finish_eq_clients unobserved]
  exact compiled.clients_outcomeLaw

/-- Every supported physical ledger-client execution leaves every player included. -/
theorem ledgerClients_noExclusions
    (unobserved : leaks.DeliversNothing)
    (state : (app).ProtocolState)
    (supported : state ∈ ((app).finish Initial horizon scheduler
      compiled.ledgerClients none).support)
    (control : (app).Control) (current : state = some control) :
    control.execution.application.excluded = ∅ := by
  rw [compiled.ledgerClients_finish_eq_clients unobserved] at supported
  exact compiled.clients_noExclusions state supported control current

/-- Supported ledger-client executions incur no count-audit charge. -/
theorem ledgerClients_noCharges
    (unobserved : leaks.DeliversNothing)
    (state : (app).ProtocolState)
    (supported : state ∈ ((app).finish Initial horizon scheduler
      compiled.ledgerClients none).support) (who : Player) :
    TerminalAudit.charge (app).stateTraffic
      (Recovery.countAudit runtime leaks spec.evidenceService.sample) state who = 0 := by
  rw [compiled.ledgerClients_finish_eq_clients unobserved] at supported
  exact compiled.clients_noCharges state supported who

end RecoveryClientCompilation

namespace RecoveryClientSpec

/-- Compiler correctness within the bounded raw menu: equilibrium, exact implemented
strategies, and the joint typed-source/settled-payoff law. -/
theorem compile_correct (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended) :
    let compiled := spec.compile intended equilibrium
    compiled.assessment.IsSequentialEquilibriumFor
      ((raw).decisionInformationAntichain Initial horizon scheduler)
      (fun who site => compiled.assessment.truncatedContinuationContext site
        (fun final => spec.payoff who final.state) (2 * horizon + 1)) ∧
    (∀ who, (raw).restrictPolicy Initial horizon scheduler who (compiled.clients who) =
      compiled.assessment.strategy who) ∧
    ((app).finish Initial horizon scheduler compiled.clients none).bind (spec.observation) =
      (setup.intendedModel.runBehavioral intended.strategy
        (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  intro compiled
  exact ⟨compiled.equilibrium, compiled.clients_strategy, compiled.clients_outcomeLaw⟩

/-- Ledger-client correctness within the bounded raw menu, with strategy agreement at every
legal decision, when the interface does not deliver pending observations. -/
theorem compile_ledger_correct (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended)
    (unobserved : leaks.DeliversNothing) :
    let compiled := spec.compile intended equilibrium
    compiled.assessment.IsSequentialEquilibriumFor
      ((raw).decisionInformationAntichain Initial horizon scheduler)
      (fun who site => compiled.assessment.truncatedContinuationContext site
        (fun final => spec.payoff who final.state) (2 * horizon + 1)) ∧
    (∀ who, ReactiveApplication.Policy.UsesLedgerOnly (app) (compiled.ledgerClients who)) ∧
    (∀ (history : ((raw).protocol Initial horizon scheduler).History) who,
      (raw).restrictPolicy Initial horizon scheduler who (compiled.ledgerClients who)
        ((model).infoOf who history.trace) =
      compiled.assessment.strategy who ((model).infoOf who history.trace)) ∧
    ((app).finish Initial horizon scheduler compiled.ledgerClients none).bind (spec.observation) =
      (setup.intendedModel.runBehavioral intended.strategy
        (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  intro compiled
  exact ⟨compiled.equilibrium, compiled.ledgerClients_useLedgerOnly,
    compiled.ledgerClients_strategy_at_history unobserved,
    compiled.ledgerClients_outcomeLaw unobserved⟩

end RecoveryClientSpec
end Vegas
