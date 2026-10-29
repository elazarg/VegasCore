/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoverySequentialCompilation
import Interaction.ReactiveLedgerAssessment

/-! # A uniform semantic compiler for intended equilibrium clients

The compiler selects the existing checked recovery completion at compile time.
Its output contains the assessment and its proof, and uniformly decodes its
strategies to physical clients. Ledger clients realize the same assessment at
every legal history when pending observations are not delivered. The completion
backend is nonconstructive; this module does not claim executable synthesis.
-/

noncomputable section

namespace Vegas.RecoveryCompiler

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
structure Specification where
  finiteNature : (app).FiniteNature Initial scheduler
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
  outputValues : bounds.CoversOutputValues
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

abbrev SourceEquilibrium (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (intended : setup.intendedModel.BehavioralAssessment) : Prop :=
  intended.IsSequentialEquilibrium setup.intended_decision_antichain
    setup.intended_bounded.wellFoundedHistories
    (fun who final => (setup.protocolReadout final.state).elim 0
      (fun terminal => utility (setup.parameterOutcome parameter terminal) who))

variable (spec : Specification setup runtime leaks bounds horizon scheduler
  parameter utility excludedPayoff)

def settlement : (app).ProtocolState → PMF (Player → ℝ) :=
  TerminalAudit.settlement
    (recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff)
    (app).stateTraffic (Recovery.countAudit runtime leaks spec.evidenceService.sample) spec.deposit

def observation (state : (app).ProtocolState) :
    PMF (Option (State L setup.program.terminalCtx) × (Player → ℝ)) :=
  (settlement spec state).map fun payoffs =>
    (sourceReadout setup runtime leaks (RecoveryProjection.protocolState runtime leaks state),
      payoffs)

def payoff (who : Player) (state : (app).ProtocolState) : ℝ :=
  TerminalAudit.utility
    (recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff)
    (app).stateTraffic (Recovery.countAudit runtime leaks spec.evidenceService.sample)
    spec.deposit state who

/-- A compiled semantic artifact, including the completion's correctness certificate. -/
structure Compilation (intended : setup.intendedModel.BehavioralAssessment) where
  assessment : (model).BehavioralAssessment
  equilibrium : assessment.IsSequentialEquilibriumFor
    ((raw).decisionInformationAntichain Initial horizon scheduler)
    (fun who site => assessment.truncatedContinuationContext site
      (fun final => payoff spec who final.state) (2 * horizon + 1))
  noExclusions : ∀ final ∈ ((model).runBehavioral assessment.strategy (2 * horizon + 1)).support,
    ∀ control, final.state = some control → control.execution.application.excluded = ∅
  noCharges : ∀ final ∈ ((model).runBehavioral assessment.strategy (2 * horizon + 1)).support,
    ∀ who, TerminalAudit.charge (app).stateTraffic
      (Recovery.countAudit runtime leaks spec.evidenceService.sample) final.state who = 0
  outcomeLaw : ((model).runBehavioral assessment.strategy (2 * horizon + 1)).bind
      (fun final => observation spec final.state) =
    (setup.intendedModel.runBehavioral intended.strategy
      (instructionCount setup.program + 1)).map
      (intendedReadoutExclusion setup parameter utility excludedPayoff)

/-- Uniform semantic compilation. The existing common completion is selected
once as part of the compiled artifact, rather than by a player's runtime code. -/
def compile (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : SourceEquilibrium parameter utility intended) : Compilation spec intended := by
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
  exact ⟨Classical.choose existsTarget, (Classical.choose_spec existsTarget).1,
    (Classical.choose_spec existsTarget).2.1, (Classical.choose_spec existsTarget).2.2.1,
    (Classical.choose_spec existsTarget).2.2.2⟩

namespace Compilation

variable {spec} {intended : setup.intendedModel.BehavioralAssessment}
  (compiled : Compilation spec intended)

/-- Physical clients for every source game and supplied intended equilibrium. -/
def clients : Player → (app).Policy :=
  (raw).decodeProfile Initial horizon scheduler compiled.assessment.strategy

/-- The same uniform translation with all pending observations erased. -/
def ledgerClients : Player → (app).Policy :=
  (raw).ledgerProfile Initial horizon scheduler compiled.assessment.strategy

theorem ledgerClients_useLedgerOnly (who : Player) :
    ReactiveApplication.Policy.UsesLedgerOnly (app) (compiled.ledgerClients who) :=
  (raw).ledgerProfile_usesLedgerOnly Initial horizon scheduler compiled.assessment.strategy who

/-- Decoding and restriction recover the complete selected strategy. -/
theorem clients_strategy (who : Player) :
    (raw).restrictPolicy Initial horizon scheduler who (compiled.clients who) =
      compiled.assessment.strategy who :=
  (raw).restrict_decode_embedPolicy Initial horizon scheduler who
    (compiled.assessment.strategy who)

theorem clients_support_finite (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) : (compiled.clients who past view).support.Finite := by
  apply ((raw).actions who past view).finite_toSet.subset
  intro response supported
  exact (raw).decode_embedPolicy_covered Initial horizon scheduler who
    (compiled.assessment.strategy who) past view response supported

theorem ledgerClients_support_finite (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) : (compiled.ledgerClients who past view).support.Finite :=
  compiled.clients_support_finite who
    (past.map (ReactiveApplication.PlayerEntry.ledgerOnly (app))) (view.ledgerOnly (app))

/-- Without pending delivery, ledger clients agree at every legal raw history. -/
theorem ledgerClients_agree
    (unobserved : ∀ who pending, leaks who pending = PMF.pure ∅)
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
    (unobserved : ∀ who pending, leaks who pending = PMF.pure ∅)
    (history : ((raw).protocol Initial horizon scheduler).History) (who : Player) :
    (raw).restrictPolicy Initial horizon scheduler who (compiled.ledgerClients who)
      ((model).infoOf who history.trace) =
    compiled.assessment.strategy who ((model).infoOf who history.trace) :=
  (raw).restrict_ledgerProfile_history Initial horizon scheduler unobserved
    compiled.assessment.strategy history who

/-- Complete physical-state correctness, before applying any outcome reader. -/
theorem clients_stateLaw :
    ((model).runBehavioral compiled.assessment.strategy (2 * horizon + 1)).map History.state =
      (app).finish Initial horizon scheduler compiled.clients none :=
  (raw).run_eq_finish Initial horizon scheduler compiled.assessment.strategy
    (2 * horizon + 1) ((raw).protocol Initial horizon scheduler).initHistory (by rfl)

/-- Correctness of the physical clients, including joint typed readout and settled payoff. -/
theorem clients_outcomeLaw :
    ((app).finish Initial horizon scheduler compiled.clients none).bind (observation spec) =
    (setup.intendedModel.runBehavioral intended.strategy
      (instructionCount setup.program + 1)).map
      (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  have same := congrArg (fun law => law.bind (observation spec)) compiled.clients_stateLaw
  rw [PMF.bind_map] at same
  exact same.symm.trans compiled.outcomeLaw

/-- Ledger clients have the same complete continuation law at every legal history. -/
theorem ledgerClients_continuation
    (unobserved : ∀ who pending, leaks who pending = PMF.pure ∅)
    (fuel : Nat) (history : ((raw).protocol Initial horizon scheduler).History)
    (enough : (app).rank horizon history.state ≤ fuel) :
    ((model).runBehavioralFrom compiled.assessment.strategy fuel history).map History.state =
      (app).finish Initial horizon scheduler compiled.ledgerClients history.state :=
  (raw).run_ledgerProfile_eq_finish Initial horizon scheduler unobserved
    compiled.assessment.strategy fuel history enough

theorem ledgerClients_stateLaw
    (unobserved : ∀ who pending, leaks who pending = PMF.pure ∅) :
    ((model).runBehavioral compiled.assessment.strategy (2 * horizon + 1)).map History.state =
      (app).finish Initial horizon scheduler compiled.ledgerClients none :=
  compiled.ledgerClients_continuation unobserved (2 * horizon + 1)
    ((raw).protocol Initial horizon scheduler).initHistory (by rfl)

theorem ledgerClients_outcomeLaw
    (unobserved : ∀ who pending, leaks who pending = PMF.pure ∅) :
    ((app).finish Initial horizon scheduler compiled.ledgerClients none).bind (observation spec) =
    (setup.intendedModel.runBehavioral intended.strategy
      (instructionCount setup.program + 1)).map
      (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  have same := congrArg (fun law => law.bind (observation spec))
    (compiled.ledgerClients_stateLaw unobserved)
  rw [PMF.bind_map] at same
  exact same.symm.trans compiled.outcomeLaw

/-- Every supported physical ledger-client execution leaves every player included. -/
theorem ledgerClients_noExclusions
    (unobserved : ∀ who pending, leaks who pending = PMF.pure ∅)
    (state : (app).ProtocolState)
    (supported : state ∈ ((app).finish Initial horizon scheduler
      compiled.ledgerClients none).support)
    (control : (app).Control) (current : state = some control) :
    control.execution.application.excluded = ∅ := by
  rw [← compiled.ledgerClients_stateLaw unobserved] at supported
  obtain ⟨history, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact compiled.noExclusions history reached control (same.trans current)

theorem ledgerClients_noCharges
    (unobserved : ∀ who pending, leaks who pending = PMF.pure ∅)
    (state : (app).ProtocolState)
    (supported : state ∈ ((app).finish Initial horizon scheduler
      compiled.ledgerClients none).support) (who : Player) :
    TerminalAudit.charge (app).stateTraffic
      (Recovery.countAudit runtime leaks spec.evidenceService.sample) state who = 0 := by
  rw [← compiled.ledgerClients_stateLaw unobserved] at supported
  obtain ⟨history, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact compiled.noCharges history reached who

end Compilation

/-- Uniform compiler correctness: sequential equilibrium, exact implemented
strategies, and the joint typed-source/settled-payoff law. -/
theorem compile_correct (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : SourceEquilibrium parameter utility intended) :
    let compiled := compile spec intended equilibrium
    compiled.assessment.IsSequentialEquilibriumFor
      ((raw).decisionInformationAntichain Initial horizon scheduler)
      (fun who site => compiled.assessment.truncatedContinuationContext site
        (fun final => payoff spec who final.state) (2 * horizon + 1)) ∧
    (∀ who, (raw).restrictPolicy Initial horizon scheduler who (compiled.clients who) =
      compiled.assessment.strategy who) ∧
    ((app).finish Initial horizon scheduler compiled.clients none).bind (observation spec) =
      (setup.intendedModel.runBehavioral intended.strategy
        (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  intro compiled
  exact ⟨compiled.equilibrium, compiled.clients_strategy, compiled.clients_outcomeLaw⟩

/-- Uniform ledger-client correctness, including strategy agreement at every
legal decision, when the interface does not deliver pending observations. -/
theorem compile_ledger_correct (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : SourceEquilibrium parameter utility intended)
    (unobserved : ∀ who pending, leaks who pending = PMF.pure ∅) :
    let compiled := compile spec intended equilibrium
    compiled.assessment.IsSequentialEquilibriumFor
      ((raw).decisionInformationAntichain Initial horizon scheduler)
      (fun who site => compiled.assessment.truncatedContinuationContext site
        (fun final => payoff spec who final.state) (2 * horizon + 1)) ∧
    (∀ who, ReactiveApplication.Policy.UsesLedgerOnly (app) (compiled.ledgerClients who)) ∧
    (∀ (history : ((raw).protocol Initial horizon scheduler).History) who,
      (raw).restrictPolicy Initial horizon scheduler who (compiled.ledgerClients who)
        ((model).infoOf who history.trace) =
      compiled.assessment.strategy who ((model).infoOf who history.trace)) ∧
    ((app).finish Initial horizon scheduler compiled.ledgerClients none).bind (observation spec) =
      (setup.intendedModel.runBehavioral intended.strategy
        (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  intro compiled
  exact ⟨compiled.equilibrium, compiled.ledgerClients_useLedgerOnly,
    compiled.ledgerClients_strategy_at_history unobserved,
    compiled.ledgerClients_outcomeLaw unobserved⟩

end Vegas.RecoveryCompiler
