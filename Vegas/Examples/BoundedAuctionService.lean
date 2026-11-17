module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.BoundedPrivateAuctionConditions
public import Vegas.Examples.BoundedPrivateValueAuctionSequential
public import Vegas.Pending.PeriodicServiceCompletion
public import Vegas.Pending.CountReportSelection
public import Interaction.MessageNetworkObservation
public import Vegas.Game.ClientCompiler
public import Vegas.Game.PaymentPreservation

@[expose] public section

/-! # A funded native runtime for the private-value auction -/

noncomputable section

namespace Vegas.Examples.BoundedAuctionService

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability GameTheory.Enforcement
open BoundedPrivateValueAuction
open CommitRevealAuction (Player)

abbrev game := setup uniformPrior

def leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph) :=
  MessageNetwork.ObservationRule.allPending

def timeouts : EventTimeouts graph := PeriodicService.timeouts graph

abbrev app := (reactiveApplication timeouts) leaks

def initialLaw : PMF app.State := Vegas.initialLaw game

abbrev horizon := PeriodicService.horizon

def scheduler : app.Scheduler := PeriodicService.scheduler graph roster leaks

instance : leaks.FiniteSupport := inferInstanceAs
  MessageNetwork.ObservationRule.allPending.FiniteSupport

instance : app.FiniteNature initialLaw scheduler where
  toFiniteEnvironment := inferInstance
  initial_finite := serviceInitialLaw_support_finite game game.informationDependencies
  scheduler_finite _ _ := by
    rw [scheduler, PeriodicService.scheduler, PMF.support_pure]
    exact Set.finite_singleton _

/-- The actual builder meets its contract on all raw histories. -/
theorem contract :
    AsyncContract timeouts leaks initialLaw horizon scheduler (fun _ => 3) (fun _ => 2) := by
  have supplied := PeriodicService.contract (graph := graph) (roster := roster) (leaks := leaks)
    (inputLaw := game.initialLaw.map game.eventInputs)
    (by decide) (by intro event; fin_cases event <;> rfl)
  simpa only [timeouts, initialLaw, PeriodicService.initial, scheduler, Vegas.initialLaw,
    serviceInitialLaw, PMF.map_comp, Function.comp_def] using supplied

def halfRate : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩

abbrev evidenceService :=
  thinnedFirstCountReports (graph := graph) halfRate halfRate

/-- Each offending bidder's first forbidden witness is collected with probability one quarter. -/
theorem collection_probability (actual : List (CountEvidence graph))
    (evidence : CountEvidence graph) (member : evidence ∈ firstCountReports actual) :
    ((evidenceService.sample actual).toOuterMeasure
      {collected | evidence ∈ collected}).toReal = 1 / 4 := by
  rw [evidenceService, thinnedFirstCountReports_sample]
  have mass := EvidenceReportService.thinned_collection_mass halfRate halfRate
    (firstCountReports actual) evidence member
  norm_num [halfRate] at mass
  exact mass

/-- The bounded auction's utility bounds, message catalogue and funded audit
serve every joint valuation prior and every builder meeting the stated timing conditions. -/
def fundedSpecification (prior : PMF (Player → Bid)) (rt : EventTimeouts graph)
    (steps : Nat) (builder : ((reactiveApplication rt) leaks).Scheduler)
    (finiteNature : ((reactiveApplication rt) leaks).FiniteNature (Vegas.initialLaw (setup prior))
      builder) (delay bound : graph.EventId → Nat)
    (service : AsyncContract rt leaks (Vegas.initialLaw (setup prior)) steps builder delay bound)
    (timely : AsyncTimely rt delay bound)
    (priors : SequentialPriorCondition (setup prior) rt leaks bounds steps builder) :
    ClientSpec (setup prior) rt leaks bounds steps builder values utility (fun _ => -6) where
  finiteNature := finiteNature
  finiteSource := inferInstance
  wellFormed := wellFormed prior
  prior := priors
  delay := delay
  bound := bound
  opportunity := service.opportunity
  inclusion := service.inclusion
  completes := service.completes
  timely := timely
  lowerUtility := fun _ => -6
  upperUtility := fun _ => 6
  lower_le := fun _ terminal _ who => (utility_bounds _ who).1
  le_upper := fun _ terminal _ who => (utility_bounds _ who).2
  exitBelow := fun _ terminal _ who => (utility_bounds _ who).1
  outputValues := outputValues
  inputValues := inputValues
  capacity := candidateCapacity
  evidenceService := evidenceService
  observationRate := fun _ => halfRate.val
  deliveryRate := fun _ => halfRate.val
  delivery_nonnegative := fun _ => by norm_num [halfRate]
  coverage := thinnedFirstCountReports_coverage halfRate halfRate
  deposit := fun _ => 48
  deposit_nonnegative := fun _ => by norm_num
  funded := fun _ => by norm_num [halfRate]

/-- Independent uniform bids on the periodic full-pending service. -/
def specification : ClientSpec game timeouts leaks bounds horizon scheduler
    values utility (fun _ => -6) :=
  fundedSpecification uniformPrior timeouts horizon scheduler
    (inferInstanceAs (app.FiniteNature initialLaw scheduler)) _ _ contract
    (PeriodicService.timely (graph := graph)) (.independent signal independent observable)

/-- One selected raw assessment retains the truthful source assessment and its physical clients. -/
def compilation : ClientCompilation specification (truthfulAssessment uniformPrior) :=
  specification.compile (truthfulAssessment uniformPrior)
    (truthfulAssessment_equilibrium uniformPrior)

abbrev raw := bounds.rawMenu timeouts leaks

abbrev model := raw.information initialLaw horizon scheduler

def jointLaw : PMF (Option (Config Player simpleExpr program.terminalCtx) × (Player → ℝ)) :=
  uniformPrior.map (fun types =>
    (some (finalConfig types (types .alice) (types .bob)),
      surplus types (types .alice) (types .bob)))

def rawJointLaw : PMF (Option (Config Player simpleExpr program.terminalCtx) × (Player → ℝ)) :=
  (raw.run initialLaw horizon scheduler compilation.assessment.strategy).bind
    (fun final => specification.observation final.state)

private theorem intended_jointLaw (prior : PMF (Player → Bid)) :
    (((setup prior).intendedModel.runBehavioral (truthfulAssessment prior).strategy
      (instructionCount program + 1)).map
      (intendedReadoutExclusion (setup prior) values utility (fun _ => -6))) =
        prior.map (fun types => (some (finalConfig types (types .alice) (types .bob)),
          surplus types (types .alice) (types .bob))) := by
  have law := truthfulAssessment_joint_law prior
  refine Eq.trans ?_ law
  apply map_congr_on_support _
  intro final _supported
  refine Prod.ext rfl (funext fun who => ?_)
  exact (setup prior).intended_exclusionReadoutUtility (wellFormed prior) values utility
    (fun _ => -6) final who

/-- For every joint valuation prior, including priors with missing type pairs,
a timely single-opportunity service realizes the truthful auction's exact joint law. -/
theorem truthful_single_opportunity (prior : PMF (Player → Bid)) (rt : EventTimeouts graph)
    (steps : Nat) (builder : ((reactiveApplication rt) leaks).Scheduler)
    (finiteNature : ((reactiveApplication rt) leaks).FiniteNature (Vegas.initialLaw (setup prior))
      builder) (delay bound : graph.EventId → Nat)
    (service : AsyncContract rt leaks (Vegas.initialLaw (setup prior)) steps builder delay bound)
    (timely : AsyncTimely rt delay bound)
    (once : SingleSubmissionOpportunity (setup prior) rt leaks bounds steps builder) :
    let spec := fundedSpecification prior rt steps builder finiteNature delay bound service timely
      (.singleOpportunity (by decide) once)
    ∃ compiled : ClientCompilation spec (truthfulAssessment prior),
      (((bounds.rawMenu rt leaks).run (Vegas.initialLaw (setup prior)) steps builder
        compiled.assessment.strategy).bind (fun final => spec.observation final.state)) =
          prior.map (fun types => (some (finalConfig types (types .alice) (types .bob)),
            surplus types (types .alice) (types .bob))) := by
  dsimp only
  let spec := fundedSpecification prior rt steps builder finiteNature delay bound service timely
    (.singleOpportunity (by decide) once)
  let compiled := spec.compile (truthfulAssessment prior) (truthfulAssessment_equilibrium prior)
  exact ⟨compiled, compiled.outcomeLaw.trans (intended_jointLaw prior)⟩

private theorem raw_jointLaw : rawJointLaw = jointLaw :=
  compilation.outcomeLaw.trans (intended_jointLaw uniformPrior)

private theorem physical_jointLaw :
    ((app.finish initialLaw horizon scheduler compilation.clients none).bind
      specification.observation) = jointLaw :=
  compilation.clients_outcomeLaw.trans (intended_jointLaw uniformPrior)

private theorem raw_readout_law :
    (raw.run initialLaw horizon scheduler compilation.assessment.strategy).map
      (fun final => sourceReadout game timeouts leaks final.state) =
    (game.intendedModel.runBehavioral (truthfulAssessment uniformPrior).strategy
      (instructionCount program + 1)).map (fun final => game.protocolReadout final.state) := by
  have projected := congrArg (PMF.map Prod.fst) compilation.outcomeLaw
  have constant (final : (raw.protocol initialLaw horizon scheduler).History) :
      (specification.settlement final.state).map
        (fun _ => sourceReadout game timeouts leaks final.state) =
      PMF.pure (sourceReadout game timeouts leaks final.state) := PMF.map_const _ _
  simp only [ClientSpec.observation, PMF.map_bind, PMF.map_comp, Function.comp_def,
    intendedReadoutExclusion] at projected
  simp_rw [constant] at projected
  exact projected

private theorem raw_clean
    (final : (raw.protocol initialLaw horizon scheduler).History)
    (supported : final ∈ (raw.run initialLaw horizon scheduler
      compilation.assessment.strategy).support) :
    ∃ (control : app.Control) (terminal : Config Player simpleExpr program.terminalCtx),
      final.state = some control ∧ control.execution.application.config.cut.Terminal ∧
      sourceReadout game timeouts leaks final.state = some terminal ∧
      control.execution.application.config.defaulted = ∅ ∧
      (∀ who, failedReveals program who (publicOutcome program terminal) = 0) ∧
      ∀ who, TerminalAudit.charge app.stateTraffic
        ((countAudit timeouts) leaks evidenceService.sample) final.state who = 0 := by
  have observed : sourceReadout game timeouts leaks final.state ∈
      ((game.intendedModel.runBehavioral (truthfulAssessment uniformPrior).strategy
        (instructionCount program + 1)).map
        (fun history => game.protocolReadout history.state)).support := by
    rw [← raw_readout_law]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩
  have explicit := observed
  rw [truthfulAssessment_readout_law] at explicit
  obtain ⟨types, _present, same⟩ := (PMF.mem_support_map_iff _ _ _).mp explicit
  have read := same.symm
  obtain ⟨source, _reached, sourceRead⟩ := (PMF.mem_support_map_iff _ _ _).mp observed
  have sourceRead := sourceRead.trans read
  cases current : final.state with
  | none =>
      rw [current] at read
      cases read
  | some control =>
      have readAt : sourceReadout game timeouts leaks (some control) =
          some (finalConfig types (types .alice) (types .bob)) := by
        rw [← current]
        exact read
      have terminal : control.execution.application.config.cut.Terminal := by
        by_contra unfinished
        simp only [sourceReadout, serviceSourceReadout, Option.bind_some,
          unfinished, ite_false] at readAt
        cases readAt
      refine ⟨control, _, rfl, terminal, readAt,
        compilation.noDefaults final supported control current,
        game.intended_no_failed_reveals (wellFormed uniformPrior) source sourceRead, ?_⟩
      have evidenceSame : specification.evidenceService = evidenceService := rfl
      simpa only [current, evidenceSame] using compilation.noCharges final supported

private theorem physical_clean (state : app.ProtocolState)
    (supported : state ∈
      (app.finish initialLaw horizon scheduler compilation.clients none).support) :
    ∃ (control : app.Control) (terminal : Config Player simpleExpr program.terminalCtx),
      state = some control ∧ control.execution.application.config.cut.Terminal ∧
      sourceReadout game timeouts leaks state = some terminal ∧
      control.execution.application.config.defaulted = ∅ ∧
      (∀ who, failedReveals program who (publicOutcome program terminal) = 0) ∧
      ∀ who, TerminalAudit.charge app.stateTraffic
        ((countAudit timeouts) leaks evidenceService.sample) state who = 0 := by
  have same : (raw.run initialLaw horizon scheduler compilation.assessment.strategy).map
      (fun final => final.state) =
      app.finish initialLaw horizon scheduler compilation.clients none :=
    compilation.clients_stateLaw
  have transported : state ∈ ((raw.run initialLaw horizon scheduler
      compilation.assessment.strategy).map (fun final => final.state)).support :=
    same.symm ▸ supported
  obtain ⟨final, present, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp transported
  exact raw_clean final present

private theorem jointLaw_expected (who : Player) :
    expect jointLaw (fun realized => realized.2 who) = 8 / 7 := by
  simpa only [jointLaw, expect_map, Function.comp_def] using truthful_joint_law_expected who

/-- The selected raw equilibrium retains the intended assessment and its complete
truthful law under full pending observation; supported play is clean and funded. -/
theorem native_equilibrium :
    Nonempty (ClientAssessmentRefinement game timeouts leaks bounds horizon scheduler
      (truthfulAssessment uniformPrior) compilation.assessment) ∧
    compilation.assessment.IsSequentialEquilibrium
      (raw.decisionInformationAntichain initialLaw horizon scheduler)
      (raw.bounded initialLaw horizon scheduler).wellFoundedHistories
      (fun who final => specification.payoff who final.state) ∧
    (∀ who, raw.restrictPolicy initialLaw horizon scheduler who (compilation.clients who) =
      compilation.assessment.strategy who) ∧
    (∀ final ∈ (raw.run initialLaw horizon scheduler compilation.assessment.strategy).support,
      ∃ (control : app.Control) (terminal : Config Player simpleExpr program.terminalCtx),
        final.state = some control ∧ control.execution.application.config.cut.Terminal ∧
        sourceReadout game timeouts leaks final.state = some terminal ∧
        control.execution.application.config.defaulted = ∅ ∧
        (∀ who, failedReveals program who (publicOutcome program terminal) = 0) ∧
        ∀ who, TerminalAudit.charge app.stateTraffic
          ((countAudit timeouts) leaks evidenceService.sample) final.state who = 0) ∧
    (∀ state ∈ (app.finish initialLaw horizon scheduler compilation.clients none).support,
      ∃ (control : app.Control) (terminal : Config Player simpleExpr program.terminalCtx),
        state = some control ∧ control.execution.application.config.cut.Terminal ∧
        sourceReadout game timeouts leaks state = some terminal ∧
        control.execution.application.config.defaulted = ∅ ∧
        (∀ who, failedReveals program who (publicOutcome program terminal) = 0) ∧
        ∀ who, TerminalAudit.charge app.stateTraffic
          ((countAudit timeouts) leaks evidenceService.sample) state who = 0) ∧
    rawJointLaw = jointLaw ∧
    ((app.finish initialLaw horizon scheduler compilation.clients none).bind
      specification.observation) = jointLaw ∧
    ∀ who, expect rawJointLaw (fun realized => realized.2 who) = 8 / 7 ∧
      expect ((app.finish initialLaw horizon scheduler compilation.clients none).bind
        specification.observation) (fun realized => realized.2 who) = 8 / 7 := by
  refine ⟨⟨compilation.refinement⟩, compilation.equilibrium, compilation.clients_strategy,
    raw_clean, physical_clean, raw_jointLaw, physical_jointLaw, ?_⟩
  intro who
  constructor
  · rw [raw_jointLaw]
    exact jointLaw_expected who
  · rw [physical_jointLaw]
    exact jointLaw_expected who

/-- The same selected assessment and physical clients retain the executable cash law. -/
theorem program_payments_preserved :
    ((raw.run initialLaw horizon scheduler compilation.assessment.strategy).bind
      (fun final => specification.programPaymentObservation final.state)) =
        game.intendedPaymentLaw (truthfulAssessment uniformPrior) ∧
    ((app.finish initialLaw horizon scheduler compilation.clients none).bind
      specification.programPaymentObservation) =
        game.intendedPaymentLaw (truthfulAssessment uniformPrior) := by
  exact ⟨intended_raw_programPayments_preserved game timeouts leaks bounds horizon scheduler
      values utility (fun _ => -6) specification (truthfulAssessment uniformPrior) compilation,
    compilation.clients_programPayments_preserved game timeouts leaks bounds horizon scheduler
      values utility (fun _ => -6) specification (truthfulAssessment uniformPrior)⟩

end Vegas.Examples.BoundedAuctionService
