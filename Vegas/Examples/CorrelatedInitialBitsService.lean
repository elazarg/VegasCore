module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.CorrelatedInitialBitsLedger
public import Vegas.Examples.CorrelatedInitialBitsInformation
public import Vegas.Game.ConditionedClientCompiler
public import Vegas.Game.ConditionedClientSpecification
public import Vegas.Pending.PeriodicServiceCompletion
public import Vegas.Pending.ThinnedCountCollection

@[expose] public section

/-! # Periodic ledger execution with a common private bit and imperfect audit -/

noncomputable section

namespace Vegas.Examples.CorrelatedInitialBits.Service

open SourceProgram Interaction EventGraphRuntime GameTheory.Enforcement

abbrev graph := setup.informationGraph
def leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph) :=
  MessageNetwork.ObservationRule.allPending
abbrev timeouts := PeriodicService.timeouts graph
abbrev app := application setup timeouts leaks
abbrev horizon := PeriodicService.horizon
def scheduler : app.Scheduler := PeriodicService.scheduler graph (Equiv.refl Bool) leaks

instance : leaks.FiniteSupport := inferInstanceAs
  MessageNetwork.ObservationRule.allPending.FiniteSupport

instance : app.FiniteNature (Vegas.initialDistribution setup) scheduler where
  toFiniteEnvironment := inferInstance
  initial_finite := serviceInitialDistribution_support_finite setup setup.informationDependencies
  scheduler_finite _ _ := by
    rw [scheduler, PeriodicService.scheduler, PMF.support_pure]
    exact Set.finite_singleton _

theorem contract :
    AsyncContract timeouts leaks (Vegas.initialDistribution setup) horizon scheduler (fun _ => 3)
      (fun _ => 2) := by
  have service := PeriodicService.contract (graph := graph) (roster := Equiv.refl Bool)
    (leaks := leaks) (inputLaw := setup.initialDistribution.map setup.eventInputs)
    (by decide) (by intro event; fin_cases event <;> rfl)
  simpa only [scheduler, PeriodicService.initial, Vegas.initialDistribution,
    serviceInitialDistribution,
    PMF.map_comp, Function.comp_def] using service

def bounds : MessageBounds graph where
  candidateCount := 2
  values := Finset.univ.image fun bit : Bool => (⟨.bool, bit⟩ : Raw simpleExpr)

def utility (result : Unit × PublicOutcome program) (who : Player) : ℝ :=
  OddsEvens.cash (result.2.values.get (.there .here)) (result.2.values.get .here) who

theorem utility_bounds (result : Unit × PublicOutcome program) (who : Player) :
    0 ≤ utility result who ∧ utility result who ≤ 200 := by
  unfold utility OddsEvens.cash
  split <;> (try split_ifs) <;> norm_num

def halfRate : Set.Icc (0 : ℝ) 1 := ⟨1/2, by norm_num⟩
abbrev component (bit : Bool) := setup.conditionInitial signal bit

/-- The same periodic scheduler, full pending observations, deposits and audit in both
components, with each component's private initializer and source histories. -/
def specification (bit : Bool) : ClientSpec (component bit) timeouts leaks bounds horizon
    scheduler (fun _ => ()) utility (fun _ => 0) :=
  Setup.conditionInitial_clientSpec (setup := setup) signal (fun _ => ()) utility (fun _ => 0)
    bit (signal_supported bit)
    (.independent (fun _ => ()) (conditioned_independent bit) (conditioned_observable bit))
    (inferInstance : app.FiniteNature (Vegas.initialDistribution setup) scheduler)
    wellFormed contract (PeriodicService.timely (graph := graph))
    (fun _ => 0) (fun _ => 200)
    (fun _ terminal _ who => utility_bounds (setup.parameterOutcome (fun _ => ()) terminal) who)
    (fun _ terminal _ who => (utility_bounds (setup.parameterOutcome (fun _ => ()) terminal)
      who).1)
    (by intro event; fin_cases event <;> intro value <;>
        exact Finset.mem_image.mpr ⟨value, Finset.mem_univ _, rfl⟩)
    (by intro input who payload binding; fin_cases input <;> cases binding)
    (by intro who; cases who <;> decide)
    (EvidenceReportService.thinned halfRate halfRate)
    (fun _ => halfRate.val) (fun _ => halfRate.val) (fun _ => 800)
    (fun _ => by norm_num [halfRate]) (thinnedCountEvidence_coverage halfRate halfRate)
    (fun _ => by norm_num) (fun _ => by norm_num [halfRate])

abbrev compiled (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium (fun _ => ()) utility intended) :=
  Setup.compileComponent (setup := setup) (bounds := bounds) (timeouts := timeouts)
    (leaks := leaks) (scheduler := scheduler) (horizon := horizon) (parameter := fun _ => ())
    (utility := utility) (exit := fun _ => 0) signal signal_supported informationFiber_component
    specification
    intended equilibrium

/-- A periodically scheduled ledger realizes every intended sequential equilibrium's
configuration and payoff law in the correlated-bit game through locally selected clients. -/
theorem clients_outcomeDistribution (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium (fun _ => ()) utility intended) :
    (app.finish (Vegas.initialDistribution setup) horizon scheduler
        (Setup.signalClients (setup := setup) (timeouts := timeouts) (leaks := leaks) ledgerBit
          (fun key => (compiled intended equilibrium key).clients))
        none).bind (specification false).observation =
      (setup.intendedModel.runBehavioral intended.strategy (instructionCount program + 1)).map
        (intendedReadoutExclusion setup (fun _ => ()) utility (fun _ => 0)) :=
  Setup.compileComponent_outcomeDistribution (setup := setup) (bounds := bounds)
    (timeouts := timeouts)
    (leaks := leaks) (scheduler := scheduler) (horizon := horizon) (parameter := fun _ => ())
    (utility := utility) (exit := fun _ => 0) signal signal_supported informationFiber_component
    specification intended equilibrium ledgerBit ledgerBit_observe wellFormed
    (specification false).observation (fun key => Setup.conditionInitial_observation_eq
      (setup := setup) (signal := signal) (specification key) (specification false) rfl rfl)

end Vegas.Examples.CorrelatedInitialBits.Service
