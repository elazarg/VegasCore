module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensSetup
public import Vegas.Pending.PeriodicServiceCompletion

@[expose] public section

/-! # The periodic physical service for Odds–Evens

The source-ordered game uses the shared two-player service with six-tick
relative deadlines, no pending delivery and its original initial law.
-/

noncomputable section

namespace Vegas.Examples.OddsEvensService

open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

def leaks : MessageNetwork.ObservationRule OddsEvens.Player
    (WitnessedPacket OddsEvens.compiled) := fun _ _ => PMF.pure ∅

def timeouts : EventTimeouts OddsEvens.compiled :=
  PeriodicService.timeouts OddsEvens.compiled

abbrev app := (reactiveApplication timeouts) leaks

def initial : PMF app.State := Vegas.initialLaw OddsEvens.setup

abbrev horizon := PeriodicService.horizon

def scheduler : app.Scheduler :=
  PeriodicService.scheduler OddsEvens.compiled (Equiv.refl Bool) leaks

instance : leaks.FiniteSupport where
  support_finite _ _ := by simp [leaks]

instance : app.FiniteNature initial scheduler where
  toFiniteEnvironment := inferInstance
  initial_finite := serviceInitialLaw_support_finite OddsEvens.setup
    OddsEvens.setup.informationDependencies
  scheduler_finite _ _ := by
    rw [scheduler, PeriodicService.scheduler, PMF.support_pure]
    exact Set.finite_singleton _

/-- The concrete builder meets the actual raw-history service contract. -/
theorem contract :
    AsyncContract timeouts leaks initial horizon scheduler (fun _ => 3) (fun _ => 2) := by
  have service := PeriodicService.contract (graph := OddsEvens.compiled)
    (roster := Equiv.refl Bool) (leaks := leaks)
    (inputLaw := OddsEvens.setup.initialLaw.map OddsEvens.setup.eventInputs)
    (by decide) (by intro event; fin_cases event <;> rfl)
  simpa only [timeouts, initial, scheduler, PeriodicService.initial, Vegas.initialLaw,
    serviceInitialLaw, PMF.map_comp, Function.comp_def] using service

end Vegas.Examples.OddsEvensService
