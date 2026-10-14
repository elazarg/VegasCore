/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedSampledRound
import Vegas.Pending.ReactiveCountedSeedObservation
import Interaction.ReactiveOccupationPosterior

/-! # Original immutable seed laws at actual bounded command controls -/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

local notation "app" => runtime.reactiveApplication leaks

/-- The genuine protocol control at the sampled command/environment boundary. -/
def decisionControl (horizon : Nat)
    (point : Nat × graph.Inputs × (app).Command × (app).Execution) : (app).ProtocolState :=
  some ⟨horizon - point.1 - 1, point.2.2.1.actor? app, point.2.2.2⟩

/-- Current owner information does not expose the remaining scheduler budget. -/
theorem observe_decisionControl (owner : Player) (horizon : Nat)
    (point : Nat × graph.Inputs × (app).Command × (app).Execution) :
    (app).observe owner (decisionControl (runtime := runtime) (leaks := leaks) horizon point) =
      decisionObservation (owner := owner) point.2 := rfl

variable {A : Bool → Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks (A false) owner event)
  (remainder : SeedRemainderController runtime leaks (A true) owner event)

/-- Sampling only command indices before the horizon gives exactly the actual
uniform occupation law, retaining the complete current control. -/
theorem sampledRoundDecisionLaw_control
    (laws : (side : Bool) → PMF (A side)) (inputs : PMF graph.Inputs)
    (players : Player → (app).Policy) (horizon : Nat) [NeZero horizon] :
    (controller.sampledRoundDecisionLaw remainder laws inputs players
      ((PMF.uniformOfFintype (Fin horizon)).map Fin.val)).map
        (decisionControl (runtime := runtime) (leaks := leaks) horizon) =
      (app).occupationControlLaw
        (((app).schedulerMixture (independentProduct laws) (fun values =>
          controller.fixedScheduler remainder
            (initialMemory (values false) (values true)))).scheduler)
        players (inputs.map State.initial) horizon := by
  simp only [sampledRoundDecisionLaw, decisionLaw, decisionControl,
    ReactiveApplication.occupationControlLaw, ReactiveApplication.commandControlLaw,
    PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- The exact original sampled seed law at bounded command controls is the
behavioral occupation law tagged with its actual full-transcript seed posterior. -/
theorem seededSampledRoundDecisionLaw_control
    (laws : (side : Bool) → PMF (A side)) (inputs : PMF graph.Inputs)
    (players : Player → (app).Policy) (horizon : Nat) [NeZero horizon] :
    (controller.seededSampledRoundDecisionLaw remainder laws inputs players
      ((PMF.uniformOfFintype (Fin horizon)).map Fin.val)).map
        (fun outcome =>
          (decisionControl (runtime := runtime) (leaks := leaks) horizon outcome.1, outcome.2)) =
      ((app).occupationControlLaw
        (((app).schedulerMixture (independentProduct laws) (fun values =>
          controller.fixedScheduler remainder
            (initialMemory (values false) (values true)))).scheduler)
        players (inputs.map State.initial) horizon).bind fun state =>
          (match state with
          | none => independentProduct laws
          | some current =>
              (((app).schedulerMixture (independentProduct laws) (fun values =>
                controller.fixedScheduler remainder
                  (initialMemory (values false) (values true)))).posterior
                    current.execution.environmentRecall)).map (Prod.mk state) := by
  rw [controller.seededSampledRoundDecisionLaw_eq,
    ← controller.sampledRoundDecisionLaw_control remainder laws inputs players horizon]
  simp only [PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def, decisionControl]

end Vegas.EventGraphRuntime.LocalSeedController
