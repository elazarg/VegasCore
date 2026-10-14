/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedReplay
import Interaction.ReactiveSchedulerBeforeResponse

/-! # Actual local-seed decision laws with independent initial game draws

A decision retains the drawn game inputs, the selected command and the real
environment-step execution before response. The immutable seed law is sampled
independently of the initial game inputs.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {A : Bool → Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks (A false) owner event)
  (remainder : SeedRemainderController runtime leaks (A true) owner event)

local notation "app" => runtime.reactiveApplication leaks

/-- Actual behavioral command/environment decision law, before any response. -/
def decisionLaw (laws : (side : Bool) → PMF (A side)) (inputs : PMF graph.Inputs)
    (players : Player → (app).Policy) (count : Nat) :
    PMF (graph.Inputs × (app).Command × (app).Execution) :=
  let scheduler := ((app).schedulerMixture (independentProduct laws) (fun values =>
    controller.fixedScheduler remainder (initialMemory (values false) (values true)))).scheduler
  inputs.bind fun setup =>
    ((app).runRounds scheduler players count
      (ReactiveApplication.Execution.initial app (State.initial setup))).bind fun before =>
        (scheduler before.environmentRecall (before.observeEnvironment app)).bind fun command =>
          (before.environmentStep app command).map fun active => (setup, command, active)

/-- The same actual decision with its independently sampled immutable scheduler seeds. -/
def seededDecisionLaw (laws : (side : Bool) → PMF (A side)) (inputs : PMF graph.Inputs)
    (players : Player → (app).Policy) (count : Nat) :
    PMF ((graph.Inputs × (app).Command × (app).Execution) × ((side : Bool) → A side)) :=
  (independentProduct laws).bind fun values =>
    let scheduler := controller.fixedScheduler remainder
      (initialMemory (values false) (values true))
    inputs.bind fun setup =>
      ((app).runRounds scheduler players count
        (ReactiveApplication.Execution.initial app (State.initial setup))).bind fun before =>
          (scheduler before.environmentRecall (before.observeEnvironment app)).bind fun command =>
            (before.environmentStep app command).map fun active =>
              ((setup, command, active), values)

/-- Behavioral realization gives the full actual latent seed law at each decision,
including correlation with all hidden game inputs and residual runtime state. -/
theorem seededDecisionLaw_eq (laws : (side : Bool) → PMF (A side)) (inputs : PMF graph.Inputs)
    (players : Player → (app).Policy) (count : Nat) :
    controller.seededDecisionLaw remainder laws inputs players count =
      (controller.decisionLaw remainder laws inputs players count).bind fun point =>
        (((app).schedulerMixture (independentProduct laws) (fun values =>
          controller.fixedScheduler remainder
            (initialMemory (values false) (values true)))).posterior
              point.2.2.environmentRecall).map
              (Prod.mk point) := by
  let family := fun values : (side : Bool) → A side =>
    controller.fixedScheduler remainder (initialMemory (values false) (values true))
  unfold seededDecisionLaw decisionLaw
  rw [PMF.bind_comm]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  apply bind_congr_on_support _
  intro setup _
  have realized := congrArg (fun law :
      PMF ((app).Command × (app).Execution × ((side : Bool) → A side)) =>
    law.map (fun outcome =>
      ((setup, outcome.1, outcome.2.1), outcome.2.2)))
    ((app).schedulerMixture_beforeResponse_joint (independentProduct laws) family players count
      (State.initial setup))
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_map] using realized

/-- Every supported behavioral decision is a genuine initialized execution,
selected scheduler command and actual environment step for its drawn inputs. -/
theorem decisionLaw_support (laws : (side : Bool) → PMF (A side)) (inputs : PMF graph.Inputs)
    (players : Player → (app).Policy) (count : Nat)
    (point : graph.Inputs × (app).Command × (app).Execution)
    (reached : point ∈ (controller.decisionLaw remainder laws inputs players count).support) :
    point.1 ∈ inputs.support ∧ ∃ before,
      before ∈ ((app).runRounds
        (((app).schedulerMixture (independentProduct laws) (fun values =>
          controller.fixedScheduler remainder
            (initialMemory (values false) (values true)))).scheduler)
              players count
                (ReactiveApplication.Execution.initial app (State.initial point.1))).support ∧
      point.2.1 ∈ (((app).schedulerMixture (independentProduct laws) (fun values =>
        controller.fixedScheduler remainder (initialMemory (values false) (values true)))).scheduler
          before.environmentRecall (before.observeEnvironment app)).support ∧
      point.2.2 ∈ (before.environmentStep app point.2.1).support := by
  obtain ⟨setup, supported, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨before, prefixSupport, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ later)
  obtain ⟨command, commandSupport, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ later)
  obtain ⟨active, activeSupport, same⟩ := (PMF.mem_support_map_iff _ _ _).mp later
  cases same
  exact ⟨supported, before, prefixSupport, commandSupport, activeSupport⟩

end Vegas.EventGraphRuntime.LocalSeedController
