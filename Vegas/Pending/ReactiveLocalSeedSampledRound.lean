/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedDecisionLaw

/-! # Actual decisions at independently sampled round counts

The count remains in the sampled outcome. The initial game inputs and immutable
scheduler seeds retain their original joint law conditional on that count.
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

/-- Sample a round count independently, then retain the actual decision at that count. -/
def sampledRoundDecisionLaw (laws : (side : Bool) → PMF (A side))
    (inputs : PMF graph.Inputs) (players : Player → (app).Policy) (counts : PMF Nat) :
    PMF (Nat × graph.Inputs × (app).Command × (app).Execution) :=
  counts.bind fun count =>
    (controller.decisionLaw remainder laws inputs players count).map (Prod.mk count)

/-- Retain the original immutable scheduler seeds together with the sampled count. -/
def seededSampledRoundDecisionLaw (laws : (side : Bool) → PMF (A side))
    (inputs : PMF graph.Inputs) (players : Player → (app).Policy) (counts : PMF Nat) :
    PMF ((Nat × graph.Inputs × (app).Command × (app).Execution) × ((side : Bool) → A side)) :=
  counts.bind fun count =>
    (controller.seededDecisionLaw remainder laws inputs players count).map fun outcome =>
      ((count, outcome.1), outcome.2)

/-- Actual sampled-round realization retains the joint initial-input and seed law. -/
theorem seededSampledRoundDecisionLaw_eq (laws : (side : Bool) → PMF (A side))
    (inputs : PMF graph.Inputs) (players : Player → (app).Policy) (counts : PMF Nat) :
    controller.seededSampledRoundDecisionLaw remainder laws inputs players counts =
      (controller.sampledRoundDecisionLaw remainder laws inputs players counts).bind fun point =>
        (((app).schedulerMixture (independentProduct laws) (fun values =>
          controller.fixedScheduler remainder
            (initialMemory (values false) (values true)))).posterior
              point.2.2.2.environmentRecall).map (Prod.mk point) := by
  unfold seededSampledRoundDecisionLaw sampledRoundDecisionLaw
  simp only [PMF.bind_map, PMF.bind_bind]
  apply bind_congr_on_support _
  intro count _
  rw [controller.seededDecisionLaw_eq]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- A supported sampled decision has its recorded count and an actual
supported decision at exactly that count. -/
theorem sampledRoundDecisionLaw_support (laws : (side : Bool) → PMF (A side))
    (inputs : PMF graph.Inputs) (players : Player → (app).Policy) (counts : PMF Nat)
    (point : Nat × graph.Inputs × (app).Command × (app).Execution)
    (reached : point ∈
      (controller.sampledRoundDecisionLaw remainder laws inputs players counts).support) :
    point.1 ∈ counts.support ∧
      point.2 ∈ (controller.decisionLaw remainder laws inputs players point.1).support := by
  obtain ⟨count, supported, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨actual, actualSupport, same⟩ := (PMF.mem_support_map_iff _ _ _).mp later
  cases same
  exact ⟨supported, actualSupport⟩

end Vegas.EventGraphRuntime.LocalSeedController
