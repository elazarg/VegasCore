/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.AsyncDeviationChoice
import Vegas.Game.ServiceBlockRun

/-! # Actual seeded service phases and their completion boundaries -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy)

/-- The points a first phase ending at `high` reaches, paired with their seeds. -/
abbrev phaseJoint {Seed : Type} (high : Nat) (prior : PMF Seed)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution) :
    PMF (Seed × (serviceApplication setup mode deadline leaks).Execution) :=
  prior.bind fun seed =>
    ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler players
      (BlockDone high) horizon (execution seed)).map fun final => (seed, final)

/-- A point a first phase ending at `high` reaches. -/
abbrev PhasePoint {Seed : Type} (high : Nat) (prior : PMF Seed)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution) : Type :=
  {point // point ∈ (phaseJoint setup leaks horizon scheduler players high prior
    execution).support}

/-- A point a first phase reaches comes from a seed of the prior and a run of
the phase. -/
theorem phaseJoint_mem {Seed : Type} {high : Nat} {prior : PMF Seed}
    {execution : Seed → (serviceApplication setup mode deadline leaks).Execution}
    {point : Seed × (serviceApplication setup mode deadline leaks).Execution}
    (member : point ∈ (phaseJoint setup leaks horizon scheduler players high prior
      execution).support) :
    point.1 ∈ prior.support ∧
      point.2 ∈ ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler players
        (BlockDone high) horizon (execution point.1)).support := by
  rcases point with ⟨seed, final⟩
  unfold phaseJoint at member
  rw [PMF.support_bind] at member
  obtain ⟨selected, chosen, moved⟩ := Set.mem_iUnion₂.mp member
  rw [PMF.support_map] at moved
  obtain ⟨reached, moved, same⟩ := moved
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨chosen, moved⟩

/-- An event ready alone has the same actual stopping law as its prefix end,
and every supported seeded endpoint is the next completion boundary. -/
theorem event_phase_stop_boundary
    (complete : CompletesPlay (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler)
    (event : (serviceGraph setup mode).EventId) {low : Nat} (atRank : event.val = low)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other,
      cut.Ready event → cut.Ready other → other = event)
    {Seed : Type} (prior : PMF Seed)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution)
    (boundary : ∀ seed ∈ prior.support,
      CompletionBoundary setup leaks scheduler players low (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon) :
    (∀ seed ∈ prior.support,
      (serviceApplication setup mode deadline leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed) =
        (serviceApplication setup mode deadline leaks).runUntilHorizon scheduler players
          (BlockDone (low + 1)) horizon (execution seed)) ∧
    ∀ point : PhasePoint setup leaks horizon scheduler players (low + 1) prior execution,
      CompletionBoundary setup leaks scheduler players (low + 1) point.val.2 ∧
        point.val.2.environmentRecall.length ≤ horizon := by
  have boundaryAt seed (supported : seed ∈ prior.support) :
      CompletionBoundary setup leaks scheduler players event.val (execution seed) := by
    rw [atRank]
    exact boundary seed supported
  have stopEq seed (supported : seed ∈ prior.support) :=
    runUntilHorizon_eventDone_eq_blockDone horizon event alone (execution seed)
      (boundaryAt seed supported)
  simp only [atRank] at stopEq
  refine ⟨stopEq, ?_⟩
  intro point
  obtain ⟨supported, reached⟩ := phaseJoint_mem setup leaks horizon scheduler players point.property
  rw [← stopEq _ supported] at reached
  obtain ⟨_, _, _, nextBounded, nextBoundary⟩ := completionRun_boundary_step complete event alone
    (execution point.val.1) (boundaryAt _ supported) (bounded _ supported) point.val.2 reached
  rw [atRank] at nextBoundary
  exact ⟨nextBoundary, nextBounded⟩

/-- A sealed completed block advances every supported seeded endpoint to its
actual end boundary without exceeding the original horizon. -/
theorem block_phase_boundary
    (complete : CompletesPlay (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler)
    {low high : Nat} (later : low ≤ high) (sealed : BlockSealed setup mode low high)
    (within : high ≤ (serviceGraph setup mode).order.eventCount)
    {Seed : Type} (prior : PMF Seed)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution)
    (boundary : ∀ seed ∈ prior.support,
      CompletionBoundary setup leaks scheduler players low (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (point : PhasePoint setup leaks horizon scheduler players high prior execution) :
    CompletionBoundary setup leaks scheduler players high point.val.2 ∧
      point.val.2.environmentRecall.length ≤ horizon := by
  obtain ⟨supported, reached⟩ := phaseJoint_mem setup leaks horizon scheduler players point.property
  have done := blockRun_completes complete high (execution point.val.1)
    (boundary _ supported) (bounded _ supported) _ reached
  obtain ⟨nextBounded, nextBoundary⟩ := blockRun_boundary later sealed within
    (execution point.val.1) (boundary _ supported) (bounded _ supported) _ reached done
  exact ⟨nextBoundary, nextBounded⟩

end Vegas
