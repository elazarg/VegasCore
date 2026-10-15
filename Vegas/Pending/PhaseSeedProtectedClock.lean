/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedServiceTick

/-! # A protected packet cannot survive an actual calendar tick -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Tick draining prevents a protected earlier packet from remaining unresolved
past its open emission tick. The proof uses actual query origins and retained
ready-time stamps, so arbitrary history-adaptive priorities and retries remain allowed. -/
theorem protected_request_time (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon remaining : Nat)
    (players : Player → (app).Policy) (count : Nat) (execution next : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks delay bound priority).family seeds)).Trace
        (some ⟨remaining, none, next⟩))
    {input : graph.Inputs} (valid : execution.application.Invariant input)
    (phases : execution.application.Ordered)
    (wordRecall : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (clean : PhaseCount.CountClean runtime leaks execution)
    (continued : next ∈ ((app).runRounds
      ((controller runtime leaks delay bound priority).family seeds) players count
        execution).support)
    (owner : Player) (coordinate : PhaseSeedAddress graph)
    (requested : execution.application.SeedRequest owner coordinate.1)
    (survives : next.application.SeedRequest owner coordinate.1)
    (entered : Nat)
    (activated : execution.application.current.native.activatedAt coordinate.1.event = some entered)
    (started : entered ≤ execution.application.current.native.clock)
    (unclosed : (execution.application.current.native.clock, coordinate) ∉
      replayClosed runtime leaks priority seeds.1 execution.environmentRecall)
    (message : Message Player (CommitAttemptPacket graph))
    (recorded : (execution.application.current.native.clock - entered, message) ∈
      (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner execution.environmentRecall
        (execution.observeEnvironment app)).emissions)
    (protection : execution.application.current.native.clock - entered +
      bound coordinate.1.event < runtime.deadline coordinate.1.event) :
    next.application.current.native.clock = execution.application.current.native.clock ∧
      next.application.current.native.activatedAt coordinate.1.event = some entered := by
  have sum : entered + (execution.application.current.native.clock - entered) =
      execution.application.current.native.clock := by omega
  obtain ⟨lower, upper, stamp⟩ := service_tick_bounds_request_time runtime leaks delay bound
    priority seeds bounds plan ordered maximal inputs horizon remaining players count execution
      next trace valid phases wordRecall clean continued owner coordinate requested survives entered
      activated started (execution.application.current.native.clock - entered) (by omega)
      (by omega) (by simpa only [sum] using unclosed)
      (execution.application.current.native.clock - entered) message recorded (Or.inl protection)
  rw [sum] at upper
  exact ⟨Nat.le_antisymm upper lower, stamp⟩

end Vegas.EventGraphRuntime.PhaseSeedCalendar
