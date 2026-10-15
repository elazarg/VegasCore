/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedUnsentDelay

/-! # All original seed candidates have the same unsent owner-fiber constraints -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The completed owner clock word at its current response input. The final
entry is the current activation, whose response has not yet been made. -/
def inputActivationClocks (coordinate : CommitAttemptEvent graph) (owner : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) : List Nat :=
  let input := PhaseSeedScheduler.informationInput runtime leaks coordinate owner past view
  input.activationClocks ++ [input.elapsed]

/-- The entire original seed filter at a genuine unsent callback is determined
by the minimum of the clocks visible in its own input, including this callback. -/
theorem unsent_information_delay_filter (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks delay bound priority).family seeds)).Trace
        (some ⟨remaining, some owner, execution⟩))
    (coordinate : PhaseSeedAddress graph)
    (request : execution.application.SeedRequest owner coordinate.1)
    (unsent : ∀ message ∈ (app).outputs (execution.recall owner),
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false) :
    ∃ firstClock,
      firstClock ∈ inputActivationClocks runtime leaks coordinate.1 owner
        (execution.recall owner) (execution.observe app owner) ∧
      (∀ clock ∈ inputActivationClocks runtime leaks coordinate.1 owner
        (execution.recall owner) (execution.observe app owner), firstClock ≤ clock) ∧
      ∀ candidate : Seed runtime delay,
        (controller runtime leaks delay bound priority).coordinateConsistentFrom seeds.1
          coordinate candidate [] execution.environmentRecall ↔ candidate.1.val = firstClock := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let scheduler := (controller runtime leaks delay bound priority).family seeds
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let idle := execution.respond app owner ⟨none⟩
  have raw := menu.toRawTrace initial horizon scheduler trace
  obtain ⟨input, valid, _, _⟩ :=
    currentTokenPrerequisites_history runtime leaks plan inputs horizon scheduler raw
  have visible : PhaseRuntimeState.requests (execution.observe app owner).application.2 owner
      coordinate.1 :=
    (PhaseRuntimeState.requests_publicView _ valid owner coordinate.1).mpr request
  have visibleBool : decide (PhaseRuntimeState.requests
      (execution.observe app owner).application.2 owner coordinate.1) = true :=
    decide_eq_true visible
  have clocks : (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (idle.recall owner)).map Prod.fst =
      inputActivationClocks runtime leaks coordinate.1 owner
        (execution.recall owner) (execution.observe app owner) := by
    simp only [idle, ReactiveApplication.Execution.respond,
      PhaseSeedScheduler.ownerWord, List.filter_append, List.filter_cons, List.filter_nil,
      List.map_append, List.map_cons, List.map_nil, visibleBool, ite_true,
      inputActivationClocks, PhaseSeedScheduler.informationInput]
  have observed : (queryAt runtime leaks idle coordinate owner).elapsed ∈
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner (idle.recall owner)).map
        Prod.fst := by
    rw [clocks]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have networkUnsent := network_unsent_of_information runtime leaks initial bounds horizon
    scheduler remaining owner execution trace coordinate unsent
  obtain ⟨idleTrace⟩ := menu.trace_respond initial horizon scheduler remaining execution owner
    ⟨none⟩ trace (PhaseCount.silence_onePacket runtime leaks bounds owner
      (execution.recall owner) (execution.observe app owner))
  obtain ⟨firstClock, member, least, candidates⟩ :=
    unsent_delay_filter_of_recorded_activation runtime leaks delay bound priority seeds bounds plan
      ordered maximal inputs horizon remaining idle idleTrace coordinate owner request networkUnsent
      observed
  refine ⟨firstClock, clocks ▸ member, ?_, ?_⟩
  · intro clock present
    exact least clock (clocks.symm ▸ present)
  · intro candidate
    simpa only [idle, (app).respond_environmentRecall] using candidates candidate

/-- Complete owner information determines the selected coordinate's command
constraints for EVERY original candidate seed, across all hidden controls and
all original remainder/foreign seed values. This is restricted to unsent sites. -/
theorem coordinateConsistent_iff_of_unsent_information_eq (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (firstSeeds secondSeeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon firstRemaining secondRemaining : Nat)
    (owner : Player) (first second : (app).Execution)
    (firstTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks delay bound priority).family firstSeeds)).Trace
        (some ⟨firstRemaining, some owner, first⟩))
    (secondTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks delay bound priority).family secondSeeds)).Trace
        (some ⟨secondRemaining, some owner, second⟩))
    (coordinate : PhaseSeedAddress graph)
    (firstRequest : first.application.SeedRequest owner coordinate.1)
    (secondRequest : second.application.SeedRequest owner coordinate.1)
    (same : (first.recall owner, first.observe app owner) =
      (second.recall owner, second.observe app owner))
    (unsent : ∀ message ∈ (app).outputs (first.recall owner),
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false)
    (candidate : Seed runtime delay) :
    (controller runtime leaks delay bound priority).coordinateConsistentFrom firstSeeds.1
      coordinate candidate [] first.environmentRecall ↔
    (controller runtime leaks delay bound priority).coordinateConsistentFrom secondSeeds.1
      coordinate candidate [] second.environmentRecall := by
  have samePast : first.recall owner = second.recall owner := congrArg Prod.fst same
  have secondUnsent : ∀ message ∈ (app).outputs (second.recall owner),
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false := by
    rw [← samePast]
    exact unsent
  obtain ⟨firstClock, firstMember, firstLeast, firstFilter⟩ := unsent_information_delay_filter
    runtime leaks delay bound priority firstSeeds bounds plan ordered maximal inputs horizon
    firstRemaining owner first firstTrace coordinate firstRequest unsent
  obtain ⟨secondClock, secondMember, secondLeast, secondFilter⟩ := unsent_information_delay_filter
    runtime leaks delay bound priority secondSeeds bounds plan ordered maximal inputs horizon
    secondRemaining owner second secondTrace coordinate secondRequest secondUnsent
  have clocksEq := congrArg (fun input : List (app).PlayerEntry × (app).PlayerView =>
    inputActivationClocks runtime leaks coordinate.1 owner input.1 input.2) same
  have clockEq : firstClock = secondClock := Nat.le_antisymm
    (firstLeast secondClock (clocksEq.symm ▸ secondMember))
    (secondLeast firstClock (clocksEq ▸ firstMember))
  rw [firstFilter candidate, secondFilter candidate, clockEq]

end Vegas.EventGraphRuntime.PhaseSeedCalendar
