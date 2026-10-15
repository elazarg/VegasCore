/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedUnsentFiber
import Vegas.Pending.PhaseOncePolicy
import Vegas.Pending.ReactiveAsyncContract

/-! # Original delay and protected timing at the first physical callback -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
/-- At a callback with no previous response, its current clock is the complete
local activation word. Silence at an earlier callback would be recorded. -/
theorem inputActivationClocks_of_unrecorded (coordinate : CommitAttemptEvent graph)
    (owner : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks owner coordinate past) :
    inputActivationClocks runtime leaks coordinate owner past view =
      [(PhaseSeedScheduler.informationInput runtime leaks coordinate owner past view).elapsed] := by
  classical
  have empty : past.filter (fun entry =>
      PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro entry member selected
    exact first ⟨entry, member, of_decide_eq_true selected⟩
  simp only [inputActivationClocks, PhaseSeedScheduler.informationInput,
    PhaseSeedScheduler.ownerWord, empty, List.map_nil, List.nil_append]

/-- The original first-delay draw is exactly the elapsed physical clock at
the first unsent callback, under arbitrary history-adaptive priority. -/
theorem first_delay_eq_elapsed_of_unrecorded (delay bound : graph.EventId → Nat)
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
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks owner coordinate.1
      (execution.recall owner)) :
    (seeds.2 coordinate).1.val = (PhaseSeedScheduler.informationInput runtime leaks coordinate.1
      owner (execution.recall owner) (execution.observe app owner)).elapsed := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let driver := controller runtime leaks delay bound priority
  let scheduler := driver.family seeds
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have raw := menu.toRawTrace initial horizon scheduler trace
  have commands := ((app).deterministic_transcript_invariant driver.choose seeds).history
    initial horizon (by intro state supported; trivial) raw
  have consistent := ((driver.command_rectangle seeds.1 seeds.2 []
    execution.environmentRecall).mp commands).2 coordinate
  obtain ⟨firstClock, member, _least, filter⟩ := unsent_information_delay_filter runtime leaks
    delay bound priority seeds bounds plan ordered maximal inputs horizon remaining owner
      execution trace coordinate request unsent
  rw [inputActivationClocks_of_unrecorded runtime leaks coordinate.1 owner _ _ first,
    List.mem_singleton] at member
  exact ((filter (seeds.2 coordinate)).mp consistent).trans member

omit [Fintype Player] [DecidableEq Player] in
/-- Every supported seed of the declared event law respects its reaction
bound. The larger finite seed carrier also contains unsupported delays. -/
theorem eventLaw_first_delay_le (delay : graph.EventId → Nat)
    (delayLaw : (event : graph.EventId) → PMF (Fin (delay event + 1)))
    (coinLaw : graph.EventId → Fin (clockLimit runtime delay + 1) → PMF Bool)
    (event : graph.EventId) (seed : Seed runtime delay)
    (supported : seed ∈ (eventLaw runtime delay delayLaw coinLaw event).support) :
    seed.1.val ≤ delay event := by
  obtain ⟨first, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨coins, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact Nat.le_of_lt_succ first.isLt

/-- A genuine first callback leaves the complete protected inclusion window
before expiry, using the actual bounded original delay rather than a service premise. -/
theorem first_callback_protected (delay bound : graph.EventId → Nat)
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
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false)
    (first : ¬ PhaseCount.ResponseRecorded runtime leaks owner coordinate.1
      (execution.recall owner))
    (delayLaw : (event : graph.EventId) → PMF (Fin (delay event + 1)))
    (coinLaw : graph.EventId → Fin (clockLimit runtime delay + 1) → PMF Bool)
    (supported : seeds.2 coordinate ∈
      (eventLaw runtime delay delayLaw coinLaw coordinate.1.event).support)
    (timely : AsyncTimely runtime delay bound) :
    (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
      (execution.recall owner) (execution.observe app owner)).elapsed + bound coordinate.1.event <
        runtime.deadline coordinate.1.event ∧
      execution.application.current.native.WithinDeadline runtime coordinate.1.event := by
  have elapsed := first_delay_eq_elapsed_of_unrecorded runtime leaks delay bound priority seeds
    bounds plan ordered maximal inputs horizon remaining owner execution trace coordinate request
      unsent first
  have bounded := eventLaw_first_delay_le runtime delay delayLaw coinLaw coordinate.1.event
    (seeds.2 coordinate) supported
  have fitting := timely coordinate.1.event (by rw [request.2.2.2.1]; rfl)
  have window : (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
      (execution.recall owner) (execution.observe app owner)).elapsed + bound coordinate.1.event <
        runtime.deadline coordinate.1.event := by omega
  refine ⟨window, ?_⟩
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon _ trace
  obtain ⟨input, invariant, _, _⟩ := currentTokenPrerequisites_history runtime leaks plan inputs
    horizon _ raw
  obtain ⟨entered, activated⟩ := Option.isSome_iff_exists.mp
    ((invariant.active.activated_iff coordinate.1.event).mpr
      ⟨request.2.2.1, by rw [request.2.2.2.1]; rfl⟩)
  change execution.application.current.native.activatedAt coordinate.1.event = some entered
    at activated
  change execution.application.current.native.clock -
    (execution.application.current.native.activatedAt coordinate.1.event).getD
      execution.application.current.native.clock + bound coordinate.1.event < _ at window
  rw [activated, Option.getD_some] at window
  simp only [State.WithinDeadline, activated]
  omega

end Vegas.EventGraphRuntime.PhaseSeedCalendar
