/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedClockLog

/-! # Clock advancement follows exhaustion of the current finite roster

Every local reply is an activation, an own inclusion, expiry or wait. Only the
remainder fallback can advance time, and it runs only after all current ready
coordinates have been closed at this clock.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

private theorem roster_empty_of_select_none
    (closed : Finset (Nat × PhaseSeedAddress graph)) (view : (app).EnvironmentView)
    (index : Nat) (selected : selectOpen runtime leaks closed view index = none) :
    openRoster runtime leaks closed view = ∅ := by
  unfold selectOpen at selected
  cases indexed : (openRoster runtime leaks closed view).toList[index]? with
  | none =>
      simp only [indexed, Option.none_or] at selected
      have empty : (openRoster runtime leaks closed view).toList = [] := by
        cases shaped : (openRoster runtime leaks closed view).toList with
        | nil => rfl
        | cons first later =>
            simp only [shaped, List.head?_cons] at selected
            cases selected
      apply Finset.eq_empty_of_forall_notMem
      intro coordinate member
      have listMember := Finset.mem_toList.mpr member
      simp only [empty, List.not_mem_nil] at listMember
  | some coordinate =>
      simp only [indexed, Option.some_or] at selected
      cases selected

/-- A local coordinate cannot advance the global clock or execute a sample. -/
theorem reply_ne_advanceClock (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (seed : Seed runtime delay)
    (query : PhaseSeedOperationalInput graph) :
    reply runtime leaks delay bound coordinate seed query ≠ .application .advanceClock := by
  unfold reply
  cases decision runtime delay bound coordinate seed query with
  | activation => cases graph.actor? coordinate.1.event <;> simp
  | inclusion index => cases emitted : query.emissions[index]? <;> simp [emitted]
  | expiry => simp
  | wait => simp

/-- The actual fixed-seed driver advances the clock only after its entire ready
roster is exhausted, independently of the priority ordering. -/
theorem choose_advanceClock_roster_empty (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (Nat × CommitAttemptId) → Nat × CommitAttemptId → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView)
    (advance : (controller runtime leaks delay bound priority).choose seeds past view =
      .application .advanceClock) :
    openRoster runtime leaks (replayClosed runtime leaks priority seeds.1 past) view = ∅ := by
  unfold ReactiveApplication.AddressedScheduler.choose controller at advance
  cases chosen : selectOpen runtime leaks (replayClosed runtime leaks priority seeds.1 past)
      view (orderPriority runtime leaks priority seeds.1 past view) with
  | none => exact roster_empty_of_select_none runtime leaks _ _ _ chosen
  | some coordinate =>
      have member := (Finset.mem_filter.mp (selectOpen_mem runtime leaks chosen)).1
      obtain ⟨owner, ready⟩ := (PhaseSeedScheduler.mem_eligible runtime leaks _ _).mp member
      simp only [chosen, Option.bind_some, ready.2.2.2.1, Option.map_some] at advance
      exact (reply_ne_advanceClock runtime leaks delay bound coordinate _ _ advance).elim

/-- At a genuine current request, advancing time proves that this address has
already received its nonactivation reply for the current tick. -/
theorem clockAdvance_request_closed (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (Nat × CommitAttemptId) → Nat × CommitAttemptId → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (execution : (app).Execution) {inputs : graph.Inputs}
    (valid : execution.application.Invariant inputs) (budget : execution.application.SeedBudget)
    {owner : Player} {coordinate : CommitAttemptEvent graph}
    (request : execution.application.SeedRequest owner coordinate)
    (advance : (controller runtime leaks delay bound priority).choose seeds
      execution.environmentRecall (execution.observeEnvironment app) = .application .advanceClock) :
    (execution.application.current.native.clock, request.coordinate budget) ∈
      replayClosed runtime leaks priority seeds.1 execution.environmentRecall := by
  classical
  have covered := PhaseSeedScheduler.request_covered runtime leaks valid budget request
  have empty := choose_advanceClock_roster_empty runtime leaks delay bound priority seeds _ _
    advance
  by_contra unclosed
  have member : request.coordinate budget ∈ openRoster runtime leaks
      (replayClosed runtime leaks priority seeds.1 execution.environmentRecall)
        (execution.observeEnvironment app) := Finset.mem_filter.mpr ⟨covered, unclosed⟩
  rw [empty] at member
  exact Finset.notMem_empty _ member

end Vegas.EventGraphRuntime.PhaseSeedCalendar
