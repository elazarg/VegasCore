/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceActivationRecall
import Vegas.Pending.PhaseSeedClosedQueries

/-! # Actual negative queries for arbitrary phased service decisions

Every local reply is an activation, an own inclusion, expiry or wait.
The argument uses arbitrary local decision functions and immutable seed types. Only the
remainder fallback can advance time, and it runs only after all current ready
coordinates have been closed at this clock.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

private theorem roster_empty_of_select_none
    (closed : Finset (Nat × PhaseSeedAddress graph)) (view : (app).EnvironmentView)
    (index : Nat) (selected : PhaseSeedCalendar.selectOpen runtime leaks closed view index = none) :
    PhaseSeedCalendar.openRoster runtime leaks closed view = ∅ := by
  unfold PhaseSeedCalendar.selectOpen at selected
  cases indexed : (PhaseSeedCalendar.openRoster runtime leaks closed view).toList[index]? with
  | none =>
      simp only [indexed, Option.none_or] at selected
      have empty : (PhaseSeedCalendar.openRoster runtime leaks closed view).toList = [] := by
        cases shaped : (PhaseSeedCalendar.openRoster runtime leaks closed view).toList with
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
theorem reply_ne_advanceClock
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (coordinate : PhaseSeedAddress graph) (seed : LocalSeed)
    (query : PhaseSeedOperationalInput graph) :
    reply runtime leaks decideLocal coordinate seed query ≠ .application .advanceClock := by
  unfold reply
  cases decideLocal coordinate seed query with
  | activation => cases graph.actor? coordinate.1.event <;> simp
  | inclusion index => cases emitted : query.emissions[index]? <;> simp [emitted]
  | expiry => simp
  | wait => simp

/-- The actual fixed-seed driver advances the clock only after its entire ready
roster is exhausted, independently of the priority ordering. -/
theorem choose_advanceClock_roster_empty
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView)
    (advance : (controller runtime leaks priority decideLocal).choose seeds past view =
      .application .advanceClock) :
    PhaseSeedCalendar.openRoster runtime leaks
      (PhaseSeedCalendar.replayClosed runtime leaks priority seeds.1 past) view = ∅ := by
  unfold ReactiveApplication.AddressedScheduler.choose controller at advance
  cases chosen : PhaseSeedCalendar.selectOpen runtime leaks
      (PhaseSeedCalendar.replayClosed runtime leaks priority seeds.1 past)
      view (priority seeds.1 past view) with
  | none => exact roster_empty_of_select_none runtime leaks _ _ _ chosen
  | some coordinate =>
      have member := (Finset.mem_filter.mp
        (PhaseSeedCalendar.selectOpen_mem runtime leaks chosen)).1
      obtain ⟨owner, ready⟩ := (PhaseSeedScheduler.mem_eligible runtime leaks _ _).mp member
      simp only [chosen, Option.bind_some, ready.2.2.2.1, Option.map_some] at advance
      exact (reply_ne_advanceClock runtime leaks decideLocal coordinate _ _ advance).elim

/-- At a genuine current request, advancing time proves that this address has
already received its nonactivation reply for the current tick. -/
theorem clockAdvance_request_closed
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (execution : (app).Execution) {inputs : graph.Inputs}
    (valid : execution.application.Invariant inputs) (budget : execution.application.SeedBudget)
    {owner : Player} {coordinate : CommitAttemptEvent graph}
    (request : execution.application.SeedRequest owner coordinate)
    (advance : (controller runtime leaks priority decideLocal).choose seeds
      execution.environmentRecall (execution.observeEnvironment app) = .application .advanceClock) :
    (execution.application.current.native.clock, request.coordinate budget) ∈
      PhaseSeedCalendar.replayClosed runtime leaks priority seeds.1
        execution.environmentRecall := by
  classical
  have covered := PhaseSeedScheduler.request_covered runtime leaks valid budget request
  have empty := choose_advanceClock_roster_empty runtime leaks priority decideLocal seeds _ _
    advance
  by_contra unclosed
  have member : request.coordinate budget ∈ PhaseSeedCalendar.openRoster runtime leaks
      (PhaseSeedCalendar.replayClosed runtime leaks priority seeds.1 execution.environmentRecall)
        (execution.observeEnvironment app) := Finset.mem_filter.mpr ⟨covered, unclosed⟩
  rw [empty] at member
  exact Finset.notMem_empty _ member

/-- Before advancing time at a genuine ready request, the actual driver has
already queried this original address at this clock and recorded a nonactivation
reply. The ordering may depend on the complete environment history and view. -/
theorem clockAdvance_query_origin
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (execution : (app).Execution) {inputs : graph.Inputs}
    (valid : execution.application.Invariant inputs) (budget : execution.application.SeedBudget)
    {owner : Player} {coordinate : CommitAttemptEvent graph}
    (request : execution.application.SeedRequest owner coordinate)
    (advance : (controller runtime leaks priority decideLocal).choose seeds
      execution.environmentRecall (execution.observeEnvironment app) = .application .advanceClock) :
    ∃ before entry after query,
      execution.environmentRecall = before ++ entry :: after ∧
      entry.beforeView.application.native.clock = execution.application.current.native.clock ∧
      (controller runtime leaks priority decideLocal).request seeds.1 before entry.beforeView =
        some (request.coordinate budget, query) ∧ (entry.command.actor? app).isNone = true := by
  have closed := clockAdvance_request_closed runtime leaks priority decideLocal seeds execution
    valid budget request advance
  obtain impossible | ⟨before, entry, after, splitEq, clockEq, selected, idle⟩ :=
    PhaseSeedCalendar.replayClosedFrom_origin runtime leaks priority seeds.1 ∅ []
      execution.environmentRecall
      execution.application.current.native.clock (request.coordinate budget) closed
  · exact (Finset.notMem_empty _ impossible).elim
  · have member := (Finset.mem_filter.mp
      (PhaseSeedCalendar.selectOpen_mem runtime leaks selected)).1
    obtain ⟨acting, ready⟩ := (PhaseSeedScheduler.mem_eligible runtime leaks _ _).mp member
    refine ⟨before, entry, after,
      PhaseSeedInput.operational coordinate.attempt
        (PhaseSeedScheduler.localInput runtime leaks coordinate acting before entry.beforeView),
      splitEq, clockEq.symm, ?_, idle⟩
    simp only [List.nil_append] at selected
    simp only [controller, PhaseSeedCalendar.replayClosed, selected, Option.bind_some,
      ready.2.2.2.1,
      Option.map_some]
    rfl


end Vegas.EventGraphRuntime.PhaseServiceScheduler
