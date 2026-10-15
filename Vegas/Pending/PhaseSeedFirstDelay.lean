/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedUnsentQueries

/-! # Exact first-delay constraints from an activation and its previous wait -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Without an emitted packet the calendar either activates, waits, or expires;
no inclusion coin enters this exact command expression. -/
theorem reply_of_no_emissions (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner) (seed : Seed runtime delay)
    (query : PhaseSeedOperationalInput graph) (empty : query.emissions = []) :
    reply runtime leaks delay bound coordinate seed query =
      if runtime.deadline coordinate.1.event ≤ query.elapsed then
        .application (.expire coordinate.1.event)
      else if seed.1.val ≤ query.elapsed ∧ query.elapsed ∉ query.activationClocks then
        .activate owner else .wait := by
  by_cases due : runtime.deadline coordinate.1.event ≤ query.elapsed
  · simp only [reply, decision, ite_eq_left due]
  · by_cases activate : seed.1.val ≤ query.elapsed ∧ query.elapsed ∉ query.activationClocks
    · simp only [reply, decision, ite_eq_right due, ite_eq_left activate, actor,
        Option.map_some, Option.getD_some]
    · simp only [reply, decision, ite_eq_right due, ite_eq_right activate, empty,
        List.zipIdx_nil, List.find?_nil]

/-- An actual empty-word activation brackets the immutable delay from above. -/
theorem first_le_of_empty_activation (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner) (seed : Seed runtime delay)
    (query : PhaseSeedOperationalInput graph) (empty : query.emissions = [])
    (activated : reply runtime leaks delay bound coordinate seed query = .activate owner) :
    query.elapsed < runtime.deadline coordinate.1.event ∧ seed.1.val ≤ query.elapsed := by
  rw [reply_of_no_emissions runtime leaks delay bound coordinate owner actor seed query empty]
    at activated
  split at activated
  · cases activated
  · rename_i timely
    split at activated
    · rename_i ready
      exact ⟨Nat.lt_of_not_ge timely, ready.1⟩
    · cases activated

/-- Before an unrecorded activation clock, an empty-word wait brackets the
immutable delay strictly from below. -/
theorem elapsed_lt_first_of_empty_wait (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner) (seed : Seed runtime delay)
    (query : PhaseSeedOperationalInput graph) (empty : query.emissions = [])
    (timely : query.elapsed < runtime.deadline coordinate.1.event)
    (unrecorded : query.elapsed ∉ query.activationClocks)
    (waited : reply runtime leaks delay bound coordinate seed query = .wait) :
    query.elapsed < seed.1.val := by
  rw [reply_of_no_emissions runtime leaks delay bound coordinate owner actor seed query empty,
    ite_eq_right (Nat.not_le_of_gt timely)] at waited
  by_contra lower
  have activate : seed.1.val ≤ query.elapsed ∧ query.elapsed ∉ query.activationClocks :=
    ⟨Nat.le_of_not_gt lower, unrecorded⟩
  rw [ite_eq_left activate] at waited
  cases waited

/-- A first activation and a queried wait at its preceding unrecorded clock
identify the first delay for EVERY candidate passing the actual command filter.
The zero-delay endpoint needs no preceding clock. -/
theorem first_eq_of_coordinateConsistent_of_bracket (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner)
    (past : List (app).EnvironmentEntry) (firstClock : Nat)
    (empty : ∀ item ∈ (controller runtime leaks delay bound priority).coordinateTranscriptFrom
      rest coordinate [] past, item.1.emissions = [])
    (positive : ∃ item ∈ (controller runtime leaks delay bound priority).coordinateTranscriptFrom
      rest coordinate [] past, item.1.elapsed = firstClock ∧ item.2 = .activate owner)
    (previous : firstClock = 0 ∨ ∃ item ∈
      (controller runtime leaks delay bound priority).coordinateTranscriptFrom
        rest coordinate [] past,
      item.1.elapsed + 1 = firstClock ∧ item.1.elapsed ∉ item.1.activationClocks ∧ item.2 = .wait)
    (candidate : Seed runtime delay)
    (consistent : (controller runtime leaks delay bound priority).coordinateConsistentFrom
      rest coordinate candidate [] past) : candidate.1.val = firstClock := by
  have matched := (ReactiveApplication.AddressedScheduler.coordinateConsistentFrom_iff_transcript
    _ rest coordinate candidate [] past).mp consistent
  obtain ⟨item, present, clockEq, activated⟩ := positive
  have upper := first_le_of_empty_activation runtime leaks delay bound coordinate owner actor
    candidate item.1 (empty item present) ((matched item present).trans activated)
  rw [clockEq] at upper
  rcases previous with zero | ⟨earlier, member, adjacent, unrecorded, waited⟩
  · omega
  · have timely : earlier.1.elapsed < runtime.deadline coordinate.1.event := by omega
    have lower := elapsed_lt_first_of_empty_wait runtime leaks delay bound coordinate owner actor
      candidate earlier.1 (empty earlier member) timely unrecorded
      ((matched earlier member).trans waited)
    omega

end Vegas.EventGraphRuntime.PhaseSeedCalendar
