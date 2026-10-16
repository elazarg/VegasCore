/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedLogRecovery

/-! # Recovering local logs with index-determined emission prefixes

Changing the emitted prefix of a query preserves its clock, activation index
and reply. Erasure therefore reuses unsent-log uniqueness, and an emission
prefix determined by the activation index restores the complete original log.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

local notation "app" => runtime.reactiveApplication leaks

/-- Replace only a query's authored packet prefix, indexed by its local activation count. -/
def setQueryEmissions (emittedAt : Nat → List (Message Player (WitnessedPacket graph)))
    (entry : LocalSeedEntry graph (app).Command) : LocalSeedEntry graph (app).Command :=
  { entry with query := { entry.query with input :=
    { entry.query.input with emitted := emittedAt entry.query.activationIndex } } }

theorem positiveQueries_setEmissions
    (emittedAt : Nat → List (Message Player (WitnessedPacket graph)))
    (log : List (LocalSeedEntry graph (app).Command)) :
    positiveQueries (log.map (setQueryEmissions emittedAt)) =
      (positiveQueries log).map (fun query => { query with input :=
        { query.input with emitted := emittedAt query.activationIndex } }) := by
  simp only [positiveQueries, List.filterMap_map, List.map_filterMap]
  apply congrArg (fun select => log.filterMap select)
  funext entry
  dsimp only [Function.comp_def, setQueryEmissions]
  cases entry.reply <;> rfl

theorem exhaustedClocks_setEmissions
    (emittedAt : Nat → List (Message Player (WitnessedPacket graph)))
    (log : List (LocalSeedEntry graph (app).Command)) :
    exhaustedClocks (log.map (setQueryEmissions emittedAt)) = exhaustedClocks log := by
  simp only [exhaustedClocks, List.filterMap_map]
  apply congrArg (fun select => log.filterMap select)
  funext entry
  dsimp only [Function.comp_def, setQueryEmissions]

/-- Query clock/index counters are independent of their emitted packet lists. -/
theorem CountedQueryLog.setEmissions
    {log : List (LocalSeedEntry graph (app).Command)} (recorded : CountedQueryLog log)
    (emittedAt : Nat → List (Message Player (WitnessedPacket graph))) :
    CountedQueryLog (log.map (setQueryEmissions emittedAt)) := by
  induction recorded with
  | empty => exact CountedQueryLog.empty
  | @append past recorded entry clock index ih =>
      rw [List.map_append, List.map_cons, List.map_nil]
      refine CountedQueryLog.append ih (setQueryEmissions emittedAt entry) ?_ ?_
      · change entry.query.input.elapsed =
          (exhaustedClocks (past.map (setQueryEmissions emittedAt))).length
        rw [exhaustedClocks_setEmissions]
        exact clock
      · change entry.query.activationIndex =
          (positiveQueries (past.map (setQueryEmissions emittedAt))).length
        rw [positiveQueries_setEmissions, List.length_map]
        exact index

theorem setQueryEmissions_comp
    (first second : Nat → List (Message Player (WitnessedPacket graph)))
    (entry : LocalSeedEntry graph (app).Command) :
    setQueryEmissions first (setQueryEmissions second entry) = setQueryEmissions first entry := rfl

private theorem setQueryEmissions_eq
    (emittedAt : Nat → List (Message Player (WitnessedPacket graph)))
    (entry : LocalSeedEntry graph (app).Command)
    (fixed : entry.query.input.emitted = emittedAt entry.query.activationIndex) :
    setQueryEmissions emittedAt entry = entry := by
  cases entry with
  | mk query reply =>
      cases query with
      | mk input index =>
          cases input with
          | mk elapsed emitted =>
              change emitted = emittedAt index at fixed
              cases fixed
              rfl

/-- Raw logs are uniquely determined by positive owner queries and closed clocks
once their emitted prefix is reconstructed from the same owner activation index. -/
theorem CountedQueryLog.eq_of_emission_signature
    (emittedAt : Nat → List (Message Player (WitnessedPacket graph)))
    {first second : List (LocalSeedEntry graph (app).Command)}
    (left : CountedQueryLog first) (right : CountedQueryLog second)
    (leftEmitted : ∀ entry ∈ first,
      entry.query.input.emitted = emittedAt entry.query.activationIndex)
    (rightEmitted : ∀ entry ∈ second,
      entry.query.input.emitted = emittedAt entry.query.activationIndex)
    (leftUnresolved : ∀ entry ∈ first, entry.reply = .activation ∨ entry.reply = .exhausted)
    (rightUnresolved : ∀ entry ∈ second, entry.reply = .activation ∨ entry.reply = .exhausted)
    (positiveEq : positiveQueries first = positiveQueries second)
    (closedEq : (exhaustedClocks first).length = (exhaustedClocks second).length) :
    first = second := by
  let erase := setQueryEmissions (runtime := runtime) (leaks := leaks) (fun _ => [])
  have erasedUnsent (log : List (LocalSeedEntry graph (app).Command)) :
      ∀ entry ∈ log.map erase, entry.query.input.emitted = [] := by
    intro entry member
    obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
    rfl
  have erasedUnresolved (log : List (LocalSeedEntry graph (app).Command))
      (unresolved : ∀ entry ∈ log, entry.reply = .activation ∨ entry.reply = .exhausted) :
      ∀ entry ∈ log.map erase, entry.reply = .activation ∨ entry.reply = .exhausted := by
    intro entry member
    obtain ⟨original, earlier, rfl⟩ := List.mem_map.mp member
    exact unresolved original earlier
  have positives : positiveQueries (first.map erase) = positiveQueries (second.map erase) := by
    rw [positiveQueries_setEmissions, positiveQueries_setEmissions, positiveEq]
  have clocks : (exhaustedClocks (first.map erase)).length =
      (exhaustedClocks (second.map erase)).length := by
    rw [exhaustedClocks_setEmissions, exhaustedClocks_setEmissions, closedEq]
  have erased := (left.setEmissions (fun _ => [])).eq_of_unsent_signature
    (right.setEmissions (fun _ => [])) (erasedUnsent first) (erasedUnsent second)
      (erasedUnresolved first leftUnresolved) (erasedUnresolved second rightUnresolved)
        (congrArg (List.map fun query : CurrentSeedQuery graph => query.input.elapsed) positives)
        clocks
  have restored (log : List (LocalSeedEntry graph (app).Command))
      (fixed : ∀ entry ∈ log, entry.query.input.emitted = emittedAt entry.query.activationIndex) :
      (log.map erase).map (setQueryEmissions emittedAt) = log := by
    calc
      _ = log.map id := by
        rw [List.map_map]
        apply List.map_congr_left
        intro entry member
        change setQueryEmissions emittedAt (erase entry) = entry
        rw [setQueryEmissions_comp]
        exact setQueryEmissions_eq emittedAt entry (fixed entry member)
      _ = _ := List.map_id log
  have same := congrArg (List.map (setQueryEmissions emittedAt)) erased
  rwa [restored first leftEmitted, restored second rightEmitted] at same

end Vegas.EventGraphRuntime.LocalSeedController
