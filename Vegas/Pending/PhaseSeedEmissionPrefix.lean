/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedRecall

/-! # An emitted clock is retained before every later callback at that clock -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedScheduler

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

private theorem adjacent_append (earlier : List (app).EnvironmentEntry)
    (entry : (app).EnvironmentEntry) (later : List (app).EnvironmentEntry)
    (view : (app).EnvironmentView) :
    adjacent runtime leaks (earlier ++ entry :: later) view =
      adjacent runtime leaks earlier entry.beforeView ++
        adjacent runtime leaks (entry :: later) view := by
  induction earlier with
  | nil => rfl
  | cons head rest ih =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          change (head, second.beforeView) ::
              adjacent runtime leaks ((second :: rest) ++ entry :: later) view =
            (head, second.beforeView) :: (adjacent runtime leaks (second :: rest)
              entry.beforeView ++ adjacent runtime leaks (entry :: later) view)
          exact congrArg ((head, second.beforeView) :: ·) ih

private theorem word_append (coordinate : CommitAttemptEvent graph) (owner : Player)
    (earlier : List (app).EnvironmentEntry) (entry : (app).EnvironmentEntry)
    (later : List (app).EnvironmentEntry) (view : (app).EnvironmentView) :
    word runtime leaks coordinate owner (earlier ++ entry :: later) view =
      word runtime leaks coordinate owner earlier entry.beforeView ++
        word runtime leaks coordinate owner (entry :: later) view := by
  classical
  simp only [word, adjacent_append, List.filter_append, List.map_append]

/-- If no callback in a suffix has this relative clock, every envelope emitted
at that clock is already present in the exact preceding environment query. -/
theorem emission_mem_before_suffix (coordinate : CommitAttemptEvent graph) (owner : Player)
    (earlier : List (app).EnvironmentEntry) (entry : (app).EnvironmentEntry)
    (later : List (app).EnvironmentEntry) (view : (app).EnvironmentView)
    (clock : Nat) (message : Message Player (CommitAttemptPacket graph))
    (emitted : (clock, message) ∈ (localInput runtime leaks coordinate owner
      (earlier ++ entry :: later) view).emissions)
    (absent : ∀ record ∈ entry :: later, callback runtime leaks coordinate owner record →
      elapsed runtime leaks coordinate record.beforeView ≠ clock) :
    (clock, message) ∈
      (localInput runtime leaks coordinate owner earlier entry.beforeView).emissions := by
  classical
  rw [localInput_word, word_append] at emitted
  simp only [List.flatMap_append, List.mem_append] at emitted
  rcases emitted with earlierEmission | laterEmission
  · simpa only [localInput_word] using earlierEmission
  · obtain ⟨record, recorded, packet⟩ := List.mem_flatMap.mp laterEmission
    obtain ⟨pair, selected, recordEq⟩ := List.mem_map.mp recorded
    obtain ⟨packet, _member, pairEq⟩ := List.mem_map.mp packet
    have source := List.mem_filter.mp selected
    have callbackHere : callback runtime leaks coordinate owner pair.1 :=
      of_decide_eq_true source.2
    have inSuffix : pair.1 ∈ entry :: later := (List.of_mem_zip source.1).1
    have clockEq : elapsed runtime leaks coordinate pair.1.beforeView = clock :=
      (congrArg Prod.fst recordEq).trans (congrArg Prod.fst pairEq)
    exact (absent pair.1 inSuffix callbackHere clockEq).elim

end Vegas.EventGraphRuntime.PhaseSeedScheduler
