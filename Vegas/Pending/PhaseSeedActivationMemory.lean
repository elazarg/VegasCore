/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedCalendarProperties
import Vegas.Pending.PhaseSeedRecall

/-! # Actual owner recall prevents repeated activation at a local tick -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
/-- Every genuine previous callback remains in the full local clock word,
including callbacks whose physical attempt is later voided. -/
theorem localInput_activation_of_entry (coordinate : CommitAttemptEvent graph) (owner : Player)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView)
    (entry : (app).EnvironmentEntry) (member : entry ∈ past)
    (activated : entry.command = .activate owner)
    (requested : PhaseRuntimeState.requests entry.beforeView.application owner coordinate) :
    PhaseSeedScheduler.elapsed runtime leaks coordinate entry.beforeView ∈
      (PhaseSeedScheduler.localInput runtime leaks coordinate owner past view).activationClocks :=
    by
  classical
  have projection :
      (past.zip (past.tail.map (·.beforeView) ++ [view])).map Prod.fst = past := by
    apply List.map_fst_zip
    simp only [List.length_append, List.length_map, List.length_tail, List.length_singleton]
    omega
  have mapped : entry ∈ (past.zip (past.tail.map (·.beforeView) ++ [view])).map Prod.fst := by
    rwa [projection]
  obtain ⟨pair, paired, same⟩ := List.mem_map.mp mapped
  change _ ∈ ((past.zip (past.tail.map (·.beforeView) ++ [view])).filter _).map _
  refine List.mem_map.mpr ⟨pair, List.mem_filter.mpr ⟨paired, ?_⟩, ?_⟩
  · exact decide_eq_true ⟨same ▸ activated, same ▸ requested⟩
  · exact congrArg (fun record : (app).EnvironmentEntry =>
      PhaseSeedScheduler.elapsed runtime leaks coordinate record.beforeView) same

/-- The concrete reply at a remembered local activation clock cannot activate
again. Raw payloads and all foreign interleavings are absent from this test. -/
theorem reply_ne_activate_of_entry (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (seed : Seed runtime delay) (owner : Player)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView)
    (entry : (app).EnvironmentEntry) (member : entry ∈ past)
    (activated : entry.command = .activate owner)
    (requested : PhaseRuntimeState.requests entry.beforeView.application owner coordinate.1)
    (sameClock : PhaseSeedScheduler.elapsed runtime leaks coordinate.1 entry.beforeView =
      PhaseSeedScheduler.elapsed runtime leaks coordinate.1 view) :
    reply runtime leaks delay bound coordinate seed
      (PhaseSeedInput.operational coordinate.1.attempt
        (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner past view)) ≠
        .activate owner := by
  have recorded := localInput_activation_of_entry runtime leaks coordinate.1 owner past view entry
    member activated requested
  rw [sameClock] at recorded
  have notActivation := decision_ne_activation_of_recorded runtime delay bound coordinate seed
    (PhaseSeedInput.operational coordinate.1.attempt
      (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner past view)) recorded
  unfold reply
  cases chosen : decision runtime delay bound coordinate seed
      (PhaseSeedInput.operational coordinate.1.attempt
        (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner past view)) with
  | activation => exact (notActivation chosen).elim
  | inclusion index =>
      cases emitted : (PhaseSeedInput.operational coordinate.1.attempt
        (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner past view)).emissions[
          index]?
      <;> simp only [emitted, Option.map_none, Option.getD_none, Option.map_some, Option.getD_some]
      <;> intro impossible <;> cases impossible
  | expiry => intro impossible; cases impossible
  | wait => intro impossible; cases impossible

end Vegas.EventGraphRuntime.PhaseSeedCalendar
