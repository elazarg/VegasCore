/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedClockProgress
import Interaction.ReactiveAddressedQueryTranscript

/-! # Actual nonactivation queries behind a drained calendar tick -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A reconstructed closure record has an actual selected nonactivation entry.
Its prefix is the complete environment history, not an erased remainder log. -/
theorem replayClosedFrom_origin
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (closed : Finset (Nat × PhaseSeedAddress graph))
    (earlier later : List (app).EnvironmentEntry) (tick : Nat)
    (coordinate : PhaseSeedAddress graph)
    (member : (tick, coordinate) ∈
      replayClosedFrom runtime leaks priority rest closed earlier later) :
    (tick, coordinate) ∈ closed ∨
      ∃ before entry after, later = before ++ entry :: after ∧
        tick = entry.beforeView.application.native.clock ∧
        selectOpen runtime leaks
          (replayClosedFrom runtime leaks priority rest closed earlier before) entry.beforeView
            (priority rest (earlier ++ before) entry.beforeView) = some coordinate ∧
        (entry.command.actor? app).isNone = true := by
  induction later generalizing closed earlier with
  | nil => exact Or.inl member
  | cons head tail ih =>
      obtain old | ⟨before, entry, after, splitEq, clockEq, selected, idle⟩ :=
        ih (closeAfter runtime leaks closed head.beforeView
          (selectOpen runtime leaks closed head.beforeView
            (priority rest earlier head.beforeView)) head.command) (earlier ++ [head]) member
      · by_cases idle : (head.command.actor? app).isNone = true
        · simp only [closeAfter, idle, ite_true] at old
          cases selected : selectOpen runtime leaks closed head.beforeView
              (priority rest earlier head.beforeView) with
          | none => exact Or.inl (by simpa only [selected, Option.elim_none] using old)
          | some chosen =>
              simp only [selected, Option.elim_some, Finset.mem_insert] at old
              rcases old with same | previous
              · have clockEq : tick = head.beforeView.application.native.clock :=
                  congrArg Prod.fst same
                have coordinateEq : coordinate = chosen := congrArg Prod.snd same
                refine Or.inr ⟨[], head, tail, rfl, clockEq, ?_, idle⟩
                simpa only [List.append_nil, replayClosedFrom, coordinateEq] using selected
              · exact Or.inl previous
        · exact Or.inl (by simpa [closeAfter, idle] using old)
      · refine Or.inr ⟨head :: before, entry, after, ?_, clockEq, ?_, idle⟩
        · rw [splitEq]
          rfl
        · simpa only [replayClosedFrom, List.cons_append, List.append_assoc,
            List.singleton_append, List.nil_append] using selected

/-- Before advancing time at a genuine ready request, the actual driver has
already queried this original address at this clock and recorded a nonactivation
reply. The ordering may depend on the complete environment history and view. -/
theorem clockAdvance_query_origin (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (execution : (app).Execution) {inputs : graph.Inputs}
    (valid : execution.application.Invariant inputs) (budget : execution.application.SeedBudget)
    {owner : Player} {coordinate : CommitAttemptEvent graph}
    (request : execution.application.SeedRequest owner coordinate)
    (advance : (controller runtime leaks delay bound priority).choose seeds
      execution.environmentRecall (execution.observeEnvironment app) = .application .advanceClock) :
    ∃ before entry after query,
      execution.environmentRecall = before ++ entry :: after ∧
      entry.beforeView.application.native.clock = execution.application.current.native.clock ∧
      (controller runtime leaks delay bound priority).request seeds.1 before entry.beforeView =
        some (request.coordinate budget, query) ∧ (entry.command.actor? app).isNone = true := by
  have closed := clockAdvance_request_closed runtime leaks delay bound priority seeds execution
    valid budget request advance
  obtain impossible | ⟨before, entry, after, splitEq, clockEq, selected, idle⟩ :=
    replayClosedFrom_origin runtime leaks priority seeds.1 ∅ [] execution.environmentRecall
      execution.application.current.native.clock (request.coordinate budget) closed
  · exact (Finset.notMem_empty _ impossible).elim
  · have member := (Finset.mem_filter.mp (selectOpen_mem runtime leaks selected)).1
    obtain ⟨acting, ready⟩ := (PhaseSeedScheduler.mem_eligible runtime leaks _ _).mp member
    refine ⟨before, entry, after,
      PhaseSeedInput.operational coordinate.attempt
        (PhaseSeedScheduler.localInput runtime leaks coordinate acting before entry.beforeView),
      splitEq, clockEq.symm, ?_, idle⟩
    simp only [List.nil_append] at selected
    simp only [controller, replayClosed, selected, Option.bind_some, ready.2.2.2.1,
      Option.map_some]
    rfl

end Vegas.EventGraphRuntime.PhaseSeedCalendar
