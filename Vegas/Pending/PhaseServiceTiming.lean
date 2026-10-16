/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceClockQueries
import Vegas.Pending.PhaseSeedCalendarProperties
import Vegas.Pending.PhaseSeedQueryMarks

/-! # Deadline discipline for arbitrary event-local service rules -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Expiry occurs exactly when this coordinate's readiness-relative deadline
has arrived. Other local decisions, including repeated activations, are free. -/
def DeadlineExpiry
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision) : Prop :=
  ∀ coordinate seed input, decideLocal coordinate seed input = .expiry ↔
    runtime.deadline coordinate.1.event ≤ input.elapsed

omit [DecidableEq Player] in
/-- The delay-and-coin rule satisfies the same deadline discipline. -/
theorem deadlineExpiry_calendar (delay bound : graph.EventId → Nat) :
    DeadlineExpiry runtime (PhaseSeedCalendar.decision runtime delay bound) := by
  intro coordinate seed input
  constructor
  · intro chosen
    unfold PhaseSeedCalendar.decision at chosen
    split at chosen
    · assumption
    · split at chosen
      · cases chosen
      · dsimp only at chosen
        split at chosen <;> cases chosen
  · exact PhaseSeedCalendar.decision_deadline runtime delay bound coordinate seed input

/-- The shared closed-tick selector supplies the exact queried operational
word, for any local decision function and original seed vector. -/
theorem request_of_selected
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (rest : RestSeed) (execution : (app).Execution) (coordinate : PhaseSeedAddress graph)
    (selected : PhaseSeedCalendar.selectedAt runtime leaks priority rest execution =
      some coordinate)
    (owner : Player) (actor : graph.actor? coordinate.1.event = some owner) :
    (controller runtime leaks priority decideLocal).request rest
      execution.environmentRecall (execution.observeEnvironment app) =
        some (coordinate, queryAt runtime leaks execution coordinate owner) := by
  simp only [PhaseSeedCalendar.selectedAt] at selected
  simp only [controller, selected, Option.bind_some, actor, Option.map_some, queryAt]

/-- At a selected coordinate the actual scheduler command is exactly its local
reply, with the full original environment history retained. -/
theorem choose_of_selected
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (execution : (app).Execution) (coordinate : PhaseSeedAddress graph)
    (selected : PhaseSeedCalendar.selectedAt runtime leaks priority seeds.1 execution =
      some coordinate)
    (owner : Player) (actor : graph.actor? coordinate.1.event = some owner) :
    (controller runtime leaks priority decideLocal).choose seeds execution.environmentRecall
      (execution.observeEnvironment app) = reply runtime leaks decideLocal coordinate
        (seeds.2 coordinate) (queryAt runtime leaks execution coordinate owner) := by
  unfold ReactiveApplication.AddressedScheduler.choose
  rw [request_of_selected runtime leaks priority decideLocal seeds.1 execution coordinate
    selected owner actor]
  rfl

end Vegas.EventGraphRuntime.PhaseServiceScheduler
