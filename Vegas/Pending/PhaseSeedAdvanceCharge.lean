/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedTickInvariant
import Vegas.Pending.PhaseSeedClockCharge
import Vegas.Pending.PhaseLive

/-! # Every actual clock advance consumes a finite ready-event ticket -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

variable (delay bound : graph.EventId → Nat)
  (priority : RestSeed → List (Nat × CommitAttemptId) → Nat × CommitAttemptId → Nat)
  (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))

private theorem fallback_of_advance (execution : (app).Execution)
    (advance : (controller runtime leaks delay bound priority).choose seeds
      execution.environmentRecall (execution.observeEnvironment app) = .application .advanceClock) :
    fallback runtime leaks (execution.observeEnvironment app) = .application .advanceClock := by
  unfold ReactiveApplication.AddressedScheduler.choose controller at advance
  cases selected : selectOpen runtime leaks
      (replayClosed runtime leaks priority seeds.1 execution.environmentRecall)
      (execution.observeEnvironment app)
      (orderPriority runtime leaks priority seeds.1 execution.environmentRecall
        (execution.observeEnvironment app)) with
  | none => simpa only [selected, Option.bind_none] using advance
  | some coordinate =>
      have member := (Finset.mem_filter.mp (selectOpen_mem runtime leaks selected)).1
      obtain ⟨owner, request⟩ := (PhaseSeedScheduler.mem_eligible runtime leaks _ _).mp member
      simp only [selected, Option.bind_some, request.2.2.2.1, Option.map_some] at advance
      exact (reply_ne_advanceClock runtime leaks delay bound coordinate _ _ advance).elim

/-- The driver cannot increase time in a finished program or a sample phase.
Its actual live owned request supplies a previously closed, strictly early tick. -/
theorem advance_charge {inputs : graph.Inputs} (execution : (app).Execution)
    (safe : TickSafe runtime leaks delay priority seeds inputs execution)
    (budget : execution.application.SeedBudget)
    (frontier : execution.application.Frontier) (live : execution.application.Live)
    (quiescent : ∀ event, ¬ execution.application.current.AutomaticReady event)
    (advance : (controller runtime leaks delay bound priority).choose seeds
      execution.environmentRecall (execution.observeEnvironment app) = .application .advanceClock) :
    ∃ (charge : ClockCharge runtime) (owner : Player),
      charge.tick = execution.application.current.native.clock ∧
      execution.application.SeedRequest owner charge.coordinate.1 ∧
      execution.application.current.native.activatedAt charge.coordinate.1.event =
        some charge.entered ∧
      (charge.tick, charge.coordinate) ∈
        replayClosed runtime leaks priority seeds.1 execution.environmentRecall ∧
      ClosedCoordinateBound runtime charge.tick charge.entered charge.coordinate.1
        execution.application := by
  have fallbackEq := fallback_of_advance runtime leaks delay bound priority seeds execution advance
  have nonempty : execution.application.phases ≠ [] := by
    intro empty
    simp only [fallback, ReactiveApplication.Execution.observeEnvironment, phaseApplication,
      PhaseRuntimeState.publicView, empty, List.head?_nil, Option.map_none] at fallbackEq
    cases fallbackEq
  rcases execution.application.request_or_sample frontier live quiescent nonempty with
    ⟨owner, event, request⟩ | ⟨phase, event, head, sample, atLow, ready, actor⟩
  · have member := clockAdvance_request_closed runtime leaks delay bound priority seeds execution
      safe.invariant budget request advance
    obtain ⟨entered, closed⟩ := safe.closed _ member
    have status := closed.event request.1
    rcases status with completed | active
    · exact False.elim (request.2.2.1.1 completed)
    · refine ⟨⟨request.coordinate budget, execution.application.current.native.clock,
        entered, closed.entered_le, active.2.2⟩, owner, rfl, request, active.2.1, member, closed⟩
  · simp only [fallback, ReactiveApplication.Execution.observeEnvironment, phaseApplication,
      PhaseRuntimeState.publicView, head, Option.map_some, sample] at fallbackEq
    split at fallbackEq <;> cases fallbackEq

end Vegas.EventGraphRuntime.PhaseSeedCalendar
