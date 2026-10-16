/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedCalendar
import Vegas.Pending.PhaseSeedHistoryInput

/-! # Phased service polling with arbitrary local seed decisions

The original addressed scheduler polls ready coordinates using the existing
closed-tick book. Its local decision reads the complete erased own word, with
no restriction to a first-delay law or one activation per tick. This interface
does not itself assert successful resolution or recover negative queries.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- An event's seed selects only its owner's activation, an emitted envelope
of this event, its expiry, or silence. Packet values are absent from the input. -/
def reply
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (coordinate : PhaseSeedAddress graph) (seed : LocalSeed)
    (input : PhaseSeedOperationalInput graph) : (app).Command :=
  match decideLocal coordinate seed input with
  | .activation => (graph.actor? coordinate.1.event).map
      (fun owner => (.activate owner : (app).Command)) |>.getD .wait
  | .inclusion index => (input.emissions[index]?).map
      (fun emission => (.include emission.identifier : (app).Command)) |>.getD .wait
  | .expiry => .application (.expire coordinate.1.event)
  | .wait => .wait

/-- Every ready coordinate is polled before the clock advances. Repeated local
activations remain possible until a nonactivation closes this coordinate's tick.
All execution and seed conditioning use the existing addressed scheduler. -/
def controller
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision) :
    (app).AddressedScheduler (PhaseSeedAddress graph) LocalSeed RestSeed
      (PhaseSeedOperationalInput graph) where
  request rest past view :=
    (PhaseSeedCalendar.selectOpen runtime leaks
      (PhaseSeedCalendar.replayClosed runtime leaks priority rest past) view
        (priority rest past view)).bind fun coordinate =>
      (graph.actor? coordinate.1.event).map fun owner =>
        (coordinate, PhaseSeedInput.operational coordinate.1.attempt
          (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner past view))
  fallback _ _ view := PhaseSeedCalendar.fallback runtime leaks view
  reply := reply runtime leaks decideLocal

/-- The concrete delay-and-coin calendar is the same controller instantiated
with its original local decision, including its original seed carrier. -/
theorem controller_calendar (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat) :
    controller runtime leaks priority (PhaseSeedCalendar.decision runtime delay bound) =
      PhaseSeedCalendar.controller runtime leaks delay bound priority := rfl

/-- Every actual request is for a ready owned event in the current physical
attempt. The conclusion is derived from native metadata, without a seed premise. -/
theorem request_sound
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (rest : RestSeed) (execution : (app).Execution) {inputs : graph.Inputs}
    (valid : execution.application.Invariant inputs) {coordinate : PhaseSeedAddress graph}
    {query : PhaseSeedOperationalInput graph}
    (requested : (controller runtime leaks priority decideLocal).request rest
      execution.environmentRecall (execution.observeEnvironment app) = some (coordinate, query)) :
    ∃ owner, execution.application.SeedRequest owner coordinate.1 := by
  exact PhaseSeedCalendar.request_sound runtime leaks (fun _ => 0) (fun _ => 0)
    priority rest execution valid requested

/-- A selected request contains the actual full local operational word. -/
theorem request_query
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (rest : RestSeed) (execution : (app).Execution) (coordinate : PhaseSeedAddress graph)
    (owner : Player) (actor : graph.actor? coordinate.1.event = some owner)
    (query : PhaseSeedOperationalInput graph)
    (requested : (controller runtime leaks priority decideLocal).request rest
      execution.environmentRecall (execution.observeEnvironment app) = some (coordinate, query)) :
    query = PhaseSeedInput.operational coordinate.1.attempt
      (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner
        execution.environmentRecall (execution.observeEnvironment app)) := by
  unfold controller at requested
  cases selected : PhaseSeedCalendar.selectOpen runtime leaks
      (PhaseSeedCalendar.replayClosed runtime leaks priority rest execution.environmentRecall)
      (execution.observeEnvironment app)
      (priority rest execution.environmentRecall (execution.observeEnvironment app)) with
  | none => simp only [selected, Option.bind_none, reduceCtorEq] at requested
  | some chosen =>
      cases acting : graph.actor? chosen.1.event with
      | none => simp only [selected, Option.bind_some, acting, Option.map_none, reduceCtorEq]
          at requested
      | some principal =>
          have pair := Option.some.inj (by
            simpa only [selected, Option.bind_some, acting, Option.map_some] using requested)
          have same : chosen = coordinate := (Prod.mk.inj pair).1
          subst chosen
          have ownerEq : principal = owner := Option.some.inj (acting.symm.trans actor)
          subst principal
          exact (Prod.mk.inj pair).2.symm

/-- Only an activation decision can emit an activation command, and its actor
is the owner of the queried coordinate, independently of the seed distribution. -/
theorem activation_owner
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (coordinate : PhaseSeedAddress graph) (seed : LocalSeed)
    (input : PhaseSeedOperationalInput graph) (owner expected : Player)
    (actor : graph.actor? coordinate.1.event = some expected)
    (activated : reply runtime leaks decideLocal coordinate seed input = .activate owner) :
    owner = expected := by
  unfold reply at activated
  cases chosen : decideLocal coordinate seed input with
  | activation =>
      simpa only [chosen, actor, Option.map_some, Option.getD_some,
        ReactiveApplication.Command.activate.injEq, eq_comm] using activated
  | inclusion index =>
      cases emitted : input.emissions[index]? <;> simp [chosen, emitted] at activated
  | expiry => simp only [chosen] at activated; cases activated
  | wait => simp only [chosen] at activated; cases activated

end Vegas.EventGraphRuntime.PhaseServiceScheduler
