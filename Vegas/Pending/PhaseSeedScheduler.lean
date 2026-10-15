/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedBudget
import Vegas.Pending.PhaseNamespace
import Interaction.ReactiveAddressedScheduler

/-! # Actual ready-only local seed requests across phase attempts

The fixed finite address space contains every genuine request. The scheduler
selects only currently ready, owned, nonexcluded events. Local replies see the
readiness-relative clock and the full clocked own-activation/emission word for
that exact attempt, while the original execution retains all retired recall.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

abbrev PhaseSeedAddress (graph : Vegas.EventGraph Player L) :=
  BoundedAttemptEvent graph (Fintype.card Player)

/-- Full local input includes emission times, rather than only a current packet
prefix. It supports arbitrary timing and handle choices based on own history. -/
structure PhaseSeedInput (graph : Vegas.EventGraph Player L) where
  elapsed : Nat
  activationClocks : List Nat
  emissions : List (Nat × Message Player (CommitAttemptPacket graph))

/-- A seed can activate its owner, include one of its own emitted packets, expire
its own event, or wait. It cannot name another event or another owner's packet. -/
inductive PhaseSeedDecision where
  | activation
  | inclusion (index : Nat)
  | expiry
  | wait
  deriving DecidableEq

namespace PhaseSeedScheduler


def elapsed (coordinate : CommitAttemptEvent graph) (view : (app).EnvironmentView) : Nat :=
  view.application.native.clock -
    (view.application.native.activatedAt coordinate.event).getD view.application.native.clock

def ownPacket (coordinate : CommitAttemptEvent graph) (owner : Player)
    (message : Message Player (CommitAttemptPacket graph)) : Bool :=
  decide (message.sender = owner ∧ message.payload.attempt = coordinate.attempt ∧
    message.payload.packet.call.event? graph = some coordinate.event)

open Classical in
/-- Successive public inputs reveal exactly the envelopes emitted between two
scheduler commands. The local word discards all foreign interleavings. -/
def localInput (coordinate : CommitAttemptEvent graph) (owner : Player)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView) : PhaseSeedInput graph :=
  let adjacent := past.zip (past.tail.map (·.beforeView) ++ [view])
  let callbacks := adjacent.filter fun pair =>
    pair.1.command = .activate owner ∧
      PhaseRuntimeState.requests pair.1.beforeView.application owner coordinate
  { elapsed := elapsed runtime leaks coordinate view
    activationClocks := callbacks.map fun pair => elapsed runtime leaks coordinate pair.1.beforeView
    emissions := callbacks.flatMap fun pair =>
      ((pair.2.network.inputs.drop pair.1.beforeView.network.inputs.length).filter
        (ownPacket coordinate owner)).map
          (Prod.mk (elapsed runtime leaks coordinate pair.1.beforeView)) }

open Classical in
def eligible (view : (app).EnvironmentView) : Finset (PhaseSeedAddress graph) :=
  Finset.univ.filter fun coordinate =>
    ∃ owner, PhaseRuntimeState.requests view.application owner coordinate.1

@[simp]
theorem mem_eligible (view : (app).EnvironmentView) (coordinate : PhaseSeedAddress graph) :
    coordinate ∈ eligible runtime leaks view ↔
      ∃ owner, PhaseRuntimeState.requests view.application owner coordinate.1 := by
  simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]

def select (view : (app).EnvironmentView) (priority : Nat) : Option (PhaseSeedAddress graph) :=
  (eligible runtime leaks view).toList[priority]?.or (eligible runtime leaks view).toList.head?

theorem select_mem {view : (app).EnvironmentView} {priority : Nat}
    {coordinate : PhaseSeedAddress graph}
    (selected : select runtime leaks view priority = some coordinate) :
    coordinate ∈ eligible runtime leaks view := by
  unfold select at selected
  cases indexed : (eligible runtime leaks view).toList[priority]? with
  | none =>
      simp only [indexed, Option.none_or] at selected
      exact Finset.mem_toList.mp (List.mem_of_mem_head? selected)
  | some value =>
      simp only [indexed, Option.some_or, Option.some.injEq] at selected
      subst value
      exact Finset.mem_toList.mp (List.mem_of_getElem? indexed)

/-- Actual native metadata turns the public selector into a genuine ready request. -/
theorem select_sound {execution : (app).Execution} {inputs : graph.Inputs}
    (valid : execution.application.Invariant inputs) {priority : Nat}
    {coordinate : PhaseSeedAddress graph}
    (selected : select runtime leaks (execution.observeEnvironment app) priority =
      some coordinate) :
    ∃ owner, execution.application.SeedRequest owner coordinate.1 := by
  obtain ⟨owner, requested⟩ := (mem_eligible runtime leaks _ _).mp
    (select_mem runtime leaks selected)
  exact ⟨owner, (PhaseRuntimeState.requests_publicView _ valid _ _).mp requested⟩

/-- Every genuine seed request occurs in the selector's fixed finite roster. -/
theorem request_covered {execution : (app).Execution} {inputs : graph.Inputs}
    (valid : execution.application.Invariant inputs) (budget : execution.application.SeedBudget)
    {owner : Player} {coordinate : CommitAttemptEvent graph}
    (request : execution.application.SeedRequest owner coordinate) :
    request.coordinate budget ∈ eligible runtime leaks (execution.observeEnvironment app) := by
  apply (mem_eligible runtime leaks _ _).mpr
  exact ⟨owner, (PhaseRuntimeState.requests_publicView _ valid _ _).mpr request⟩

def reply (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedInput graph →
    PhaseSeedDecision) (coordinate : PhaseSeedAddress graph) (seed : LocalSeed)
    (input : PhaseSeedInput graph) : (app).Command :=
  match decideLocal coordinate seed input with
  | .activation => (graph.actor? coordinate.1.event).map
      (fun owner => (.activate owner : (app).Command)) |>.getD .wait
  | .inclusion index => (input.emissions[index]?).map
      (fun emission => (.include emission.2.id : (app).Command)) |>.getD .wait
  | .expiry => .application (.expire coordinate.1.event)
  | .wait => .wait

/-- Selection reads only remainder randomness and actual public history. Local
seed values enter the actual scheduler only through the guarded local reply. -/
def controller
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (fallback : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → (app).Command)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedInput graph → PhaseSeedDecision) :
    (app).AddressedScheduler (PhaseSeedAddress graph) LocalSeed RestSeed
      (PhaseSeedInput graph) where
  request rest past view := (select runtime leaks view (priority rest past view)).bind
    fun coordinate => (graph.actor? coordinate.1.event).map fun owner =>
      (coordinate, localInput runtime leaks coordinate.1 owner past view)
  fallback := fallback
  reply := reply runtime leaks decideLocal

/-- A coordinate belonging to any other attempt is never requested, regardless
of the remainder's priority or the values of any local seed. -/
theorem request_ne_of_namespace
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (fallback : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → (app).Command)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedInput graph → PhaseSeedDecision)
    (selected : PhaseSeedAddress graph) (past : List (app).EnvironmentEntry)
    (view : (app).EnvironmentView) (different : selected.1.attempt ≠ view.application.attempt)
    (rest : RestSeed) :
    ((controller runtime leaks priority fallback decideLocal).request rest past view).map Prod.fst ≠
      some selected := by
  intro requested
  cases selectedCoordinate : select runtime leaks view (priority rest past view) with
  | none =>
      simp only [controller, selectedCoordinate, Option.bind_none, Option.map_none] at requested
      cases requested
  | some coordinate =>
      cases acting : graph.actor? coordinate.1.event with
      | none =>
          simp only [controller, selectedCoordinate, Option.bind_some, acting,
            Option.map_none] at requested
          cases requested
      | some owner =>
          have same : coordinate = selected := by
            simpa only [controller, selectedCoordinate, Option.bind_some, acting,
              Option.map_some, Option.some.injEq] using requested
          subst coordinate
          obtain ⟨owner, ready⟩ := (mem_eligible runtime leaks _ _).mp
            (select_mem runtime leaks selectedCoordinate)
          exact different ready.1

end PhaseSeedScheduler
end Vegas.EventGraphRuntime
