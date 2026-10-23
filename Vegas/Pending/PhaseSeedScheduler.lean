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

def select (view : (app).EnvironmentView) (priority : Nat) : Option (PhaseSeedAddress graph) :=
  (eligible runtime leaks view).toList[priority]?.or (eligible runtime leaks view).toList.head?

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

end PhaseSeedScheduler
end Vegas.EventGraphRuntime
