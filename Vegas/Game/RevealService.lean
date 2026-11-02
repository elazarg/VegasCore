/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphInputs
import Vegas.EventGraph.Sequential
import Vegas.Pending.ReactiveRuntime
import Vegas.Pending.EventPublicState
import Vegas.Source.ProtocolTermination

/-! # Compiled source service configurations

The constructors share the existing event graph and reactive application.
A dependency mode selects the graph order; a configured deadline counts from
an event's readiness. The default graph retains the total source order.
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

theorem eventCount_eq_instructionCount {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) : eventCount program = instructionCount program := by
  induction program with
  | ret payoffs => rfl
  | sample name fresh law next ih => exact congrArg Nat.succ ih
  | commit name owner fresh guard next ih => exact congrArg Nat.succ ih
  | reveal published owner name fresh source unresolved next ih => exact congrArg Nat.succ ih

end Vegas

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The compiled event graph under a dependency mode. -/
abbrev serviceGraph (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode) : EventGraph Player L :=
  setup.eventGraph.withMode mode

/-- The default service graph: the sequential specialization of the compiled
graph, which is its sequential mode. -/
abbrev graph (setup : Setup (Player := Player) (L := L)) := setup.eventGraph.sequentialize

/-- Under the public-barrier certificate, every compiler dependency mode has
the same total source order and the same complete event graph. -/
theorem serviceGraph_eq_sequential (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode) (ordered : (serviceGraph setup mode).BarrierOrdered) :
    serviceGraph setup mode = graph setup :=
  setup.eventGraph.sequentialize_withMode_eq_of_barrierOrdered mode ordered

/-- The service graph of every mode keeps the public-barrier dependencies except
possibly those between independent reveals. -/
theorem serviceGraph_revealRelaxedOrdered (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode) : (serviceGraph setup mode).RevealRelaxedOrdered :=
  setup.eventGraph.withMode_revealRelaxedOrdered (toEventGraph_barrierOrdered setup.program) mode

/-- The default roster deadline: an event may stay ready for its index plus one
clock ticks. -/
abbrev rankDeadline (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode) (event : (serviceGraph setup mode).EventId) : Nat :=
  event.val + 1

/-- The service runtime of a dependency mode with a configured deadline duration
per event. The runtime counts each duration from the clock at which the event
became ready (`EventGraphRuntime.State.WithinDeadline`). -/
abbrev serviceRuntime (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode)
    (deadline : (serviceGraph setup mode).EventId → Nat) :
    EventGraphRuntime (serviceGraph setup mode) where
  deadline := deadline

@[simp] theorem serviceRuntime_deadline (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode) (deadline : (serviceGraph setup mode).EventId → Nat) :
    (serviceRuntime setup mode deadline).deadline = deadline := rfl

/-- The default service runtime: the sequential graph with `rankDeadline`. -/
abbrev runtime (setup : Setup (Player := Player) (L := L)) : EventGraphRuntime (graph setup) :=
  serviceRuntime setup .sequential (rankDeadline setup .sequential)

/-- In the sequentialized graph a ready event is the only ready event, so each
player either has it as its turn or is idle. -/
theorem soleReady_of_ready (setup : Setup (Player := Player) (L := L))
    (state : EventGraphRuntime.State (graph setup)) {event : (graph setup).EventId}
    (ready : state.config.cut.Ready event) : state.publicView.SoleReady event :=
  ⟨(state.publicView_eventReady event).mpr ready, fun other otherReady =>
    setup.eventGraph.sequentialize_ready_unique state.config.cut
      ((state.publicView_eventReady other).mp otherReady) ready⟩

/-- In every dependency mode a ready event is its actor's turn: a player acts
at most at one ready event. -/
theorem serviceOwnTurn?_of_ready (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    (state : EventGraphRuntime.State (serviceGraph setup mode))
    {event : (serviceGraph setup mode).EventId}
    (ready : state.config.cut.Ready event) {who : Player}
    (owned : (serviceGraph setup mode).actor? event = some who) :
    state.publicView.ownTurn? who = some event :=
  state.publicView.ownTurn?_of_ownTurn who event
    ⟨(state.publicView_eventReady event).mpr ready, owned, fun other otherReady otherActor =>
      (serviceGraph_revealRelaxedOrdered setup mode).ready_actor_unique state.config.cut
          ready ((state.publicView_eventReady other).mp otherReady) owned otherActor⟩

/-- A ready event is its actor's turn. -/
theorem ownTurn?_of_ready (setup : Setup (Player := Player) (L := L))
    (state : EventGraphRuntime.State (graph setup)) {event : (graph setup).EventId}
    (ready : state.config.cut.Ready event) {who : Player}
    (owned : (graph setup).actor? event = some who) :
    state.publicView.ownTurn? who = some event :=
  serviceOwnTurn?_of_ready (mode := .sequential) setup state ready owned

section Configured

variable (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- The reactive application of the service runtime of a dependency mode and a
deadline configuration, under an observation rule for pending packets. -/
abbrev serviceApplication := (serviceRuntime setup mode deadline).reactiveApplication leaks

/-- The prior over initial values, compiled to initial states of the service
graph of a dependency mode. -/
def serviceInitialLaw : PMF (EventGraphRuntime.State (serviceGraph setup mode)) :=
  setup.initialLaw.map (fun initial => EventGraphRuntime.State.initial (setup.eventInputs initial))

/-- A finitely supported prior compiles to finitely many initial states. -/
theorem serviceInitialLaw_support_finite [setup.FiniteInitialLaw] :
    (serviceInitialLaw setup mode).support.Finite := by
  rw [serviceInitialLaw, PMF.support_map]
  exact setup.initialLaw_support_finite.image _

end Configured

variable (setup : Setup (Player := Player) (L := L))

/-- The sequential compiled application with its supplied runtime. -/
abbrev application (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))) :=
  runtime.reactiveApplication leaks

/-- The initial law of the default sequential graph. -/
abbrev initialLaw : PMF (EventGraphRuntime.State (graph setup)) :=
  serviceInitialLaw setup .sequential


end Vegas
