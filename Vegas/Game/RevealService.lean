module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphInputs
public import Vegas.EventGraph.Sequential
public import Vegas.Pending.ReactiveRuntime
public import Vegas.Pending.EventPublicState
public import Vegas.Source.ProtocolTermination

@[expose] public section

/-! # Compiled source service configurations

The constructors share the existing event graph and reactive application.
A dependency choice selects the graph order; a configured deadline counts from
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

/-- The compiled event graph under a dependency choice. -/
abbrev serviceGraph (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies) : EventGraph Player L :=
  setup.dataflowGraph.withDependencies deps

/-- The default roster timeout: an event may stay ready for its index plus one
clock ticks. -/
abbrev rankDuration (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies)
    (event : (serviceGraph setup deps).EventId) : Nat :=
  event.val + 1

/-- Timeout durations for the service graph of a dependency choice. Each duration
is counted from the clock at which the event became ready
(`EventGraphRuntime.State.WithinDeadline`). -/
abbrev serviceTimeouts (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat) :
    EventTimeouts (serviceGraph setup deps) where
  duration := duration

@[simp] theorem serviceTimeouts_duration (setup : Setup (Player := Player) (L := L))
    (deps : setup.dataflowGraph.Dependencies)
    (duration : (serviceGraph setup deps).EventId → Nat) :
    (serviceTimeouts setup deps duration).duration = duration := rfl

/-- The default service timeout durations: the sequential graph with `rankDuration`. -/
abbrev timeouts (setup : Setup (Player := Player) (L := L)) :
    EventTimeouts setup.informationGraph :=
  serviceTimeouts setup setup.informationDependencies
    (rankDuration setup setup.informationDependencies)

/-- In the sequentialized graph a ready event is the only ready event, so each
player either has it as its turn or is idle. -/
theorem soleReady_of_ready (setup : Setup (Player := Player) (L := L))
    (state : EventGraphRuntime.State setup.informationGraph)
    {event : setup.informationGraph.EventId}
    (ready : state.config.cut.Ready event) : state.publicView.SoleReady event :=
  ⟨(state.publicView_eventReady event).mpr ready, fun other otherReady =>
    setup.informationGraph.sequentialize_ready_unique state.config.cut
      ((state.publicView_eventReady other).mp otherReady) ready⟩

/-- A ready event is its actor's turn. -/
theorem ownTurn?_of_ready (setup : Setup (Player := Player) (L := L))
    (state : EventGraphRuntime.State setup.informationGraph)
    {event : setup.informationGraph.EventId}
    (ready : state.config.cut.Ready event) {who : Player}
    (owned : setup.informationGraph.actor? event = some who) :
    state.publicView.ownTurn? who = some event :=
  state.publicView.ownTurn?_of_ownTurn who event
    ((soleReady_of_ready setup state ready).ownTurn owned)

section Configured

variable (setup : Setup (Player := Player) (L := L))
  (deps : setup.dataflowGraph.Dependencies)
  (duration : (serviceGraph setup deps).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player
    (WitnessedPacket (serviceGraph setup deps)))

/-- The reactive application of a service graph and its timeout durations,
under an observation rule for pending packets. -/
abbrev serviceApplication :=
  (reactiveApplication (serviceTimeouts setup deps duration)) leaks

/-- The prior over initial values, compiled to initial states of the service
graph of a dependency choice. -/
def serviceInitialLaw : PMF (EventGraphRuntime.State (serviceGraph setup deps)) :=
  setup.initialLaw.map (fun initial => EventGraphRuntime.State.initial (setup.eventInputs initial))

/-- A finitely supported prior compiles to finitely many initial states. -/
theorem serviceInitialLaw_support_finite [setup.FiniteInitialLaw] :
    (serviceInitialLaw setup deps).support.Finite := by
  rw [serviceInitialLaw, PMF.support_map]
  exact setup.initialLaw_support_finite.image _

end Configured

variable (setup : Setup (Player := Player) (L := L))

/-- The sequential compiled application with its supplied timeout durations. -/
abbrev application (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)) :=
  (reactiveApplication timeouts) leaks

/-- The initial law of the default sequential graph. -/
abbrev initialLaw : PMF (EventGraphRuntime.State setup.informationGraph) :=
  serviceInitialLaw setup setup.informationDependencies


end Vegas
