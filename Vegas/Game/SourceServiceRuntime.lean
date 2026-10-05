/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.RevealSequence
import Vegas.Compile.EventGraphInputs
import Vegas.Compile.EventGraphPolicy
import Vegas.EventGraph.Sequential
import Vegas.Pending.ReactiveRevealBlock
import Vegas.Pending.ReactiveMonitoring
import Vegas.Pending.ReactiveFiniteResponses
import Interaction.ReactiveResponseMenu
import Interaction.ReactiveMenuRestriction

/-! # Sequential source service runtime
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem eventCount_eq_instructionCount {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) : eventCount program = instructionCount program := by
  induction program with
  | ret payoffs => rfl
  | sample name fresh law next ih => exact congrArg Nat.succ ih
  | commit name owner fresh guard next ih => exact congrArg Nat.succ ih
  | reveal published owner name fresh source unresolved next ih => exact congrArg Nat.succ ih

abbrev graph (setup : Setup (Player := Player) (L := L)) := setup.eventGraph.sequentialize

def runtime (setup : Setup (Player := Player) (L := L)) : EventGraphRuntime (graph setup) where
  deadline event := event.val + 1

theorem runtime_deadline_pos (setup : Setup (Player := Player) (L := L))
    (event : (graph setup).EventId) : 0 < (runtime setup).deadline event := Nat.zero_lt_succ _

/-- In the sequentialized graph a ready event is the only ready event, so each
player either has it as its turn or is idle. -/
theorem soleReady_of_ready (setup : Setup (Player := Player) (L := L))
    (state : EventGraphRuntime.State (graph setup)) {event : (graph setup).EventId}
    (ready : state.config.cut.Ready event) : state.publicView.SoleReady event :=
  ⟨(state.publicView_eventReady event).mpr ready, fun other otherReady =>
    setup.eventGraph.sequentialize_ready_unique state.config.cut
      ((state.publicView_eventReady other).mp otherReady) ready⟩

/-- A ready event is its actor's turn. -/
theorem ownTurn?_of_ready (setup : Setup (Player := Player) (L := L))
    (state : EventGraphRuntime.State (graph setup)) {event : (graph setup).EventId}
    (ready : state.config.cut.Ready event) {who : Player}
    (owned : (graph setup).actor? event = some who) :
    state.publicView.ownTurn? who = some event :=
  state.publicView.ownTurn?_of_ownTurn who event
    ((soleReady_of_ready setup state ready).ownTurn owned)

/-- While an event is ready, every player other than its actor is idle. -/
theorem idle_of_ready (setup : Setup (Player := Player) (L := L))
    (state : EventGraphRuntime.State (graph setup)) {event : (graph setup).EventId}
    (ready : state.config.cut.Ready event) {who : Player}
    (foreign : (graph setup).actor? event ≠ some who) : state.publicView.Idle who :=
  (soleReady_of_ready setup state ready).idle foreign

omit [DecidableEq Player] in
/-- Readiness is public: states with the same public view have the same ready
events. -/
theorem ready_of_publicView_eq {graph : EventGraph Player L}
    {first second : EventGraphRuntime.State graph}
    (same : first.publicView = second.publicView) {event : graph.EventId}
    (ready : second.config.cut.Ready event) : first.config.cut.Ready event := by
  rw [← State.publicView_eventReady, same, State.publicView_eventReady]
  exact ready

theorem runtime_deadline_increases (setup : Setup (Player := Player) (L := L))
    (first second : (graph setup).EventId) (before : first.val < second.val) :
    (runtime setup).deadline first < (runtime setup).deadline second := by
  change first.val + 1 < second.val + 1
  omega

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

abbrev application := (runtime setup).reactiveApplication leaks

def initialLaw : PMF (EventGraphRuntime.State (graph setup)) :=
  setup.initialLaw.map (fun initial => EventGraphRuntime.State.initial (setup.eventInputs initial))

end Vegas
