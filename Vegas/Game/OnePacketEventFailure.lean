/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketExclusionPayoff
import Vegas.Game.RevealServiceRosterContinuation
import Vegas.Pending.ReactiveAcceptedOutput

/-! # Event-level failure read through the typed readout

A field value of a binding or publication kind is a failure when it records a
failed result (`Vegas.EventGraph.EventField.IsFailure`). An event failed in a
graph store when its output field holds a failure
(`Vegas.StoreEventFailed`), and in a terminal source state when a cell of the
terminal context read from the event's output holds a failure
(`Vegas.EventCellFailed`). Reading a failure through any reference to the
event's output field is a failure of the event in the store
(`Vegas.storeEventFailed_of_ref`).

The event-level failed readouts of a player are those recording a failure of
the event together with a failed reveal of that player
(`Vegas.EventFailedReadout`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open EventGraphRuntime Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The event's output field holds a failure in the store. -/
def StoreEventFailed {graph : EventGraph Player L} (store : EventGraph.Store graph.layout)
    (event : graph.EventId) : Prop :=
  ∃ value, store (.inr event) = some value ∧ (graph.layout (.inr event)).IsFailure value

omit [DecidableEq Player] in
/-- Reading a failure through any reference to the event's output field is a
failure of the event in the store. -/
theorem storeEventFailed_of_ref {graph : EventGraph Player L}
    (store : EventGraph.Store graph.layout) (event : graph.EventId)
    {kind : EventGraph.EventField Player L} (ref : EventGraph.FieldRef graph.layout kind)
    (field : ref.field = .inr event) {value : kind.Value} (read : ref.get? store = some value)
    (failed : kind.IsFailure value) : StoreEventFailed store event := by
  rcases ref with ⟨refField, layoutEq⟩
  change refField = .inr event at field
  subst field
  subst layoutEq
  exact ⟨value, read, failed⟩

variable (setup : Setup (Player := Player) (L := L))

/-- A cell of the terminal context read from the event's output holds a
failure. -/
def EventCellFailed (event : (graph setup).EventId)
    (terminal : State L setup.program.terminalCtx) : Prop :=
  ∃ (name : VarId) (cell : CellTy Player L) (source : HasVar setup.program.terminalCtx name cell),
    ((terminalRefs setup.program).get source).field = .inr event ∧
      (cellField cell).IsFailure (cellValue (terminal.get source))

/-- **The event-level failed readouts.** Readouts recording a failure of the
event and a failed reveal of the player. -/
def EventFailedReadout (who : Player) (event : (graph setup).EventId) :
    Set (Option (State L setup.program.terminalCtx)) :=
  {readout | ∃ terminal, readout = some terminal ∧
    1 ≤ failedReveals setup.program who (publicOutcome setup.program terminal) ∧
    EventCellFailed setup event terminal}

variable (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

end Vegas
