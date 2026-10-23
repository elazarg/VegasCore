/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveService

/-! # Watcher observation rounds and packets outside the current public event

A watcher's service round activates it and then idles the round's network
slot: the service includes nothing on the watcher's behalf
(`Vegas.EventGraphRuntime.idleNetwork`).

A barrier-ordered graph has at most one ready public event, so while it stays
ready the handler rejects every differently addressed packet.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A network slot in which nothing is included. -/
def idleNetwork (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    runtime.NetworkPolicy leaks := fun _ _ => PMF.pure .wait

theorem idleNetwork_instruction (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (history : List (runtime.reactiveApplication leaks).EnvironmentEntry)
    (view : (runtime.reactiveApplication leaks).EnvironmentView) :
    runtime.interactionInstruction leaks (runtime.idleNetwork leaks) history view .wire =
      PMF.pure .wait := by
  simp [interactionInstruction, idleNetwork, NetworkChoice.command,
    ReactiveApplication.atMostOnceCommand, PMF.pure_map]

end Vegas.EventGraphRuntime
