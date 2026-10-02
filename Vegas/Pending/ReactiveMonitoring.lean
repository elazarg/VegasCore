/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMonitoring
import Vegas.Pending.EventPublicBarrier
import Vegas.Pending.ReactiveRuntime
import Vegas.Pending.ReactiveServiceEvaluation

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

/-- The watcher's round is its activation followed by an idle slot. -/
theorem run_observation_plan (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy) (watcher : Player)
    (execution : (runtime.reactiveApplication leaks).Execution) :
    runtime.runInteractionPlan leaks players (runtime.idleNetwork leaks)
      [.player watcher, .wire] execution =
        (runtime.reactiveApplication leaks).observationRound players watcher execution := by
  have active : runtime.interactionStep leaks players (runtime.idleNetwork leaks)
      (.player watcher) execution =
        (runtime.reactiveApplication leaks).dispatch players (.activate watcher) execution := by
    simp only [interactionStep, interactionInstruction, PMF.pure_bind]
  rw [runInteractionPlan, active]
  simp only [runInteractionPlan, interactionStep, idleNetwork_instruction,
    PMF.pure_bind, PMF.bind_pure, ReactiveApplication.observationRound]

/-- Rejection depends on the current ready event, not merely the author.
This also covers premature packets for a later event owned by the same player. -/
theorem handle_eq_none_of_other_event_ready_public
    (runtime : EventGraphRuntime graph) (ordered : graph.BarrierOrdered)
    (state : State graph) (current : graph.EventId)
    (isPublic : (graph.outputLayout current).IsPublic)
    (ready : state.config.cut.Ready current)
    (message : Message Player (Payload graph))
    (other : Payload.event? graph message.payload ≠ some current) :
    runtime.handle state message = none := by
  cases accepted : runtime.handle state message with
  | none => rfl
  | some next =>
      obtain ⟨actual, addressed, actualReady, _, _⟩ :=
        runtime.handle_config_mem_step state next message accepted
      have same := ordered.ready_public_unique state.config.cut isPublic ready actualReady
      exact (other (addressed.trans (congrArg some same))).elim

end Vegas.EventGraphRuntime
