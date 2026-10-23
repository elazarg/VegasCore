/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCountVerdict
import Vegas.Pending.ReactiveOnePacketMenu
import Vegas.Pending.ReactiveSignedCommitments
import Interaction.ReactiveTrafficIdentity
import Vegas.Pending.ReactiveEventStability
import Interaction.ReactiveOwnerSelection

/-! # Pending authentic packets at unfinished timely events -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem countCallCorrect_owned_event
    (earlier : Message Player (WitnessedPacket graph) → Prop)
    (message : Message Player (WitnessedPacket graph))
    (correct : CountCallCorrect earlier message) {event : graph.EventId}
    (named : message.payload.call.event? graph = some event) :
    graph.actor? event = some message.sender := by
  unfold CountCallCorrect at correct
  cases call : message.payload.call with
  | malformed raw => rw [call] at named; cases named
  | commitment named' handle =>
      rw [call] at named correct
      cases named
      have owned := correct.1
      unfold bindingOwnedBy at owned
      cases view : nodeView graph event with
      | bind owner payload outputEq codeEq =>
          rw [outputEq] at owned
          have same : owner = message.sender := of_decide_eq_true owned
          rw [← same]
          exact graph.actor?_of_outputLayout_binding outputEq
      | resolve owner payload binding checks outputEq codeEq =>
          rw [outputEq] at owned
          cases owned
      | sample payload law outputEq codeEq =>
          rw [outputEq] at owned
          cases owned
  | opening named' handle raw =>
      rw [call] at named correct
      cases named
      obtain ⟨_, owned⟩ := correct
      cases view : nodeView graph event with
      | resolve owner payload binding checks outputEq codeEq =>
          rw [view] at owned
          rw [owned.1]
          exact (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
            (congrArg EventCode.actor codeEq)
      | bind _ _ _ _ => rw [view] at owned; exact owned.elim
      | sample _ _ _ _ => rw [view] at owned; exact owned.elim

private def CountedSurvivors (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ∀ message ∈ execution.network.inputs, ∀ event,
    message.payload.call.event? graph = some event →
    execution.application.publicView.missedBindingBy message.sender = false →
    event ∉ execution.application.config.cut.completed →
    execution.application.WithinDeadline runtime event → message ∈ execution.network.pending

private theorem countedSurvivors_respond
    (execution : (runtime.reactiveApplication leaks).Execution)
    (valid : CountedSurvivors runtime leaks execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action) :
    CountedSurvivors runtime leaks
      (execution.respond (runtime.reactiveApplication leaks) who action) := by
  intro message member event named unmissed unfinished timely
  have same := runtime.reactive_respond_application leaks execution who action
  have unmissedBefore : execution.application.publicView.missedBindingBy message.sender = false :=
    same.2 ▸ unmissed
  have unfinishedBefore : event ∉ execution.application.config.cut.completed :=
    same.1 ▸ unfinished
  have timelyBefore : execution.application.WithinDeadline runtime event := by
    unfold State.WithinDeadline at timely ⊢
    have clock := congrArg PublicView.clock same.2
    have active := congrArg PublicView.activatedAt same.2
    dsimp only [State.publicView] at clock active
    rwa [clock, active] at timely
  cases action with
  | mk transmission =>
      cases transmission with
      | none => exact valid message member event named unmissedBefore unfinishedBefore timelyBefore
      | some material =>
          change message ∈ execution.network.inputs ++ [_] at member
          rcases List.mem_append.mp member with old | latest
          · exact (runtime.reactiveApplication leaks).respond_pending_mono execution who
              ⟨some material⟩ (valid message old event named unmissedBefore unfinishedBefore
                timelyBefore)
          · change message ∈ execution.network.pending ++ [_]
            exact List.mem_append_right _ latest

variable [Fintype Player]

end Vegas.EventGraphRuntime
