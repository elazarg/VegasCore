/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCountVerdict
import Vegas.Pending.ReactiveEventStability

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

variable [Fintype Player]

end Vegas.EventGraphRuntime
