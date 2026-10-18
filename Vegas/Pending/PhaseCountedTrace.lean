/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseCountCollection
import Interaction.ReactiveRecordedMenuTrace
import Interaction.ReactiveRecordedResponseAfter

/-! # Clean signed inputs recover an actual counted prehistory -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

/-- No forbidden recorded response can precede a clean endpoint, since its
signed envelope and forbidden verdict persist along every raw continuation. -/
theorem onePacketMenu_trace_of_countClean
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (current : (phaseApplication runtime leaks).Control)
    (trace : ((rawMenu runtime leaks bounds).protocol initial horizon scheduler).Trace
      (some current)) (clean : CountClean runtime leaks current.execution) :
    Nonempty (((onePacketMenu runtime leaks bounds).protocol initial horizon scheduler).Trace
      (some current)) := by
  classical
  let app := phaseApplication runtime leaks
  apply (onePacketMenu runtime leaks bounds).trace_of_recorded_actions
    (silence_onePacket runtime leaks bounds) initial horizon scheduler current
      ((rawMenu runtime leaks bounds).toRawTrace initial horizon scheduler trace)
  intro owner earlier entry later recalled
  obtain ⟨remaining, execution, prior, postTrace, kept, past, viewed, allowed,
      _before, _length⟩ :=
    (rawMenu runtime leaks bounds).recorded_response_after initial horizon scheduler
      current trace owner earlier entry later recalled
  change entry.action ∈ onePacketActions runtime leaks bounds owner earlier entry.beforeView
  rw [mem_onePacketActions]
  refine ⟨?_, ?_⟩
  · rwa [past, ← viewed] at allowed
  cases sent : entry.action.transmission with
  | none => exact Or.inl rfl
  | some material =>
      refine Or.inr ⟨material, sent, ?_⟩
      by_contra rejected
      have forbidden : permits (app.outputs earlier)
          (localEnvelope runtime leaks owner earlier entry.beforeView material) = false :=
        Bool.eq_false_of_not_eq_true rejected
      have actionEq : entry.action = ⟨some material⟩ := by
        have eta : entry.action = ⟨entry.action.transmission⟩ := by
          cases entry.action
          rfl
        exact eta.trans (congrArg ReactiveApplication.Action.mk sent)
      have countRecall := countRecall_history runtime leaks
        ((rawMenu runtime leaks bounds).toRawTrace initial horizon scheduler prior)
      have response := permits_respond runtime leaks execution countRecall owner material
      let message := localEnvelope runtime leaks owner earlier entry.beforeView material
      have emitted : message ∈ (execution.respond app owner entry.action).network.inputs := by
        rw [actionEq, response.1, past, ← viewed]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have verdict : permits (execution.respond app owner entry.action).network.inputs
          message = false := by
        rw [actionEq]
        change permits (execution.respond app owner ⟨some material⟩).network.inputs _ = false
        rw [show message = localEnvelope runtime leaks owner (execution.recall owner)
          (execution.observe app owner) material by rw [past, ← viewed]]
        rw [response.2.1, past, ← viewed]
        exact forbidden
      have retained := countForbidden_reaches
        ((rawMenu runtime leaks bounds).reaches_raw initial horizon scheduler kept.reachesWithin)
        ⟨remaining, none, execution.respond app owner entry.action⟩ current rfl rfl
          message emitted verdict
      have contradiction := clean.2 message retained.1
      rw [retained.2] at contradiction
      cases contradiction

end Vegas.EventGraphRuntime.PhaseCount
