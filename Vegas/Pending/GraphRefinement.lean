/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionNativeFailure
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.ReactiveAsyncContract

/-! # Operational refinement of the message runtime

Every initialized raw history projects to a graph-reachable configuration.
Every subsequent protocol transition either stutters or performs one graph
step, retaining its dependent action and exact chance-step support. Application
completion is conditional on the supplied service's completion guarantee.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Raw message execution refines graph execution at every initialized prefix
and every transition, independently of player policies and pending visibility.
The completion condition additionally makes every typed terminal field available. -/
theorem reactive_protocol_graph_refinement (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (∀ (before after : (runtime.reactiveApplication leaks).Control)
      (joint : Player → Option (runtime.reactiveApplication leaks).Action),
      some after ∈ ((runtime.reactiveApplication leaks).transition
        (inputs.map State.initial) horizon scheduler (some before) joint).support →
      after.execution.application.config = before.execution.application.config ∨
        ∃ event, ∃ (ready : before.execution.application.config.cut.Ready event)
          (action : graph.Action event),
          after.execution.application.config ∈
            (before.execution.application.config.step event ready action).support) ∧
    (∀ (control : (runtime.reactiveApplication leaks).Control)
      (_trace : ((runtime.reactiveApplication leaks).protocol
        (inputs.map State.initial) horizon scheduler).Trace (some control)),
      (∃ initial ∈ inputs.support, control.execution.application.config.Reachable initial) ∧
      (CompletesPlay runtime leaks (inputs.map State.initial) horizon scheduler →
        ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
          horizon scheduler).terminal (some control) →
        control.execution.application.config.cut.Terminal ∧
          ∀ field, (control.execution.application.config.store field).isSome = true)) := by
  constructor
  · intro before after joint supported
    have step := (reactiveApplication_completionStep runtime leaks).transition
      (inputs.map State.initial) horizon scheduler before after joint supported
    rcases step with same | ⟨event, ready, action, reached, _⟩
    · exact Or.inl same.1
    · exact Or.inr ⟨event, ready, action, reached⟩
  · intro control trace
    obtain ⟨initial, supported, valid⟩ :=
      reactive_history_invariant runtime leaks inputs horizon scheduler trace
    refine ⟨⟨initial, supported, valid.reachable⟩, ?_⟩
    intro completes terminal
    have done := completes control trace terminal
    exact ⟨done, fun field => control.execution.application.config.store_available_of_terminal
      done field⟩

end Vegas.EventGraphRuntime
