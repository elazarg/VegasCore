/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveGraphSteps
import Vegas.Pending.ReactiveStateInvariant

/-! # Operational refinement of the message runtime

Every initialized raw history projects to a graph-reachable configuration.
Every subsequent protocol transition follows a finite supported graph path,
including automatic completions after public default. Application
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
      Relation.ReflTransGen EventGraph.Config.Step before.execution.application.config
        after.execution.application.config) ∧
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
    exact reactive_protocol_graph_steps runtime leaks (inputs.map State.initial)
      horizon scheduler before after joint supported
  · intro control trace
    obtain ⟨initial, supported, valid⟩ :=
      reactive_history_invariant runtime leaks inputs horizon scheduler trace
    refine ⟨⟨initial, supported, valid.reachable⟩, ?_⟩
    intro completes terminal
    have done := completes control trace terminal
    exact ⟨done, fun field => control.execution.application.config.store_available_of_terminal
      done field⟩

end Vegas.EventGraphRuntime
