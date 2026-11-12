module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveGraphSteps
public import Vegas.Pending.ReactiveStateInvariant

@[expose] public section

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
theorem reactive_protocol_graph_refinement (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler) :
    (∀ (before after : ((reactiveApplication timeouts) leaks).Control)
      (joint : Player → Option ((reactiveApplication timeouts) leaks).Action),
      some after ∈ (((reactiveApplication timeouts) leaks).transition
        (inputs.map State.initial) horizon scheduler (some before) joint).support →
      Relation.ReflTransGen EventGraph.Config.Step before.execution.application.config
        after.execution.application.config) ∧
    (∀ (control : ((reactiveApplication timeouts) leaks).Control)
      (_trace : (((reactiveApplication timeouts) leaks).protocol
        (inputs.map State.initial) horizon scheduler).Trace (some control)),
      (∃ initial ∈ inputs.support, control.execution.application.config.Reachable initial) ∧
      (CompletesPlay timeouts leaks (inputs.map State.initial) horizon scheduler →
        (((reactiveApplication timeouts) leaks).protocol (inputs.map State.initial)
          horizon scheduler).terminal (some control) →
        control.execution.application.config.cut.Terminal ∧
          ∀ field, (control.execution.application.config.store field).isSome = true)) := by
  constructor
  · intro before after joint supported
    exact reactive_protocol_graph_steps timeouts leaks (inputs.map State.initial)
      horizon scheduler before after joint supported
  · intro control trace
    obtain ⟨initial, supported, valid⟩ :=
      reactive_history_invariant timeouts leaks inputs horizon scheduler trace
    refine ⟨⟨initial, supported, valid.reachable⟩, ?_⟩
    intro completes terminal
    have done := completes control trace terminal
    exact ⟨done, fun field => control.execution.application.config.store_available_of_terminal
      done field⟩

end Vegas.EventGraphRuntime
