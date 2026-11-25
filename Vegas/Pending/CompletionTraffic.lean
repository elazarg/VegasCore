module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ConfigDrain
public import Vegas.Pending.EventCompletionStopping
public import Vegas.EventGraph.CompletionObservation
public import GameTheory.Math.Probability.ConditionalObservation

@[expose] public section

/-! # Traffic factors across graph checkpoints

At an automatic rank the native execution may already be ahead of the graph
checkpoint. Its traffic can be carried unchanged across the graph completion
while retaining the observation-local factorization.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- The same native traffic still factors through actual graph observation
after advancing an already-drained automatic checkpoint by one event. The
auxiliary traffic moves neither in time nor in content. -/
theorem automatic_checkpoint_traffic_factor {Traffic : Type*}
    (who : Player) (event : graph.EventId)
    (law : PMF ({config : graph.Config // (State.ofConfig config).AutomaticReady event} × Traffic))
    (traffic : graph.PlayerObservation who → PMF Traffic)
    (factor : law = (law.map Prod.fst).bind fun config =>
      (traffic (graph.playerObserve who config.val)).map fun extra => (config, extra)) :
    let advance := fun config : {config : graph.Config //
        (State.ofConfig config).AutomaticReady event} =>
      ((State.ofConfig config.val).completeAutomatic event config.property).config
    let next := law.map fun pair => (advance pair.1, pair.2)
    next = (next.map Prod.fst).bind fun config =>
      (traffic (beforeCompletion event (graph.playerObserve who config))).map fun extra =>
        (config, extra) := by
  intro advance next
  apply map_observation_factor law (fun config => graph.playerObserve who config.val) traffic
    factor advance (graph.playerObserve who) (beforeCompletion event)
  intro config
  obtain ⟨action, taken⟩ := (State.ofConfig config.val).completeAutomatic_step event config.property
  exact beforeCompletion_playerObserve_of_step who config.val event config.property.1 action
    (advance config) taken

/-- A solitary automatic checkpoint changes the graph rank while keeping
the full native execution. Its advanced graph configuration drains to the
same physical configuration, even if the ledger consumed several events. -/
theorem automatic_checkpoint_native_stutter
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : (reactiveApplication timeouts leaks).Scheduler)
    (players : Player → (reactiveApplication timeouts leaks).Policy)
    (horizon : Nat) (execution : (reactiveApplication timeouts leaks).Execution)
    (config : graph.Config) (aligned : execution.application.config = State.drainConfig config)
    (event : graph.EventId) (eligible : (State.ofConfig config).AutomaticReady event)
    (unique : ∀ other, config.cut.Ready other → other = event) :
    let next := ((State.ofConfig config).completeAutomatic event eligible).config
    (reactiveApplication timeouts leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution =
      PMF.pure execution ∧
    execution.application.config = State.drainConfig next := by
  obtain ⟨owner, owned, inactive⟩ := eligible.owned
  have completed : event ∈ execution.application.config.cut.completed := by
    rw [aligned]
    exact State.drainConfig_completed_of_defaulted config event eligible.1 unique owner owned
      inactive
  refine ⟨?_, ?_⟩
  · exact (reactiveApplication timeouts leaks).runUntil_of_stop scheduler players _ _ execution
      completed
  · rw [aligned, ← State.drain_config_eq ((State.ofConfig config).completeAutomatic event eligible)]
    change (State.ofConfig config).drain.config =
      ((State.ofConfig config).completeAutomatic event eligible).drain.config
    rw [State.drain_eq_completeAutomatic_of_unique _ event eligible unique]

end Vegas.EventGraphRuntime
