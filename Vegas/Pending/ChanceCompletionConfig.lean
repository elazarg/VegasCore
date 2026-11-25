module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ChanceContinuation
public import Vegas.Pending.ConfigDrain

@[expose] public section

/-! # Graph configuration at the first completion of a solitary chance event -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
    {graph : Vegas.EventGraph Player L}

/-- The first completed sampling boundary has precisely the graph-step configuration
distribution followed by deterministic automatic completion. -/
theorem chance_completed_config_law
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (serial : graph.ActorSerial)
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (event : graph.EventId) (ownerless : graph.actor? event = none)
    (solitary : graph.Solitary event) (count : Nat)
    (before : ((reactiveApplication timeouts) leaks).Execution)
    (ready : before.application.config.cut.Ready event)
    (completed : ∀ final ∈ (((reactiveApplication timeouts) leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count before).support,
      event ∈ final.application.config.cut.completed) :
    (((reactiveApplication timeouts) leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count before).map
        (fun final => final.application.config) =
      (before.application.config.step event ready
        (EventCode.actionOfActorNone (graph.nodes event) ownerless)).map State.drainConfig := by
  let action := EventCode.actionOfActorNone (graph.nodes event) ownerless
  let recover := fun output : Option (graph.outputLayout event).Value =>
    output.elim before.application.config (fun value =>
      State.drainConfig (before.application.config.complete event ready action value))
  have raw := chance_completed_output_law timeouts leaks serial scheduler players event ownerless
    solitary count before ready completed
  have projected := congrArg (PMF.map recover) raw
  simp only [PMF.map_comp] at projected
  refine Eq.trans (map_congr_on_support _ ?_) (projected.trans (map_congr_on_support _ ?_))
  · intro after reached
    have clear (other : graph.EventId) (eligible : before.application.AutomaticReady other) :
        False := by
      obtain rfl := solitary _ eligible.1 ready
      obtain ⟨owner, acting, _⟩ := eligible.owned
      rw [ownerless] at acting
      contradiction
    obtain ⟨choice, native, primary, drained⟩ := runUntil_completed_primary_drain timeouts leaks
      scheduler players event count before after ready (fun _ other => solitary _ other ready)
      clear reached (completed after reached)
    obtain rfl := (graph.nodes event).action_eq_of_actor_none ownerless action choice
    rw [Config.step, PMF.support_map] at primary
    obtain ⟨value, _, applied⟩ := primary
    have stored : native.config.store (.inr event) = some value := by
      rw [← applied]
      exact Config.complete_output_same ..
    have finalStored := Config.Step.path_store_of_some native.drain_graph_steps _ _ stored
    change _ = recover (after.application.config.outputs event)
    rw [drained]
    change _ = recover (native.drain.config.store (.inr event))
    rw [finalStored, native.drain_config_eq, ← applied]
    rfl
  · intro next reached
    rw [Config.step, PMF.support_map] at reached
    obtain ⟨value, _, rfl⟩ := reached
    change recover ((before.application.config.complete event ready action value).outputs event) = _
    rw [Config.complete_output_same]
    rfl

end Vegas.EventGraphRuntime
