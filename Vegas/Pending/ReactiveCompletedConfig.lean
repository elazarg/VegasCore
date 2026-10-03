/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveStateInvariant

/-! # Completed application configurations under arbitrary raw play

After every event is complete, no player packet or environment command can
change the typed graph configuration. Candidate registration, further traffic,
receipts, clock ticks and passive observation remain possible. This is a
configuration invariant, without an audit or payoff comparison premise.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Arbitrary responses and scheduler commands preserve a fully completed
configuration, while private candidate material and actual traffic can change. -/
theorem reactiveCompletedConfigInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (config : graph.Config) (complete : config.cut.completed = Finset.univ) :
    (runtime.reactiveApplication leaks).Invariant (fun state => state.config = config) := by
  have notReady (state : State graph) (same : state.config = config) (event : graph.EventId) :
      ¬state.config.cut.Ready event := by
    intro ready
    apply ready.1
    rw [same, complete]
    exact Finset.mem_univ _
  constructor
  · intro state who material same
    change (submitStep (material.call.register state who) who material.call.packet).config = config
    rw [submitStep_config, (material.call.register_facts who state).1]
    exact same
  · intro state message next same accepted
    obtain ⟨event, _named, ready, _action, _step⟩ := handle_config_mem_step runtime state next
      ⟨message.id, message.payload.call⟩ (reactiveHandle_call accepted)
    exact (notReady state same event ready).elim
  · intro state command next same moved
    change next ∈ (environmentStep runtime state command).support at moved
    cases command with
    | advanceClock =>
        change next ∈ (PMF.pure { state with clock := state.clock + 1 }).support at moved
        cases (PMF.mem_support_pure_iff _ _).mp moved
        exact same
    | executeSample event =>
        rw [environmentStep_executeSample_of_not_ready runtime state event
          (notReady state same event)] at moved
        cases (PMF.mem_support_pure_iff _ _).mp moved
        exact same
    | expire event =>
        rw [environmentStep_expire_of_not_ready runtime state event
          (notReady state same event)] at moved
        cases (PMF.mem_support_pure_iff _ _).mp moved
        exact same

end Vegas.EventGraphRuntime
