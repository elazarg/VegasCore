module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.CompletionObservation
public import Vegas.EventGraph.PrefixConfiguration
public import Vegas.Pending.OwnedCompletionConfig
public import GameTheoryExtensions.Math.Probability.ObservedChoice

@[expose] public section

/-! # Native traffic conditional on the focal graph successor -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
    {graph : Vegas.EventGraph Player L}

/-- At an active focal event the next traffic law depends only on the focal
observation of the primary graph successor. Automatic service can carry the
native configuration beyond this primary one. The displayed pair retains the
entire stopped native configuration together with its actual traffic. -/
theorem focal_owned_successor_traffic_factor
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (bound : graph.EventId → Nat) (turns : Nat) (timing : EventGraphRuntime.TurnTiming graph turns)
    (reference : graph.BehavioralProfile)
    (focal : Player) (deviation : ((reactiveApplication timeouts) leaks).Policy)
    (event : graph.EventId) (owned : graph.actor? event = some focal)
    (solitary : graph.Solitary event) (horizon : Nat)
    {Seed : Type*} (prior : PMF Seed)
    (execution : Seed → ((reactiveApplication timeouts) leaks).Execution) :
    let app := (reactiveApplication timeouts) leaks
    let config := fun seed => (execution seed).application.config
    let traffic := (bindingTraffic timeouts) leaks focal
    let observe := graph.playerObserve focal
    let players := Function.update (turnPolicy timeouts leaks bound turns timing reference)
      focal deviation
    let phase := fun seed => app.runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
    ∀ (noise : graph.PlayerObservation focal → PMF _),
      prior.map (fun seed => (config seed, traffic (execution seed))) =
        (prior.map config).bind (fun before =>
          (noise (observe before)).map fun extra => (before, extra)) →
      (∀ seed ∈ prior.support, (config seed).cut.Ready event) →
      (∀ seed ∈ prior.support, focal ∉ (config seed).defaulted) →
      (∀ seed ∈ prior.support, ∀ final ∈ (phase seed).support,
        event ∈ final.application.config.cut.completed) →
      ∃ law : graph.PlayerObservation focal → PMF (graph.Action event),
      ∃ nextNoise : graph.PlayerObservation focal → PMF (BindingTraffic timeouts leaks),
        (prior.bind fun seed => (phase seed).map fun final =>
          (final.application.config, traffic final)) =
        prior.bind fun seed =>
          if ready : (config seed).cut.Ready event then
            (law (observe (config seed))).bind fun action =>
              ((config seed).step event ready action).bind fun primary =>
                (nextNoise (observe primary)).map fun extra => (State.drainConfig primary, extra)
          else PMF.pure (config seed, traffic (execution seed)) := by
  intro app config traffic observe players phase noise factor ready active completed
  obtain ⟨channel, joint⟩ := focal_owned_completed_traffic_law timeouts leaks scheduler bound
    turns timing reference focal deviation event owned solitary horizon prior execution noise
    factor ready active completed
  let read := fun observation : graph.PlayerObservation focal =>
    (recalledAction event observation).getD ((graph.nodes event).failureAction focal owned)
  let pick := fun extra : BindingTraffic timeouts leaks =>
    (recalledAction event extra.2.2.2.2.1.observation).getD
      ((graph.nodes event).failureAction focal owned)
  let nextNoise := fun observation : graph.PlayerObservation focal =>
    fiberPosterior (channel (beforeCompletion event observation)) pick (read observation)
  refine ⟨fun observation => (channel observation).map pick, nextNoise, joint.trans ?_⟩
  apply bind_congr_on_support _
  intro seed supported
  have available := ready seed supported
  change (channel (observe (config seed))).bind _ = _
  simp only [config] at available
  simp only [config, dite_eq_left available]
  let before := (execution seed).application.config
  let observed := graph.playerObserve focal before
  let law := channel observed
  change (law.bind fun extra => (before.step event available (pick extra)).map fun target =>
    (State.drainConfig target, extra)) = (law.map pick).bind _
  conv_lhs => rw [← fiberPosterior_reconstruct law pick]
  rw [PMF.bind_bind]
  apply bind_congr_on_support _
  intro action possible
  obtain ⟨after, stepLaw⟩ := before.step_eq_pure_of_actor event available action focal owned
  have moved : after ∈ (before.step event available action).support := by
    rw [stepLaw, PMF.mem_support_pure_iff]
  have recovered := beforeCompletion_playerObserve_of_step focal before event available action
    after moved
  have remembers := recalledAction_of_step before event focal owned (active seed supported)
    available action after moved
  change ((fiberPosterior law pick action).bind _) =
    (before.step event available action).bind _
  rw [stepLaw, PMF.pure_bind]
  simp only [nextNoise, observe, recovered, read, remembers, Option.getD_some]
  rw [← PMF.bind_pure_comp]
  apply bind_congr_on_support _
  intro extra member
  have picked := (mem_support_fiberPosterior possible member).1
  rw [picked, stepLaw, PMF.pure_map]
  rfl

/-- Reading the next rank from the physical execution gives the primary graph
checkpoint jointly with the actual drained endpoint and all retained traffic. -/
theorem focal_owned_primary_traffic_factor
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (bound : graph.EventId → Nat) (turns : Nat) (timing : EventGraphRuntime.TurnTiming graph turns)
    (reference : graph.BehavioralProfile)
    (focal : Player) (deviation : ((reactiveApplication timeouts) leaks).Policy)
    (event : graph.EventId) (owned : graph.actor? event = some focal)
    (solitary : graph.Solitary event) (horizon : Nat)
    {Seed : Type*} (prior : PMF Seed)
    (execution : Seed → ((reactiveApplication timeouts) leaks).Execution)
    (ordered : ∀ seed ∈ prior.support,
      (execution seed).application.config.cut.IsPrefix event.val) :
    let app := (reactiveApplication timeouts) leaks
    let config := fun seed => (execution seed).application.config
    let traffic := (bindingTraffic timeouts) leaks focal
    let observe := graph.playerObserve focal
    let players := Function.update (turnPolicy timeouts leaks bound turns timing reference)
      focal deviation
    let phase := fun seed => app.runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)
    ∀ (noise : graph.PlayerObservation focal → PMF _),
      prior.map (fun seed => (config seed, traffic (execution seed))) =
        (prior.map config).bind (fun before =>
          (noise (observe before)).map fun extra => (before, extra)) →
      (∀ seed ∈ prior.support, (config seed).cut.Ready event) →
      (∀ seed ∈ prior.support, focal ∉ (config seed).defaulted) →
      (∀ seed ∈ prior.support, ∀ final ∈ (phase seed).support,
        event ∈ final.application.config.cut.completed) →
      ∃ law : graph.PlayerObservation focal → PMF (graph.Action event),
      ∃ nextNoise : graph.PlayerObservation focal → PMF (BindingTraffic timeouts leaks),
        (prior.bind fun seed => (phase seed).map fun final =>
          (Config.rankPrefix (event.val + 1) final.application.config,
            final.application.config, traffic final)) =
        prior.bind fun seed =>
          if ready : (config seed).cut.Ready event then
            (law (observe (config seed))).bind fun action =>
              ((config seed).step event ready action).bind fun primary =>
                (nextNoise (observe primary)).map fun extra =>
                  (primary, State.drainConfig primary, extra)
          else PMF.pure (config seed, config seed, traffic (execution seed)) := by
  intro app config traffic observe players phase noise factor ready active completed
  obtain ⟨law, nextNoise, joint⟩ := focal_owned_successor_traffic_factor timeouts leaks scheduler
    bound turns timing reference focal deviation event owned solitary horizon prior execution
    noise factor ready active completed
  let recover := fun pair : graph.Config × BindingTraffic timeouts leaks =>
    (Config.rankPrefix (event.val + 1) pair.1, pair)
  have lifted := congrArg (PMF.map recover) joint
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at lifted
  refine ⟨law, nextNoise, lifted.trans ?_⟩
  apply bind_congr_on_support _
  intro seed supported
  have available : (execution seed).application.config.cut.Ready event := ready seed supported
  simp only [config, dite_eq_left available, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro action _
  apply bind_congr_on_support _
  intro primary moved
  have atRank : primary.cut.IsPrefix (event.val + 1) := by
    rw [(execution seed).application.config.step_cut event available action primary moved]
    exact (ordered seed supported).complete_at event available rfl
  have restored := Config.rankPrefix_of_path atRank (State.ofConfig primary).drain_graph_steps
  change Config.rankPrefix (event.val + 1) (State.drainConfig primary) = primary at restored
  simp only [recover, restored, observe]

end Vegas.EventGraphRuntime
