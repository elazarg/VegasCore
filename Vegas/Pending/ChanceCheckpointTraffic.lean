module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ChancePhaseTraffic
public import Vegas.EventGraph.PrefixConfiguration
public import GameTheoryExtensions.Math.Probability.Support

@[expose] public section

/-! # Stopped chance traffic at a primary rank checkpoint -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => (reactiveApplication timeouts) leaks

/-- At a solitary chance head, the stopped rank checkpoint and the actual
traffic have the graph step law paired with observation-local traffic.
Additional automatic completions are removed by the rank readout. -/
theorem chance_checkpoint_traffic_factor
    (serial : graph.ActorSerial) (scheduler : (app).Scheduler)
    (bound : graph.EventId → Nat) (turns : Nat)
    (timing : EventGraphRuntime.TurnTiming graph turns)
    (reference : graph.BehavioralProfile) (focal : Player) (deviation : (app).Policy)
    (event : graph.EventId) (ownerless : graph.actor? event = none)
    (solitary : graph.Solitary event)
    (horizon : Nat) {Seed : Type*} (prior : PMF Seed) (execution : Seed → (app).Execution)
    (checkpoint : Seed → graph.Config) :
    let traffic := (bindingTraffic timeouts) leaks focal
    let observe := graph.playerObserve focal
    let players := Function.update (turnPolicy timeouts leaks bound turns timing reference)
      focal deviation
    let phase := fun seed => (app).runUntilHorizon scheduler players
      (fun current => event ∈ current.application.config.cut.completed) horizon (execution seed)
    let action := EventCode.actionOfActorNone (graph.nodes event) ownerless
    ∀ (noise : graph.PlayerObservation focal → PMF _),
      prior.map (fun seed => (checkpoint seed, traffic (execution seed))) =
        (prior.map checkpoint).bind (fun before =>
          (noise (observe before)).map fun extra => (before, extra)) →
      (∀ seed ∈ prior.support, (checkpoint seed).cut.IsPrefix event.val) →
      (∀ seed ∈ prior.support,
        (execution seed).application.config = State.drainConfig (checkpoint seed)) →
      (∀ seed ∈ prior.support, ∀ final ∈ (phase seed).support,
        event ∈ final.application.config.cut.completed) →
      ∃ nextNoise : graph.PlayerObservation focal → PMF _,
        (prior.bind phase).map (fun final =>
          (Config.rankPrefix (event.val + 1) final.application.config, traffic final)) =
          (prior.bind fun seed =>
            if ready : (checkpoint seed).cut.Ready event then
              (checkpoint seed).step event ready action
            else PMF.pure (checkpoint seed)).bind (fun next =>
                (nextNoise (observe next)).map fun extra => (next, extra)) := by
  classical
  intro traffic observe players phase action noise factor ordered aligned completed
  let supported := pmfToSubtype prior (P := fun seed => seed ∈ prior.support) (fun _ mem => mem)
  have bind_supported {Result : Type} (kernel : Seed → PMF Result) :
      (supported.bind fun seed => kernel seed.val) = prior.bind kernel := by
    rw [show (fun seed : prior.support => kernel seed.val) = kernel ∘ Subtype.val from rfl,
      ← PMF.bind_map, map_val_pmfToSubtype]
  have physical (seed : prior.support) : (execution seed).application.config = checkpoint seed :=
    (aligned seed seed.property).trans (State.drainConfig_of_quiescent (State.ofConfig
      (checkpoint seed)) fun other automatic => by
        obtain rfl := solitary _ automatic.1 ((ordered seed seed.property).ready event.isLt)
        obtain ⟨owner, owned, _⟩ := automatic.owned
        rw [ownerless] at owned
        cases owned)
  have ready (seed : prior.support) : (execution seed).application.config.cut.Ready event := by
    rw [physical seed]
    exact (ordered seed seed.property).ready event.isLt
  have liftedFactor :
      supported.map (fun seed : prior.support =>
        ((execution seed).application.config, traffic (execution seed))) =
        (supported.map fun seed : prior.support => (execution seed).application.config).bind
          (fun before =>
          (noise (observe before)).map fun extra => (before, extra)) := by
    let before := fun seed : prior.support => (execution seed).application.config
    let reads := fun seed : prior.support => traffic (execution seed)
    change supported.map (fun seed => (before seed, reads seed)) =
      (supported.map before).bind _
    rw [map_congr_on_support _ (g := fun seed => (checkpoint seed.val, reads seed))
      (fun seed _ => congrArg (fun config => (config, reads seed)) (physical seed)),
      map_congr_on_support _ (g := fun seed => checkpoint seed.val)
        (fun seed _ => physical seed)]
    exact (map_pmfToSubtype prior (fun _ mem => mem)
      (fun seed => (checkpoint seed, traffic (execution seed)))).trans
        (factor.trans (congrArg (fun laws : PMF graph.Config =>
          laws.bind fun before => (noise (observe before)).map fun extra => (before, extra))
          (map_pmfToSubtype prior (fun _ mem => mem) checkpoint).symm))
  obtain ⟨nextNoise, joint, drained⟩ := chance_primary_traffic_factor timeouts leaks serial
    scheduler bound turns timing reference focal deviation event ownerless solitary horizon
    supported (fun seed => execution seed.val) ready noise liftedFactor
    (fun seed _ => completed seed seed.property)
  let step := fun (seed : prior.support) =>
    (execution seed).application.config.step event (ready seed) action
  let rank := Config.rankPrefix (graph := graph) (event.val + 1)
  let reduce := fun next => rank (State.drainConfig next)
  have retained (next : graph.Config) (reached : next ∈ (supported.bind step).support) :
      reduce next = next := by
    obtain ⟨seed, _, stepped⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
    have priorPrefix : (execution seed).application.config.cut.IsPrefix event.val := by
      rw [physical seed]
      exact ordered seed seed.property
    have nextPrefix : next.cut.IsPrefix (event.val + 1) := by
      have cut := (execution seed).application.config.step_cut event (ready seed) action
        next stepped
      rw [cut]
      exact priorPrefix.complete_at event (ready seed) rfl
    exact Config.rankPrefix_of_path nextPrefix (State.ofConfig next).drain_graph_steps
  have stepLaw : supported.bind step =
      prior.bind fun seed =>
        if available : (checkpoint seed).cut.Ready event then
          (checkpoint seed).step event available action
        else PMF.pure (checkpoint seed) := by
    rw [← bind_supported]
    apply bind_congr_on_support _
    intro seed _
    have available := (ordered seed seed.property).ready event.isLt
    have moved : ∀ (config : graph.Config) (legal : config.cut.Ready event),
        config = checkpoint seed → config.step event legal action =
          (checkpoint seed).step event available action := by
      intro config legal same
      subst config
      rfl
    simp only [dite_eq_left available]
    exact moved _ (ready seed) (physical seed)
  refine ⟨nextNoise, ?_⟩
  have samePhases : (supported.bind fun seed => phase seed.val) = prior.bind phase :=
    bind_supported phase
  rw [← samePhases, PMF.map_bind]
  have masked := congrArg (PMF.map (fun pair => (reduce pair.1, pair.2))) joint
  rw [PMF.map_bind, PMF.map_bind] at masked
  refine Eq.trans ?_ (masked.trans ?_)
  · apply bind_congr_on_support _
    intro seed member
    rw [PMF.map_comp]
    apply map_congr_on_support _
    intro final reached
    exact congrArg (fun config => (rank config, traffic final))
      (drained seed member final reached)
  · rw [← stepLaw]
    apply bind_congr_on_support _
    intro next reached
    rw [PMF.map_comp]
    exact congrArg (fun config => (nextNoise (observe next)).map fun extra => (config, extra))
      (retained next reached)

end Vegas.EventGraphRuntime
