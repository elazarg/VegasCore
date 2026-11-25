module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.EventCompletionStopping
public import Vegas.Pending.ConfigDrain
public import Vegas.EventGraph.Information
public import Vegas.Pending.FocalTraffic
public import GameTheory.Math.Probability.ConditionalObservation

@[expose] public section

/-! # Configurations at the first native completion of an owned event

A stopped native execution records the action at the selected event in the
owner's actual recall. Given that action, the primary graph step is
deterministic. Automatic service can extend the final configuration beyond
that primary step.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
    {graph : Vegas.EventGraph Player L}

/-- The action recorded for an event in a player's actual graph observation. -/
def recalledAction {owner : Player} (event : graph.EventId)
    (observation : graph.PlayerObservation owner) : Option (graph.Action event) :=
  (observation.ownActions.find? (fun record => record.event = event)).bind fun record =>
    if equal : record.event = event then
      record.decision.map (cast (congrArg graph.Action equal))
    else none

private theorem recalledAction_of_mem (config : graph.Config)
    (event : graph.EventId) (owner : Player) (owned : graph.actor? event = some owner)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (present : EventGraph.completion graph event (some action) value ∈ config.history) :
    recalledAction event (graph.playerObserve owner config) = some action := by
  let record := EventGraph.completion graph event (some action) value
  have recalled : record ∈ graph.ownCompletions owner config.history :=
    (EventGraph.mem_ownCompletions owner config.history record).2 ⟨present, owned, rfl⟩
  have found : (graph.ownCompletions owner config.history).find?
      (fun earlier => earlier.event = event) = some record := by
    cases selected : (graph.ownCompletions owner config.history).find?
        (fun earlier => earlier.event = event) with
    | none =>
        have absent := List.find?_eq_none.mp selected record recalled
        exact (absent (by simp only [record, EventGraph.completion, decide_true])).elim
    | some earlier =>
        have member := List.mem_of_find?_eq_some selected
        have matching : earlier.event = event := by
          simpa only [decide_eq_true_eq] using List.find?_some selected
        have retained := ((EventGraph.mem_ownCompletions owner config.history earlier).1 member).1
        exact congrArg some
          (List.inj_on_of_nodup_map config.history_nodup retained present matching)
  unfold recalledAction
  change ((graph.ownCompletions owner config.history).find? _).bind _ = _
  rw [found]
  simp [record, EventGraph.completion]

/-- The stopped configuration law of any native client at an active, solitary
owned event is the primary graph step with the action read from actual owner
recall, followed by the graph's deterministic automatic drain. -/
theorem owned_completed_config_law
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (event : graph.EventId) (owner : Player) (owned : graph.actor? event = some owner)
    (count : Nat) (before : ((reactiveApplication timeouts) leaks).Execution)
    (ready : before.application.config.cut.Ready event)
    (unique : ∀ other, before.application.config.cut.Ready other → other = event)
    (active : owner ∉ before.application.config.defaulted)
    (quiescent : ∀ other, ¬ before.application.AutomaticReady other)
    {Readout : Type*} (read : ((reactiveApplication timeouts) leaks).Execution → Readout)
    (completed : ∀ after ∈ (((reactiveApplication timeouts) leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count before).support,
      event ∈ after.application.config.cut.completed) :
    let phase := ((reactiveApplication timeouts) leaks).runUntil scheduler players
      (fun final => event ∈ final.application.config.cut.completed) count before
    let pick := fun final =>
      (recalledAction event (final.application.playerView owner).observation).getD
        ((graph.nodes event).failureAction owner owned)
    phase.map (fun final => (final.application.config, read final)) =
      phase.bind fun final =>
        (before.application.config.step event ready (pick final)).map
          (fun config => (State.drainConfig config, read final)) := by
  intro phase pick
  rw [← PMF.bind_pure_comp]
  apply bind_congr_on_support _
  intro after reached
  obtain ⟨action, native, primary, drained⟩ := runUntil_completed_primary_drain timeouts
    leaks scheduler players event count before after ready unique quiescent reached
    (completed after reached)
  obtain ⟨value, _, recorded⟩ :=
    before.application.config.step_completion event ready action native.config primary
  rw [before.application.config.actualDecision_of_active event owner owned active action]
    at recorded
  obtain ⟨extra, retained⟩ := Config.Step.path_history_prefix native.drain_graph_steps
  have present : EventGraph.completion graph event (some action) value ∈
      after.application.config.history := by
    rw [drained, ← retained, recorded]
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
  have chosen : pick after = action := by
    dsimp only [pick, State.playerView]
    rw [recalledAction_of_mem after.application.config event owner owned action value present]
    rfl
  obtain ⟨target, stepLaw⟩ := before.application.config.step_eq_pure_of_actor event ready
    action owner owned
  rw [stepLaw, PMF.mem_support_pure_iff] at primary
  change PMF.pure (after.application.config, read after) =
    (before.application.config.step event ready (pick after)).map
      (fun config => (State.drainConfig config, read after))
  rw [chosen, stepLaw, PMF.pure_map, drained, native.drain_config_eq, primary]

/-- If a native execution is already at the drain of a graph checkpoint,
advancing an automatic head takes no more native rounds. Its graph step still
advances exactly one rank, and then drains to the unchanged native endpoint. -/
theorem defaulted_completed_config_law
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (horizon : Nat) (before : ((reactiveApplication timeouts) leaks).Execution)
    (checkpoint : graph.Config)
    (aligned : before.application.config = State.drainConfig checkpoint)
    (event : graph.EventId) (ready : checkpoint.cut.Ready event)
    (unique : ∀ other, checkpoint.cut.Ready other → other = event)
    (owner : Player) (owned : graph.actor? event = some owner)
    (inactive : owner ∈ checkpoint.defaulted) (action : graph.Action event) :
    (((reactiveApplication timeouts) leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon before).map
        (fun final => final.application.config) =
      (checkpoint.step event ready action).map State.drainConfig := by
  have completed : event ∈ before.application.config.cut.completed := by
    rw [aligned]
    exact State.drainConfig_completed_of_defaulted checkpoint event ready unique owner owned
      inactive
  rw [State.step_drainConfig_of_defaulted checkpoint event ready unique owner owned inactive,
    ReactiveApplication.runUntilHorizon,
    ReactiveApplication.runUntil_of_stop _ _ _ _ _ before completed, PMF.pure_map, aligned]

/-- At a solitary active event of the focal player, actual native traffic
induces an action law of its graph observation alone. The exact stopped
configuration law uses that action followed by deterministic automatic service. -/
theorem focal_owned_completed_config_law
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
        (prior.bind fun seed => (phase seed).map (fun final => final.application.config)) =
          prior.bind fun seed =>
            if ready : (config seed).cut.Ready event then
              (law (observe (config seed))).bind fun action =>
                ((config seed).step event ready action).map State.drainConfig
            else PMF.pure (config seed) := by
  intro app config traffic observe players phase noise factor ready active completed
  have alone (cut : graph.order.Cut) (other : graph.EventId)
      (ready : cut.Ready event) (otherReady : cut.Ready other) :
      other = event := solitary cut otherReady ready
  have phaseEq (seed : Seed) (supported : seed ∈ prior.support) :
      phase seed = app.runUntilHorizon scheduler (focalPlayers timeouts leaks focal deviation)
        (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed) :=
    runUntil_turnPolicy_focal (timeouts := timeouts) (leaks := leaks) scheduler bound turns
      timing reference focal deviation event (Or.inr owned) solitary _ (execution seed)
      (fun _ => ready seed supported)
  obtain ⟨channel, channelLaw⟩ := exists_updated_observation_kernel_of_readout
    prior config (fun seed => traffic (execution seed)) observe noise factor
    (fun _ => PMF.pure ()) (fun before _ => before) observe
    (fun seed _ => (phase seed).map traffic)
    (fun _ _ _ _ _ _ _ _ same => same)
    (fun left leftSupport _ _ right rightSupport _ _ _ same => by
      have recalled := congrArg (fun value => value.2.2.1) same
      change (execution left).environmentRecall = (execution right).environmentRecall at recalled
      rw [phaseEq left leftSupport, phaseEq right rightSupport]
      simp only [ReactiveApplication.runUntilHorizon, recalled]
      exact focalPhase_traffic_congr scheduler focal deviation (Or.inr owned) alone
        (horizon - (execution right).environmentRecall.length) (execution left) (execution right)
        (fun _ => ready left leftSupport) (fun _ => ready right rightSupport) same)
  have joint : (prior.bind fun seed => (phase seed).map fun final =>
      (config seed, traffic final)) =
      (prior.map config).bind fun before =>
        (channel (observe before)).map fun extra => (before, extra) := by
    simpa only [PMF.pure_bind, PMF.pure_map, PMF.bind_pure, PMF.map_comp, Function.comp_def]
      using channelLaw
  let pick := fun extra : MessageNetwork Player app.Payload ×
      List (MessageId Player × Bool) × List app.EnvironmentEntry × List app.PlayerEntry ×
      PlayerView graph × PublicView graph =>
    (recalledAction event extra.2.2.2.2.1.observation).getD
      ((graph.nodes event).failureAction focal owned)
  let advance := fun (before : graph.Config) action =>
    if ready : before.cut.Ready event then
      (before.step event ready action).map State.drainConfig
    else PMF.pure before
  refine ⟨fun observed => (channel observed).map pick, ?_⟩
  calc
    _ = (prior.bind fun seed => (phase seed).map fun final =>
          (config seed, traffic final)).bind (fun pair => advance pair.1 (pick pair.2)) := by
      simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
      apply bind_congr_on_support _
      intro seed supported
      have readyAt := ready seed supported
      have clear (other : graph.EventId) (eligible : (execution seed).application.AutomaticReady
          other) : False := by
        obtain rfl := solitary _ eligible.1 readyAt
        have inactive := eligible.2
        rw [owned] at inactive
        exact active seed supported inactive
      have stopped := owned_completed_config_law timeouts leaks scheduler players event focal
        owned (horizon - (execution seed).environmentRecall.length) (execution seed)
        readyAt (fun _ otherReady => solitary _ otherReady readyAt)
        (active seed supported) clear traffic (completed seed supported)
      have projected := congrArg (PMF.map Prod.fst) stopped
      simpa only [advance, dite_eq_left readyAt, PMF.map_comp, PMF.map_bind, Function.comp_def,
        phase, ReactiveApplication.runUntilHorizon, config, pick, traffic, bindingTraffic, app]
        using projected
    _ = _ := by
      rw [joint]
      simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, advance]
      apply bind_congr_on_support _
      intro seed supported
      simp only [dite_eq_left (ready seed supported)]
      rfl

/-- The initialized focal phase needs no traffic-factorization premise. The
initial contents may be correlated, and the service contract supplies
completion of the selected event even on a silent deviation. -/
theorem focal_initial_completed_config_law
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (bound : graph.EventId → Nat) (turns : Nat) (timing : EventGraphRuntime.TurnTiming graph turns)
    (reference : graph.BehavioralProfile)
    (focal : Player) (deviation : ((reactiveApplication timeouts) leaks).Policy)
    (event : graph.EventId) (owned : graph.actor? event = some focal)
    (solitary : graph.Solitary event) (ready : (EventOrder.Cut.empty graph.order).Ready event)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (completes : CompletesPlay timeouts leaks (inputs.map State.initial) horizon scheduler) :
    let app := (reactiveApplication timeouts) leaks
    let players := Function.update (turnPolicy timeouts leaks bound turns timing reference)
      focal deviation
    ∃ law : graph.PlayerObservation focal → PMF (graph.Action event),
      (inputs.bind fun initial =>
        (app.runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (ReactiveApplication.Execution.initial app (State.initial initial))).map
            (fun final => final.application.config)) =
        inputs.bind fun initial =>
          let config := EventGraph.Config.initial initial
          (law (graph.playerObserve focal config)).bind fun action =>
            (config.step event ready action).map State.drainConfig := by
  intro app players
  let start := fun seed => ReactiveApplication.Execution.initial app (State.initial seed)
  obtain ⟨noise, factor⟩ := initial_bindingTraffic_factorization timeouts leaks focal inputs
  have support (seed : graph.Inputs) (member : seed ∈ inputs.support) :
      start seed ∈ (app.roundsFrom (inputs.map State.initial) scheduler players
        (start seed).environmentRecall.length).support := by
    change start seed ∈ (app.roundsFrom (inputs.map State.initial) scheduler players 0).support
    unfold ReactiveApplication.roundsFrom
    exact (PMF.mem_support_bind_iff _ _ _).mpr
      ⟨State.initial seed, (PMF.mem_support_map_iff _ _ _).mpr ⟨seed, member, rfl⟩,
        (PMF.mem_support_pure_iff _ _).mpr rfl⟩
  obtain ⟨law, stopped⟩ := focal_owned_completed_config_law timeouts leaks scheduler bound turns
    timing reference focal deviation event owned solitary horizon inputs start noise factor
    (fun _ _ => ready) (by intro seed _; change focal ∉ (∅ : Finset Player); simp)
    (fun seed member final reached =>
      (runUntilHorizon_event_progress completes event (start seed) final (support seed member)
        (Nat.zero_le _) ready.1 reached).2.2.1)
  refine ⟨law, stopped.trans ?_⟩
  apply bind_congr_on_support _
  intro seed _
  rw [dite_eq_left (show (start seed).application.config.cut.Ready event from ready)]
  rfl

/-- On a single-event graph the observation-local focal action realizes the
complete arbitrary-deviation configuration law. The horizon may extend past
the completion round. -/
theorem focal_single_event_config_law
    (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (bound : graph.EventId → Nat) (turns : Nat) (timing : EventGraphRuntime.TurnTiming graph turns)
    (reference : graph.BehavioralProfile)
    (focal : Player) (deviation : ((reactiveApplication timeouts) leaks).Policy)
    (event : graph.EventId) (owned : graph.actor? event = some focal)
    (count : graph.order.eventCount = 1)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (completes : CompletesPlay timeouts leaks (inputs.map State.initial) horizon scheduler) :
    let app := (reactiveApplication timeouts) leaks
    let players := Function.update (turnPolicy timeouts leaks bound turns timing reference)
      focal deviation
    ∃ policy : graph.BehavioralPolicy focal,
      (app.roundsFrom (inputs.map State.initial) scheduler players horizon).map
          (fun final => final.application.config) =
        inputs.bind (graph.runPolicies graph.canonicalScheduler
          (Function.update reference focal policy)) := by
  intro app players
  have same (other : graph.EventId) : other = event := by
    have left := other.isLt
    have right := event.isLt
    apply Fin.ext
    omega
  have ready : (EventOrder.Cut.empty graph.order).Ready event := by
    refine ⟨by simp [EventOrder.Cut.empty], ?_⟩
    intro other prior
    have before := graph.order.predecessor_lt prior
    rw [same other] at before
    exact (Nat.lt_irrefl _ before).elim
  have terminal (config : graph.Config) (completed : event ∈ config.cut.completed) :
      config.cut.Terminal := by
    apply Finset.eq_univ_iff_forall.mpr
    intro other
    simpa only [same other] using completed
  have solitary : graph.Solitary event := by
    intro _ other _ _
    exact same other
  obtain ⟨law, phaseLaw⟩ := focal_initial_completed_config_law timeouts leaks scheduler bound turns
    timing reference focal deviation event owned solitary ready inputs horizon completes
  let policy : graph.BehavioralPolicy focal :=
    fun other _ observed _ => (same other).symm ▸ law observed
  refine ⟨policy, ?_⟩
  let stop := fun after : app.Execution => event ∈ after.application.config.cut.completed
  let start := fun seed => ReactiveApplication.Execution.initial app (State.initial seed)
  have native :
      (app.roundsFrom (inputs.map State.initial) scheduler players horizon).map
          (fun final => final.application.config) =
        inputs.bind fun seed =>
          (app.runUntilHorizon scheduler players stop horizon (start seed)).map
            (fun final => final.application.config) := by
    unfold ReactiveApplication.roundsFrom
    rw [PMF.map_bind, PMF.bind_map]
    apply bind_congr_on_support _
    intro seed member
    have supported : start seed ∈ (app.roundsFrom (inputs.map State.initial) scheduler
          players (start seed).environmentRecall.length).support := by
      change start seed ∈ (app.roundsFrom (inputs.map State.initial) scheduler players 0).support
      unfold ReactiveApplication.roundsFrom
      exact (PMF.mem_support_bind_iff _ _ _).mpr
        ⟨State.initial seed, (PMF.mem_support_map_iff _ _ _).mpr ⟨seed, member, rfl⟩,
          (PMF.mem_support_pure_iff _ _).mpr rfl⟩
    change (app.runToHorizon scheduler players horizon (start seed)).map _ = _
    rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players stop, PMF.map_bind,
      ← PMF.bind_pure_comp]
    apply bind_congr_on_support _
    intro stopped reached
    have progress := runUntilHorizon_event_progress completes event (start seed) stopped supported
      (Nat.zero_le _) ready.1 reached
    have completed := terminal _ progress.2.2.1
    change ((app.runRounds scheduler players _ stopped).map (fun final =>
      final.application.config)) = PMF.pure stopped.application.config
    rw [map_congr_on_support _ (g := fun _ => stopped.application.config)
      (fun final member => EventGraph.Config.Step.path_eq_of_terminal
        (reactive_runRounds_graph_steps timeouts leaks scheduler players _ stopped final member)
        completed), pmf_map_fun_const]
  rw [native, phaseLaw]
  apply bind_congr_on_support _
  intro seed _
  let initial := Config.initial (graph := graph) seed
  have available : initial.cut.Ready event := ready
  have active : focal ∉ initial.defaulted := by change focal ∉ (∅ : Finset Player); simp
  unfold runPolicies run
  rw [count, runPlan_canonical_succ _ 0 initial available.not_terminal event available
    (fun other _ => (same other).ge)]
  simp only [runPlan, PMF.bind_pure, eventStep, actionLaw_of_actor _ _ owned, dite_eq_right active,
    Function.update_self, policy]
  apply bind_congr_on_support _
  intro action _
  rw [map_congr_on_support _ (g := id) ?_, PMF.map_id]
  intro final member
  have completed : event ∈ final.cut.completed := by
    rw [initial.step_cut event available action final member, EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  exact State.drainConfig_of_quiescent (State.ofConfig final) fun other eligible =>
    eligible.1.1 ((same other).symm ▸ completed)


end Vegas.EventGraphRuntime
