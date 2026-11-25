module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ChanceCompletionConfig
public import Vegas.Pending.FocalTraffic
public import Vegas.EventGraph.CompletionObservation
public import GameTheoryExtensions.Math.Probability.ObservedChoice

@[expose] public section

/-! # The traffic factor at a canonical public chance checkpoint -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => (reactiveApplication timeouts) leaks

/-- A solitary public sample preserves observation-local traffic at the primary
graph checkpoint. The retained traffic comes from the actual stopped execution,
including automatic service after the sample. The primary checkpoint itself
contains precisely one graph step. -/
theorem chance_primary_traffic_factor
    (serial : graph.ActorSerial) (scheduler : (app).Scheduler)
    (bound : graph.EventId → Nat) (turns : Nat)
    (timing : EventGraphRuntime.TurnTiming graph turns)
    (reference : graph.BehavioralProfile) (focal : Player) (deviation : (app).Policy)
    (event : graph.EventId) (ownerless : graph.actor? event = none)
    (solitary : graph.Solitary event)
    (horizon : Nat) {Seed : Type*} (prior : PMF Seed) (execution : Seed → (app).Execution)
    (ready : ∀ seed, (execution seed).application.config.cut.Ready event) :
    let config := fun seed => (execution seed).application.config
    let traffic := (bindingTraffic timeouts) leaks focal
    let observe := graph.playerObserve focal
    let players := Function.update (turnPolicy timeouts leaks bound turns timing reference)
      focal deviation
    let phase := fun seed => (app).runUntilHorizon scheduler players
      (fun current => event ∈ current.application.config.cut.completed) horizon (execution seed)
    let action := EventCode.actionOfActorNone (graph.nodes event) ownerless
    let primary := fun seed final =>
      ((observe final.application.config).store (.inr event)).elim (config seed)
        (fun value => (config seed).complete event
          (ready seed) action value)
    ∀ (noise : graph.PlayerObservation focal → PMF _),
      prior.map (fun seed => (config seed, traffic (execution seed))) =
        (prior.map config).bind (fun before =>
          (noise (observe before)).map fun extra => (before, extra)) →
      (∀ seed ∈ prior.support, ∀ final ∈ (phase seed).support,
        event ∈ final.application.config.cut.completed) →
      ∃ nextNoise : graph.PlayerObservation focal → PMF _,
        (prior.bind fun seed => (phase seed).map fun final => (primary seed final, traffic final)) =
          (prior.bind fun seed =>
            (config seed).step event (ready seed) action).bind (fun next =>
              (nextNoise (observe next)).map (fun extra => (next, extra))) ∧
          ∀ seed ∈ prior.support, ∀ final ∈ (phase seed).support,
            final.application.config = State.drainConfig (primary seed final) := by
  classical
  intro config traffic observe players phase action primary noise factor completed
  have visible : graph.fieldVisibleTo focal (.inr event) := by
    cases node : nodeView graph event with
    | bind owner payload outputEq codeEq =>
      rw [nodeView_bind_actor outputEq codeEq] at ownerless
      cases ownerless
    | resolve owner payload binding checks outputEq codeEq =>
      rw [nodeView_resolve_actor outputEq codeEq] at ownerless
      cases ownerless
    | sample payload law outputEq codeEq =>
      change (graph.outputLayout event).VisibleTo focal
      rw [outputEq]
      trivial
  let read := fun seed => traffic (execution seed)
  let output : graph.Config → Option (graph.outputLayout event).Value :=
    fun current => current.store (.inr event)
  let pick := fun extra : MessageNetwork Player (app).Payload ×
      List (MessageId Player × Bool) × List (app).EnvironmentEntry × List (app).PlayerEntry ×
      PlayerView graph × PublicView graph =>
    (extra.2.2.2.2.1.observation.store (.inr event) : Option (graph.outputLayout event).Value)
  let step := fun (before : graph.Config) =>
    if ready : before.cut.Ready event then before.step event ready action else PMF.pure before
  let advance := fun (before : graph.Config) (choice : Option (graph.outputLayout event).Value) =>
    if ready : before.cut.Ready event then
      choice.elim before (fun value => before.complete event ready action value)
    else before
  let choice := fun before => (step before).map output
  let posterior := fun seed sampled => fiberPosterior ((phase seed).map traffic) pick sampled
  have readyAt (seed : Seed) : (config seed).cut.Ready event :=
    ready seed
  have chosen (before : graph.Config) (ready : before.cut.Ready event) (value) :
      advance before (some value) = before.complete event ready action value := by
    simp only [advance, dite_eq_left ready, Option.elim_some]
  have returned (before : graph.Config) (ready : before.cut.Ready event)
      (next : graph.Config) (member : next ∈ (step before).support) :
      ∃ value, next = before.complete event ready action value ∧ output next = some value := by
    simp only [step, dite_eq_left ready, Config.step, PMF.support_map] at member
    obtain ⟨value, _, rfl⟩ := member
    exact ⟨value, rfl, Config.complete_output_same ..⟩
  have reflect (left right : Seed) (a b : Option (graph.outputLayout event).Value)
      (present : a ∈ (choice (config left)).support)
      (other : b ∈ (choice (config right)).support)
      (same : observe (advance (config left) a) = observe (advance (config right) b)) :
      observe (config left) = observe (config right) ∧ a = b := by
    obtain ⟨next, supported, found⟩ := (PMF.mem_support_map_iff _ _ _).mp present
    obtain ⟨next', supported', found'⟩ := (PMF.mem_support_map_iff _ _ _).mp other
    obtain ⟨first, _, seen⟩ := returned _ (readyAt left) next supported
    obtain ⟨second, _, seen'⟩ := returned _ (readyAt right) next' supported'
    have firstEq : a = some first := found.symm.trans seen
    have secondEq : b = some second := found'.symm.trans seen'
    rw [firstEq, secondEq, chosen _ (readyAt left), chosen _ (readyAt right)] at same
    have previous := congrArg (beforeCompletion event) same
    change beforeCompletion event
        (graph.playerObserve focal ((config left).complete event (readyAt left) action first)) =
      beforeCompletion event
        (graph.playerObserve focal ((config right).complete event (readyAt right) action second))
      at previous
    rw [beforeCompletion_playerObserve, beforeCompletion_playerObserve] at previous
    refine ⟨previous, ?_⟩
    have stores := graph.store_eq_of_playerObserve_eq focal _ _ same (.inr event) visible
    rw [firstEq, secondEq]
    exact (Config.complete_output_same ..).symm.trans
      (stores.trans (Config.complete_output_same ..))
  have phaseEq (seed : Seed) :
      phase seed = (app).runUntilHorizon scheduler
        (focalPlayers timeouts leaks focal deviation)
        (fun current => event ∈ current.application.config.cut.completed) horizon
        (execution seed) :=
    runUntil_turnPolicy_focal (timeouts := timeouts) (leaks := leaks) scheduler bound turns timing
      reference focal deviation event (Or.inl ownerless) solitary _ (execution seed)
      (fun _ => readyAt seed)
  have coupled (left right : Seed) (same : read left = read right) :
      (phase left).map traffic = (phase right).map traffic := by
    have recalled : (execution left).environmentRecall = (execution right).environmentRecall :=
      congrArg (fun extra => extra.2.2.1) same
    rw [phaseEq, phaseEq]
    simp only [ReactiveApplication.runUntilHorizon, recalled]
    exact focalPhase_traffic_congr scheduler focal deviation (Or.inl ownerless)
      (fun cut _ first second => solitary cut second first) _ (execution left) (execution right)
      (fun _ => readyAt left) (fun _ => readyAt right) same
  have sampleLaw (seed : Seed) (member : seed ∈ prior.support) :
      ((phase seed).map traffic).map pick = choice (config seed) := by
    rw [PMF.map_comp]
    have same : pick ∘ traffic = fun final : (app).Execution => output final.application.config :=
      funext fun final => graph.playerStore_of_visible focal _ _ visible
    rw [same]
    simp only [choice, step, dite_eq_left (readyAt seed)]
    exact chance_completed_output_law timeouts leaks serial scheduler players event ownerless
      solitary (horizon - (execution seed).environmentRecall.length) (execution seed)
      (readyAt seed) (completed seed member)
  obtain ⟨nextNoise, law⟩ := exists_updated_observation_kernel_of_readout
    prior config read observe noise factor choice advance observe posterior
    (fun left leftSupport a first right rightSupport b second same => by
      obtain ⟨leftSeed, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp leftSupport
      obtain ⟨rightSeed, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rightSupport
      exact (reflect leftSeed rightSeed a b first second same).1)
    (fun left _ a first right _ b second observed same => by
      have options := (reflect left right a b first second observed).2
      simp only [posterior, coupled left right same, options])
  have first (seed : Seed) (member : seed ∈ prior.support) :
      (phase seed).map (fun final => (primary seed final, traffic final)) =
        (choice (config seed)).bind (fun sampled =>
          (posterior seed sampled).map fun extra => (advance (config seed) sampled, extra)) := by
    have readout := map_readout_choice ((phase seed).map traffic) pick
      (fun sampled extra => (advance (config seed) sampled, extra))
    rw [sampleLaw seed member, PMF.map_comp] at readout
    have point (final : (app).Execution) :
        advance (config seed) (pick (traffic final)) = primary seed final := by
      simp only [advance, dite_eq_left (readyAt seed)]
      rfl
    have composed :
        (fun extra => (advance (config seed) (pick extra), extra)) ∘ traffic =
          fun final => (primary seed final, traffic final) := by
      funext final
      exact congrArg (fun next => (next, traffic final)) (point final)
    rw [composed] at readout
    exact readout
  have second (seed : Seed) :
      (choice (config seed)).map (advance (config seed)) =
        (config seed).step event (readyAt seed) action := by
    change ((step (config seed)).map output).map (advance (config seed)) = _
    rw [PMF.map_comp]
    calc
      _ = (step (config seed)).map id := by
        apply map_congr_on_support _
        intro next member
        obtain ⟨value, same, seen⟩ := returned _ (readyAt seed) next member
        rw [Function.comp_apply, seen, chosen _ (readyAt seed), same, id]
      _ = _ := (PMF.map_id _).trans (dite_eq_left (readyAt seed))
  refine ⟨nextNoise, ?_, ?_⟩
  · rw [bind_congr_on_support _ first, law]
    have marginal :
        ((prior.map config).bind fun before => (choice before).map (advance before)) =
          prior.bind fun seed => (config seed).step event (readyAt seed) action := by
      rw [PMF.bind_map]
      exact bind_congr_on_support _ fun seed _ => second seed
    rw [marginal]
  · intro seed supported final reached
    have ready := readyAt seed
    have clear (other : graph.EventId) (eligible : (execution seed).application.AutomaticReady
        other) : False := by
      obtain rfl := solitary _ eligible.1 ready
      obtain ⟨owner, acting, _⟩ := eligible.owned
      rw [ownerless] at acting
      contradiction
    obtain ⟨selected, native, stepMember, drained⟩ := runUntil_completed_primary_drain timeouts
      leaks scheduler players event (horizon - (execution seed).environmentRecall.length)
      (execution seed) final ready (fun _ otherReady => solitary _ otherReady ready)
      clear reached (completed seed supported final reached)
    obtain rfl := (graph.nodes event).action_eq_of_actor_none ownerless action selected
    have inStep : native.config ∈ (step (config seed)).support := by
      simpa only [step, dite_eq_left ready] using stepMember
    obtain ⟨value, applied, stored⟩ := returned _ ready native.config inStep
    have physicalOutput : final.application.config.store (.inr event) = some value := by
      rw [drained]
      exact Config.Step.path_store_of_some native.drain_graph_steps _ _ stored
    change final.application.config = State.drainConfig
      (((graph.playerObserve focal final.application.config).store (.inr event)).elim
        (config seed) (fun value => (config seed).complete event ready action value))
    have physicalVisible :
        (graph.playerObserve focal final.application.config).store (.inr event) = some value :=
      (graph.playerStore_of_visible focal _ _ visible).trans physicalOutput
    rw [physicalVisible, Option.elim_some, drained, native.drain_config_eq, applied]

end Vegas.EventGraphRuntime
