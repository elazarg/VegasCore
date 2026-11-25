module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ChanceCheckpointTraffic
public import Vegas.Pending.FocalCompletionTraffic
public import Vegas.Pending.PhysicalPrefix

@[expose] public section

/-! # One rank of physical traffic and graph play -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- At an ownerless or focal-owned event, advance one rank while preserving
the factorization of actual traffic through the graph observation. -/
theorem physicalPrefix_singleOwner_phase
    (timeouts : EventTimeouts graph.sequentialize)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    (scheduler : (reactiveApplication timeouts leaks).Scheduler)
    (bound : graph.sequentialize.EventId → Nat) (turns : Nat)
    (timing : EventGraphRuntime.TurnTiming graph.sequentialize turns)
    (reference : graph.sequentialize.BehavioralProfile)
    (focal : Player) (deviation : (reactiveApplication timeouts leaks).Policy)
    (inputs : PMF graph.sequentialize.Inputs) (horizon : Nat)
    (completes : CompletesPlay timeouts leaks (inputs.map State.initial) horizon scheduler)
    (event : graph.sequentialize.EventId)
    (owner : graph.sequentialize.actor? event = none ∨
      graph.sequentialize.actor? event = some focal) :
    let players := Function.update (turnPolicy timeouts leaks bound turns timing reference)
      focal deviation
    let prior := physicalPrefix timeouts leaks scheduler players inputs horizon event.val
    let next := physicalPrefix timeouts leaks scheduler players inputs horizon (event.val + 1)
    let checkpoint := fun execution : (reactiveApplication timeouts leaks).Execution =>
      Config.rankPrefix event.val execution.application.config
    let traffic := bindingTraffic timeouts leaks focal
    let observe := graph.sequentialize.playerObserve focal
    ∀ noise : graph.sequentialize.PlayerObservation focal → PMF (BindingTraffic timeouts leaks),
      prior.map (fun execution => (checkpoint execution, traffic execution)) =
        (prior.map checkpoint).bind (fun before =>
          (noise (observe before)).map fun extra => (before, extra)) →
      ∃ siteLaw : graph.sequentialize.PlayerObservation focal →
          PMF (graph.sequentialize.Action event),
      ∃ nextNoise : graph.sequentialize.PlayerObservation focal →
          PMF (BindingTraffic timeouts leaks),
        next.map (fun execution =>
          (Config.rankPrefix (event.val + 1) execution.application.config, traffic execution)) =
          (prior.bind fun execution =>
            let config := checkpoint execution
            if ready : config.cut.Ready event then
              (siteLaw (observe config)).bind fun action => config.step event ready action
            else PMF.pure config).bind fun primary =>
              (nextNoise (observe primary)).map fun extra => (primary, extra) := by
  classical
  intro players prior next checkpoint traffic observe noise factor
  let app := reactiveApplication timeouts leaks
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
  let phase := fun execution => app.runUntilHorizon scheduler players stop horizon execution
  have shape (execution) (present : execution ∈ prior.support) :=
    physicalPrefix_supported timeouts leaks scheduler players inputs horizon completes
      event.val event.isLt.le execution present
  have ordered (execution) (present : execution ∈ prior.support) :
      (checkpoint execution).cut.IsPrefix event.val := by
    obtain ⟨_, _, _, _, result, _⟩ := shape execution present
    exact result
  have aligned (execution) (present : execution ∈ prior.support) :
      execution.application.config = State.drainConfig (checkpoint execution) := by
    obtain ⟨_, _, _, _, _, result⟩ := shape execution present
    exact result
  have completed (execution) (present : execution ∈ prior.support)
      (final) (member : final ∈ (phase execution).support) : stop final := by
    obtain ⟨_, _, boundary, within, _⟩ := shape execution present
    by_cases done : stop execution
    · change final ∈ (app.runUntil scheduler players stop
        (horizon - execution.environmentRecall.length) execution).support at member
      rw [app.runUntil_of_stop scheduler players stop _ execution done,
        PMF.mem_support_pure_iff] at member
      exact member.symm ▸ done
    · exact (runUntilHorizon_event_progress completes event execution final
        boundary.supported within done member).2.2.1
  have successor : next = prior.bind phase :=
    physicalPrefix_succ timeouts leaks scheduler players inputs horizon event
  rcases owner with ownerless | owned
  · obtain ⟨nextNoise, law⟩ := chance_checkpoint_traffic_factor timeouts leaks
      (fun event => (graph.sequentialize_solitary event).ownerSolitary) scheduler bound turns
      timing reference focal deviation event ownerless (graph.sequentialize_solitary event)
      horizon prior id checkpoint noise factor ordered aligned completed
    exact ⟨fun _ => PMF.pure (EventCode.actionOfActorNone
      (graph.sequentialize.nodes event) ownerless), nextNoise, by
        rw [successor]
        refine law.trans ?_
        apply congrArg (fun phase : PMF graph.sequentialize.Config => phase.bind fun primary =>
          (nextNoise (observe primary)).map fun extra => (primary, extra))
        apply bind_congr_on_support _
        intro execution present
        have ready := (ordered execution present).ready event.isLt
        simp only [dite_eq_left ready, PMF.pure_bind]⟩
  · obtain ⟨siteLaw, nextNoise, law⟩ := focal_checkpoint_primary_traffic_factor timeouts leaks
      scheduler bound turns timing reference focal deviation event owned
      (graph.sequentialize_solitary event) horizon prior id checkpoint noise factor
      ordered aligned completed
    exact ⟨siteLaw, nextNoise, by rw [successor]; exact law⟩

end Vegas.EventGraphRuntime
