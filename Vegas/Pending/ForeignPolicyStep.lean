module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.PhysicalPrefixPolicy
public import Vegas.Pending.ForeignBindingPhase

@[expose] public section

/-! # Unchanged graph policy at a foreign physical prefix -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {timeouts : EventTimeouts graph.sequentialize}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize)}

local notation "G" => graph.sequentialize
local notation "app" => reactiveApplication timeouts leaks

/-- Convert a foreign primary-checkpoint traffic law into one of the physical
prefix policy steps. Every actual prefix supplies its ordered graph
checkpoint, horizon bound and drain equation. An active owner places the
native execution at the checkpoint rank itself. -/
theorem foreign_physicalPrefix_policyStep
    (scheduler : (app).Scheduler) (players : Player → (app).Policy)
    (inputs : PMF (G).Inputs) (horizon : Nat) (reference : (G).BehavioralProfile)
    (focal owner : Player) (event : (G).EventId) (owned : (G).actor? event = some owner)
    (completes : CompletesPlay timeouts leaks (inputs.map State.initial) horizon scheduler) :
    let prior := physicalPrefix timeouts leaks scheduler players inputs horizon event.val
    let config := fun execution : (app).Execution =>
      Config.rankPrefix event.val execution.application.config
    let phase := fun (execution : (app).Execution) =>
      (app).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon execution
    let observe := (G).playerObserve focal
    let traffic := bindingTraffic timeouts leaks focal
    (∀ (noise : (G).PlayerObservation focal → PMF (BindingTraffic timeouts leaks)),
      prior.map (fun before => (config before, traffic before)) =
        (prior.map config).bind (fun before =>
          (noise (observe before)).map fun extra => (before, extra)) →
      (∀ before ∈ prior.support, (config before).cut.IsPrefix event.val) →
      (∀ before ∈ prior.support, before.application.config = State.drainConfig (config before)) →
      (∀ before ∈ prior.support, owner ∉ (config before).defaulted →
        PrefixBoundary (inputs.map State.initial) scheduler players event.val before) →
      (∀ before ∈ prior.support, before.environmentRecall.length ≤ horizon) →
      ∃ nextNoise : (G).PlayerObservation focal → PMF (BindingTraffic timeouts leaks),
        (prior.bind phase).map (fun final =>
          (Config.rankPrefix (event.val + 1) final.application.config, traffic final)) =
        (prior.bind fun before =>
          if ready : (config before).cut.Ready event then
            eventStep reference (config before) event ready
          else PMF.pure (config before)).bind fun primary =>
            (nextNoise (observe primary)).map fun extra => (primary, extra)) →
    PhysicalPrefixPolicyStep scheduler players inputs horizon reference focal event := by
  intro prior config phase observe traffic atCheckpoint noise factor
  have solitary := graph.sequentialize_solitary event
  have facts (execution : (app).Execution) (member : execution ∈ prior.support) :=
    physicalPrefix_supported timeouts leaks scheduler players inputs horizon completes
      event.val event.isLt.le execution member
  have ordered (execution : (app).Execution) (member : execution ∈ prior.support) :
      (config execution).cut.IsPrefix event.val := by
    obtain ⟨_, _, _, _, ordered, _⟩ := facts execution member
    exact ordered
  have aligned (execution : (app).Execution) (member : execution ∈ prior.support) :
      execution.application.config = State.drainConfig (config execution) := by
    obtain ⟨_, _, _, _, _, aligned⟩ := facts execution member
    exact aligned
  have bounded (execution : (app).Execution) (member : execution ∈ prior.support) :
      execution.environmentRecall.length ≤ horizon := by
    obtain ⟨_, _, _, bounded, _, _⟩ := facts execution member
    exact bounded
  have boundary (execution : (app).Execution) (member : execution ∈ prior.support)
      (active : owner ∉ (config execution).defaulted) :
      PrefixBoundary (inputs.map State.initial) scheduler players event.val execution := by
    obtain ⟨actualRank, _, boundary, _, primary, native⟩ := facts execution member
    have quiet (other : (G).EventId)
        (automatic : (State.ofConfig (config execution)).AutomaticReady other) : False := by
      have same := solitary _ automatic.1 (primary.ready event.isLt)
      subst other
      have inactive := automatic.2
      rw [owned] at inactive
      exact active inactive
    have exactConfig : execution.application.config = config execution :=
      native.trans (State.drainConfig_of_quiescent (State.ofConfig (config execution)) quiet)
    have atRank : actualRank = event.val :=
      boundary.ordered.unique (exactConfig.symm ▸ primary)
    exact atRank ▸ boundary
  obtain ⟨nextNoise, law⟩ := atCheckpoint noise factor ordered aligned boundary bounded
  refine ⟨reference focal, nextNoise, ?_⟩
  simp only [Function.update_eq_self]
  rw [physicalPrefix_succ]
  refine law.trans ?_
  apply congrArg (fun marginal : PMF (G).Config => marginal.bind
    (fun primary => (nextNoise (observe primary)).map fun extra => (primary, extra)))
  rw [PMF.bind_map]
  apply bind_congr_on_support _
  intro execution supported
  have atPrefix := ordered execution supported
  rw [dite_eq_left (atPrefix.ready event.isLt)]
  exact (runPlan_one_at_prefix reference (config execution) event atPrefix).symm

/-- Active and already-drained checkpoints at a foreign binding keep the
reference graph policy at that event. -/
theorem physicalPrefix_foreign_binding_policyStep
    {horizon turns : Nat} (scheduler : (app).Scheduler)
    (delay bound : (G).EventId → Nat) (inputs : PMF (G).Inputs)
    (reference : (G).BehavioralProfile)
    (contract : AsyncContract timeouts leaks (inputs.map State.initial) horizon scheduler
      delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (focal owner : Player) (deviation : (app).Policy) (foreign : owner ≠ focal)
    (event : (G).EventId) {payload : L.Ty}
    (outputEq : (G).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (G).layout) outputEq)
      ((G).nodes event) = .bind owner payload)
    (node : nodeView (G) event = .bind owner payload outputEq codeEq) :
    let players := Function.update (turnPolicy timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming G turns) reference) focal deviation
    PhysicalPrefixPolicyStep scheduler players inputs horizon reference focal event := by
  intro players
  apply foreign_physicalPrefix_policyStep scheduler players inputs horizon reference
    focal owner event (nodeView_bind_actor outputEq codeEq) contract.completes
  exact foreign_binding_checkpoint_primary_traffic_factor (graph := graph.sequentialize)
    (timeouts := timeouts) (leaks := leaks)
    (fun next => (graph.sequentialize_solitary next).ownerSolitary)
    scheduler delay bound reference contract timely focal owner deviation foreign event
    (graph.sequentialize_solitary event) outputEq codeEq node
    (physicalPrefix timeouts leaks scheduler players inputs horizon event.val)
    id (fun execution => Config.rankPrefix event.val execution.application.config)

end Vegas.EventGraphRuntime
