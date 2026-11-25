module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ForeignOwnedPhase
public import Vegas.Pending.ForeignBindingObservation

@[expose] public section

/-! # The joint traffic law after a foreign binding -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {timeouts : EventTimeouts graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {inputs : PMF graph.Inputs}

local notation "app" => reactiveApplication timeouts leaks

/-- The primary rank projected from the actual stopped ledger, jointly with
focal native traffic, has the canonical foreign binding law and an
observation-local traffic factor. The prior may mix defaulted and active
checkpoints at the same rank. -/
theorem foreign_binding_checkpoint_primary_traffic_factor
    (serial : graph.ActorSerial)
    {horizon turns : Nat} (scheduler : (app).Scheduler)
    (delay bound : graph.EventId → Nat) (reference : graph.BehavioralProfile)
    (contract : AsyncContract timeouts leaks (inputs.map State.initial) horizon scheduler
      delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (focal owner : Player) (deviation : (app).Policy) (foreign : owner ≠ focal)
    (event : graph.EventId) (solitary : graph.Solitary event) {payload : L.Ty}
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    {Seed : Type*} (prior : PMF Seed) (execution : Seed → (app).Execution)
    (config : Seed → graph.Config) :
    let traffic := bindingTraffic timeouts leaks focal
    let observe := graph.playerObserve focal
    let honest := turnPolicy timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming graph turns) reference
    let players := Function.update honest focal deviation
    let stop := fun final : (app).Execution => event ∈ final.application.config.cut.completed
    let phase := fun seed => (app).runUntilHorizon scheduler players stop horizon (execution seed)
    ∀ (noise : graph.PlayerObservation focal → PMF _),
      prior.map (fun seed => (config seed, traffic (execution seed))) =
        (prior.map config).bind (fun before =>
          (noise (observe before)).map fun extra => (before, extra)) →
      (∀ seed ∈ prior.support, (config seed).cut.IsPrefix event.val) →
      (∀ seed ∈ prior.support, (execution seed).application.config = State.drainConfig
        (config seed)) →
      (∀ seed ∈ prior.support, owner ∉ (config seed).defaulted →
        PrefixBoundary (inputs.map State.initial) scheduler players event.val (execution seed)) →
      (∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon) →
      ∃ nextNoise : graph.PlayerObservation focal → PMF _,
        (prior.bind phase).map (fun final =>
          (Config.rankPrefix (event.val + 1) final.application.config, traffic final)) =
        (prior.bind fun seed =>
          if ready : (config seed).cut.Ready event then
            eventStep reference (config seed) event ready
          else PMF.pure (config seed)).bind fun primary =>
            (nextNoise (observe primary)).map fun extra => (primary, extra) := by
  intro traffic observe honest players stop phase noise factor ordered native boundary bounded
  have owned : graph.actor? event = some owner := nodeView_bind_actor outputEq codeEq
  apply foreign_owned_checkpoint_primary_traffic_factor scheduler delay bound reference contract
    timely focal owner deviation foreign event owned solitary prior execution config noise factor
    ordered native boundary bounded
  · intro seed _ _ action _
    simp [EffectiveAction, node]
  · intro left leftSupport right rightSupport leftAction _ rightAction _ leftReady rightReady
      leftActive rightActive _ _ leftPrimary leftMoved rightPrimary rightMoved same observed
    let typed := fun action => cast (congrArg EventField.Action outputEq) action
    have back (action : graph.Action event) :
        cast (congrArg EventField.Action outputEq.symm) (typed action) = action := by
      simp [typed]
    have admitted := (foreign_binding_step_observation_eq_iff focal owner foreign event
      outputEq codeEq (config left) (config right) leftPrimary rightPrimary leftReady rightReady
      leftActive rightActive (typed leftAction) (typed rightAction)
      (by rw [back]; exact leftMoved) (by rw [back]; exact rightMoved)).mp same
    have coupled := foreign_binding_fixed_traffic_congr (turns := turns) serial scheduler
      bound reference focal owner deviation foreign event solitary outputEq codeEq node
      (typed leftAction) (typed rightAction) admitted.2 (execution left) (execution right)
      (boundary left leftSupport leftActive) (boundary right rightSupport rightActive)
      (bounded left leftSupport) (bounded right rightSupport) observed
    simpa only [back] using coupled

end Vegas.EventGraphRuntime
