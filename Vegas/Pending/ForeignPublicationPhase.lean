module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ForeignPublicationObservation
public import Vegas.Pending.ForeignOwnedPhase
public import Vegas.Pending.ForeignPublicationTraffic
public import Vegas.Pending.ForeignPolicyStep

@[expose] public section

/-! # Observation-local traffic at a foreign effective publication -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

section EffectivePublication

variable {event : graph.EventId} {owner : Player} {payload : L.Ty}
  {binding : FieldRef graph.layout (.binding owner payload)}
  {checks : List (GuardCheck graph.layout payload)}
  {outputEq : graph.outputLayout event = .publication payload}
  {codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
    .resolve owner payload binding checks}
  (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)

include node

omit [DecidableEq Player] in
private theorem publication_realizable_of_safe
    (config : graph.Config) (action : graph.Action event)
    (safe : (cast (congrArg EventField.Action outputEq) action : Bool) = true →
      openingAccepted event config.store = true) :
    EffectiveAction config event action := by
  simp only [EffectiveAction, node]
  intro disclose
  obtain ⟨value, stored, _⟩ := openingAccepted_value node config (safe disclose)
  exact ⟨value, stored⟩

/-- Equal observations of two safe foreign publications identify the
same prescribed disclosure. If they disclose, both immutable bindings hold
the same publicly written value. -/
private theorem foreign_safe_publication_choices_agree
    (focal : Player) (foreign : owner ≠ focal)
    (left right leftNext rightNext : graph.Config)
    (leftReady : left.cut.Ready event) (rightReady : right.cut.Ready event)
    (leftActive : owner ∉ left.defaulted) (rightActive : owner ∉ right.defaulted)
    (leftAction rightAction : graph.Action event)
    (leftSafe : (cast (congrArg EventField.Action outputEq) leftAction : Bool) = true →
      openingAccepted event left.store = true)
    (rightSafe : (cast (congrArg EventField.Action outputEq) rightAction : Bool) = true →
      openingAccepted event right.store = true)
    (leftMoved : leftNext ∈ (left.step event leftReady leftAction).support)
    (rightMoved : rightNext ∈ (right.step event rightReady rightAction).support)
    (same : graph.playerObserve focal leftNext = graph.playerObserve focal rightNext) :
    let decode := fun action => (cast (congrArg EventField.Action outputEq) action : Bool)
    decode leftAction = decode rightAction ∧
      (decode leftAction = true → ∃ value, binding.get? left.store = some (.success value) ∧
        binding.get? right.store = some (.success value)) := by
  intro decode
  have publicResult := (foreign_publication_step_observation_eq_iff focal owner foreign event
    outputEq codeEq left right leftNext rightNext leftReady rightReady leftAction rightAction
    leftMoved rightMoved).mp same |>.2
  have leftDecoded := publication_action_from_output_of_safe left leftNext event leftReady
    node leftAction (fun disclosed => ⟨leftActive, leftSafe disclosed⟩) leftMoved
  have rightDecoded := publication_action_from_output_of_safe right rightNext event rightReady
    node rightAction (fun disclosed => ⟨rightActive, rightSafe disclosed⟩) rightMoved
  rw [publicResult] at leftDecoded
  have disclosed : decode leftAction = decode rightAction := leftDecoded.trans rightDecoded.symm
  refine ⟨disclosed, ?_⟩
  intro sends
  have rightSends := disclosed.symm.trans sends
  obtain ⟨leftValue, leftStored, leftOutput⟩ := publication_disclosed_value_of_accepted node
    left leftNext leftReady leftActive leftAction leftMoved sends (leftSafe sends)
  obtain ⟨rightValue, rightStored, rightOutput⟩ := publication_disclosed_value_of_accepted node
    right rightNext rightReady rightActive rightAction rightMoved rightSends (rightSafe rightSends)
  rw [leftOutput, rightOutput] at publicResult
  have values := congrArg (cast (congrArg EventField.Value outputEq)) (Option.some.inj publicResult)
  simp only [cast_cast, cast_eq, PublicationResult.success.injEq] at values
  exact ⟨leftValue, leftStored, by simpa only [values] using rightStored⟩

end EffectivePublication

section Checkpoints

variable {timeouts : EventTimeouts graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {inputs : PMF graph.Inputs}

local notation "app" => reactiveApplication timeouts leaks

/-- At a safe foreign publication, the stopped native execution has the
drained reference successor law jointly with observation-local traffic.
Already-defaulted heads advance without a new native round. -/
theorem foreign_safe_publication_checkpoint_successor_traffic_factor
    (serial : graph.ActorSerial)
    {horizon turns : Nat} (scheduler : (app).Scheduler)
    (delay bound : graph.EventId → Nat) (reference : graph.BehavioralProfile)
    (contract : AsyncContract timeouts leaks (inputs.map State.initial) horizon scheduler
      delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (focal owner : Player) (deviation : (app).Policy) (foreign : owner ≠ focal)
    (event : graph.EventId) (solitary : graph.Solitary event) {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
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
      (∀ seed ∈ prior.support, owner ∉ (config seed).defaulted →
        ∀ action ∈ (actionLaw reference (config seed) event).support,
          (cast (congrArg EventField.Action outputEq) action : Bool) = true →
            openingAccepted event (config seed).store = true) →
      ∃ nextNoise : graph.PlayerObservation focal → PMF _,
        (prior.bind fun seed => (phase seed).map fun final =>
          (final.application.config, traffic final)) =
        (prior.bind fun seed =>
          if ready : (config seed).cut.Ready event then
            (eventStep reference (config seed) event ready).bind fun primary =>
              (nextNoise (observe primary)).map fun extra => (State.drainConfig primary, extra)
          else PMF.pure (config seed, traffic (execution seed))) := by
  intro traffic observe honest players stop phase noise factor ordered native boundary bounded safe
  have owned := nodeView_resolve_actor outputEq codeEq
  apply foreign_owned_checkpoint_successor_traffic_factor scheduler delay bound reference
    contract timely focal owner deviation foreign event owned solitary prior execution config
    noise factor ordered native boundary bounded
  · intro seed supported active action chosen
    exact publication_realizable_of_safe node (config seed) action
      (safe seed supported active action chosen)
  · intro left leftSupport right rightSupport leftAction leftChosen rightAction rightChosen
      leftReady rightReady leftActive rightActive leftAligned rightAligned leftNext leftMoved
      rightNext rightMoved same observed
    let decode := fun action => (cast (congrArg EventField.Action outputEq) action : Bool)
    obtain ⟨agrees, values⟩ := foreign_safe_publication_choices_agree node focal foreign
      (config left) (config right) leftNext rightNext leftReady rightReady leftActive rightActive
      leftAction rightAction (safe left leftSupport leftActive leftAction leftChosen)
      (safe right rightSupport rightActive rightAction rightChosen) leftMoved rightMoved same
    have stored (sends : decode leftAction = true) : ∃ value,
        binding.get? (execution left).application.config.store = some (.success value) ∧
        binding.get? (execution right).application.config.store = some (.success value) := by
      rw [leftAligned, rightAligned]
      exact values sends
    have coupled := foreign_publication_fixed_traffic_congr serial scheduler bound turns
      (EventGraphRuntime.firstTurnTiming graph turns) reference focal owner deviation foreign
      event solitary binding checks outputEq codeEq node (decode leftAction) (execution left)
      (execution right) stored (boundary left leftSupport leftActive)
      (boundary right rightSupport rightActive) (bounded left leftSupport)
      (bounded right rightSupport) observed
    have equalAction : leftAction = rightAction := by
      have equal := congrArg (cast (congrArg EventField.Action outputEq.symm)) agrees
      simpa [decode] using equal
    have castBack :
        cast (congrArg EventField.Action outputEq.symm) (decode leftAction) = leftAction := by
      simp [decode]
    rw [castBack] at coupled
    simpa only [← equalAction] using coupled

/-- Project the stopped foreign publication to its single primary graph rank,
retaining the actual stopped traffic of the ledger. -/
theorem foreign_safe_publication_checkpoint_primary_traffic_factor
    (serial : graph.ActorSerial)
    {horizon turns : Nat} (scheduler : (app).Scheduler)
    (delay bound : graph.EventId → Nat) (reference : graph.BehavioralProfile)
    (contract : AsyncContract timeouts leaks (inputs.map State.initial) horizon scheduler
      delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (focal owner : Player) (deviation : (app).Policy) (foreign : owner ≠ focal)
    (event : graph.EventId) (solitary : graph.Solitary event) {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
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
      (∀ seed ∈ prior.support, owner ∉ (config seed).defaulted →
        ∀ action ∈ (actionLaw reference (config seed) event).support,
          (cast (congrArg EventField.Action outputEq) action : Bool) = true →
            openingAccepted event (config seed).store = true) →
      ∃ nextNoise : graph.PlayerObservation focal → PMF _,
        (prior.bind phase).map (fun final =>
          (Config.rankPrefix (event.val + 1) final.application.config, traffic final)) =
        (prior.bind fun seed =>
          if ready : (config seed).cut.Ready event then
            eventStep reference (config seed) event ready
          else PMF.pure (config seed)).bind fun primary =>
            (nextNoise (observe primary)).map fun extra => (primary, extra) := by
  intro traffic observe honest players stop phase noise factor ordered native boundary bounded safe
  obtain ⟨nextNoise, joint⟩ := foreign_safe_publication_checkpoint_successor_traffic_factor serial
    scheduler delay bound reference contract timely focal owner deviation foreign event solitary
    binding checks outputEq codeEq node prior execution config noise factor ordered native
    boundary bounded safe
  exact ⟨nextNoise, primary_rank_traffic_of_checkpoint_law prior phase config (fun final =>
    final.application.config) execution traffic observe event reference nextNoise ordered joint⟩

end Checkpoints

section PhysicalPrefix

variable {timeouts : EventTimeouts graph.sequentialize}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize)}

local notation "G" => graph.sequentialize
local notation "app" => reactiveApplication timeouts leaks

/-- A foreign reference realizes its policy step when every supported
disclosure at the active, reachable head is accepted. It may still withhold
when an opening would succeed. -/
theorem physicalPrefix_foreign_safe_publication_policyStep
    {horizon turns : Nat} (scheduler : (app).Scheduler)
    (delay bound : (G).EventId → Nat) (inputs : PMF (G).Inputs)
    (reference : (G).BehavioralProfile)
    (contract : AsyncContract timeouts leaks (inputs.map State.initial) horizon scheduler
      delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (focal owner : Player) (deviation : (app).Policy) (foreign : owner ≠ focal)
    (event : (G).EventId) {payload : L.Ty}
    (binding : FieldRef (G).layout (.binding owner payload))
    (checks : List (GuardCheck (G).layout payload))
    (outputEq : (G).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (G).layout) outputEq) ((G).nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView (G) event = .resolve owner payload binding checks outputEq codeEq)
    (safe : ∀ initial ∈ inputs.support, ∀ config : (G).Config, config.Reachable initial →
      config.cut.Ready event → owner ∉ config.defaulted →
      ∀ action ∈ (actionLaw reference config event).support,
        (cast (congrArg EventField.Action outputEq) action : Bool) = true →
          openingAccepted event config.store = true) :
    let players := Function.update (turnPolicy timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming G turns) reference) focal deviation
    PhysicalPrefixPolicyStep scheduler players inputs horizon reference focal event := by
  intro players
  have owned := nodeView_resolve_actor outputEq codeEq
  have solitary := graph.sequentialize_solitary event
  apply foreign_physicalPrefix_policyStep scheduler players inputs horizon reference
    focal owner event owned contract.completes
  intro noise factor ordered native boundary bounded
  apply foreign_safe_publication_checkpoint_primary_traffic_factor (graph := graph.sequentialize)
    (timeouts := timeouts) (leaks := leaks)
    (fun next => (graph.sequentialize_solitary next).ownerSolitary)
    scheduler delay bound reference contract timely focal owner deviation foreign event
    solitary binding checks outputEq codeEq node
    (physicalPrefix timeouts leaks scheduler players inputs horizon event.val)
    id (fun execution => Config.rankPrefix event.val execution.application.config)
    noise factor ordered native boundary bounded
  intro execution supported active action chosen disclosed
  obtain ⟨trace⟩ := (app).raw_trace_roundsFrom (inputs.map State.initial) horizon scheduler players
    execution.environmentRecall.length (bounded execution supported) execution
    (boundary execution supported active).supported
  obtain ⟨initial, initialSupported, invariant⟩ :=
    reactive_history_invariant timeouts leaks inputs horizon scheduler trace
  let checkpoint := Config.rankPrefix event.val execution.application.config
  have ready : checkpoint.cut.Ready event := (ordered execution supported).ready event.isLt
  have aligned : execution.application.config = checkpoint := by
    refine (native execution supported).trans
      (State.drainConfig_of_quiescent (State.ofConfig checkpoint) ?_)
    intro other automatic
    have same := solitary _ automatic.1 ready
    subst other
    have inactive := automatic.2
    rw [owned] at inactive
    exact active inactive
  exact safe initial initialSupported checkpoint (aligned ▸ invariant.reachable) ready active
    action chosen disclosed

/-- The effective-opening reference realizes the foreign publication policy
step on actual physical prefixes, also across already-drained ranks. -/
theorem physicalPrefix_foreign_publication_policyStep
    {horizon turns : Nat} (scheduler : (app).Scheduler)
    (delay bound : (G).EventId → Nat) (inputs : PMF (G).Inputs)
    (base : (G).BehavioralProfile)
    (contract : AsyncContract timeouts leaks (inputs.map State.initial) horizon scheduler
      delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (focal owner : Player) (deviation : (app).Policy) (foreign : owner ≠ focal)
    (event : (G).EventId) {payload : L.Ty}
    (binding : FieldRef (G).layout (.binding owner payload))
    (checks : List (GuardCheck (G).layout payload))
    (outputEq : (G).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (G).layout) outputEq) ((G).nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView (G) event = .resolve owner payload binding checks outputEq codeEq) :
    let reference := effectiveOpening base
    let players := Function.update (turnPolicy timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming G turns) reference) focal deviation
    PhysicalPrefixPolicyStep scheduler players inputs horizon reference focal event := by
  intro reference players
  exact physicalPrefix_foreign_safe_publication_policyStep scheduler delay bound inputs reference
    contract timely focal owner deviation foreign event binding checks outputEq codeEq node
    (fun _ _ config _ _ _ action chosen disclose =>
      (effectiveOpening_publication_disclosure_safe node base config action chosen disclose).2)

end PhysicalPrefix

end Vegas.EventGraphRuntime
