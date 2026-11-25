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
private theorem accepted_opening_value (config : graph.Config)
    (accepted : openingAccepted event config.store = true) :
    ∃ value, binding.get? config.store = some (.success value) ∧
      EventCode.resolveOutput? binding checks true config.store = some (.success value) := by
  obtain ⟨value, resolved⟩ :
      ∃ value, EventCode.resolveOutput? binding checks true config.store =
        some (.success value) := by
    simp only [openingAccepted, node] at accepted
    cases stored : EventCode.resolveOutput? binding checks true config.store with
    | none => simp [stored] at accepted
    | some output =>
      cases output with
      | failure => simp [stored] at accepted
      | success value => exact ⟨value, rfl⟩
  refine ⟨value, ?_, resolved⟩
  cases stored : binding.get? config.store with
  | none => simp [EventCode.resolveOutput?, stored] at resolved
  | some bound =>
    cases guards : GuardCheck.allAccepted? checks config.store bound with
    | none => simp [EventCode.resolveOutput?, stored, guards] at resolved
    | some admitted =>
      cases admitted with
      | false => simp [EventCode.resolveOutput?, stored, guards] at resolved
      | true =>
        have equal : bound = .success value := by
          simpa [EventCode.resolveOutput?, stored, guards] using resolved
        exact congrArg some equal

private theorem effective_disclosure_accepted
    (base : graph.BehavioralProfile) (config : graph.Config)
    (active : owner ∉ config.defaulted) (action : graph.Action event)
    (chosen : action ∈ (actionLaw (effectiveOpening base) config event).support)
    (disclose : (cast (congrArg EventField.Action outputEq) action : Bool) = true) :
    openingAccepted event config.store = true := by
  let owned := nodeView_resolve_actor outputEq codeEq
  rw [actionLaw_of_actor _ _ owned, dite_eq_right active,
    effectiveOpening_of_resolve base node owned, PMF.mem_support_pure_iff] at chosen
  change action = cast (congrArg EventField.Action outputEq.symm)
    (openingAccepted event (graph.playerStore owner config.store)) at chosen
  rw [openingAccepted_playerStore event owned] at chosen
  rw [chosen] at disclose
  simpa using disclose

/-- The effective-opening law only prescribes realizable actions at active publications. -/
theorem effectiveOpening_publication_realizable
    (base : graph.BehavioralProfile) (config : graph.Config) (active : owner ∉ config.defaulted)
    (action : graph.Action event)
    (chosen : action ∈ (actionLaw (effectiveOpening base) config event).support) :
    EffectiveAction config event action := by
  simp only [EffectiveAction, node]
  intro disclose
  obtain ⟨value, stored, _⟩ := accepted_opening_value node config
    (effective_disclosure_accepted node base config active action chosen disclose)
  exact ⟨value, stored⟩

private theorem effective_publication_disclosed_value
    (base : graph.BehavioralProfile) (config next : graph.Config)
    (ready : config.cut.Ready event) (active : owner ∉ config.defaulted)
    (action : graph.Action event)
    (chosen : action ∈ (actionLaw (effectiveOpening base) config event).support)
    (moved : next ∈ (config.step event ready action).support)
    (disclose : (cast (congrArg EventField.Action outputEq) action : Bool) = true) :
    ∃ value, binding.get? config.store = some (.success value) ∧
      next.outputs event = some (cast (congrArg EventField.Value outputEq.symm) (.success value)) :=
    by
  obtain ⟨value, stored, resolved⟩ := accepted_opening_value node config
    (effective_disclosure_accepted node base config active action chosen disclose)
  have actionEq : action = cast (congrArg EventField.Action outputEq.symm) true := by
    rw [← disclose, cast_cast, cast_eq]
  have evaluates : (EventCode.resolve owner payload binding checks).eval?
      ((EventCode.resolve owner payload binding checks).effectiveAction config.defaulted true)
        config.store = some (PMF.pure (.success value)) := by
    simp only [EventCode.effectiveAction, EventCode.actor, ite_eq_right active,
      EventCode.resolve_eval?, resolved, Option.map_some]
  rw [actionEq, config.step_eq_map_of_code event ready outputEq _ codeEq true _
    evaluates, PMF.pure_map, PMF.mem_support_pure_iff] at moved
  exact ⟨value, stored, moved ▸ Config.complete_output_same ..⟩

/-- Equal observations of two effective foreign publications identify the
same prescribed disclosure. If they disclose, both immutable bindings hold
the same publicly written value. -/
theorem foreign_effective_publication_choices_agree
    (base : graph.BehavioralProfile)
    (focal : Player) (foreign : owner ≠ focal)
    (left right leftNext rightNext : graph.Config)
    (leftReady : left.cut.Ready event) (rightReady : right.cut.Ready event)
    (leftActive : owner ∉ left.defaulted) (rightActive : owner ∉ right.defaulted)
    (leftAction rightAction : graph.Action event)
    (leftChosen : leftAction ∈ (actionLaw (effectiveOpening base) left event).support)
    (rightChosen : rightAction ∈ (actionLaw (effectiveOpening base) right event).support)
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
  have leftDecoded := effectiveOpening_publication_action_from_output base left leftNext
    event leftReady node leftAction leftChosen leftMoved
  have rightDecoded := effectiveOpening_publication_action_from_output base right rightNext
    event rightReady node rightAction rightChosen rightMoved
  rw [publicResult] at leftDecoded
  have disclosed : decode leftAction = decode rightAction := leftDecoded.trans rightDecoded.symm
  refine ⟨disclosed, ?_⟩
  intro sends
  obtain ⟨leftValue, leftStored, leftOutput⟩ := effective_publication_disclosed_value node base
    left leftNext leftReady leftActive leftAction leftChosen leftMoved sends
  obtain ⟨rightValue, rightStored, rightOutput⟩ := effective_publication_disclosed_value node base
    right rightNext rightReady rightActive rightAction rightChosen rightMoved
    (disclosed.symm.trans sends)
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

/-- At a foreign effective publication, the stopped native execution has the
drained reference successor law jointly with observation-local traffic.
Already-defaulted heads advance without a new native round. -/
theorem foreign_publication_checkpoint_successor_traffic_factor
    (serial : graph.ActorSerial)
    {horizon turns : Nat} (scheduler : (app).Scheduler)
    (delay bound : graph.EventId → Nat) (base : graph.BehavioralProfile)
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
    let reference := effectiveOpening base
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
        (prior.bind fun seed => (phase seed).map fun final =>
          (final.application.config, traffic final)) =
        (prior.bind fun seed =>
          if ready : (config seed).cut.Ready event then
            (eventStep reference (config seed) event ready).bind fun primary =>
              (nextNoise (observe primary)).map fun extra => (State.drainConfig primary, extra)
          else PMF.pure (config seed, traffic (execution seed))) := by
  intro reference traffic observe honest players stop phase noise factor ordered native
    boundary bounded
  have owned := nodeView_resolve_actor outputEq codeEq
  apply foreign_owned_checkpoint_successor_traffic_factor scheduler delay bound reference
    contract timely focal owner deviation foreign event owned solitary prior execution config
    noise factor ordered native boundary bounded
  · intro seed _ active action chosen
    exact effectiveOpening_publication_realizable node base (config seed) active action chosen
  · intro left leftSupport right rightSupport leftAction leftChosen rightAction rightChosen
      leftReady rightReady leftActive rightActive leftAligned rightAligned leftNext leftMoved
      rightNext rightMoved same observed
    let decode := fun action => (cast (congrArg EventField.Action outputEq) action : Bool)
    obtain ⟨agrees, values⟩ := foreign_effective_publication_choices_agree node base focal foreign
      (config left) (config right) leftNext rightNext leftReady rightReady leftActive rightActive
      leftAction rightAction leftChosen rightChosen leftMoved rightMoved same
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
theorem foreign_publication_checkpoint_primary_traffic_factor
    (serial : graph.ActorSerial)
    {horizon turns : Nat} (scheduler : (app).Scheduler)
    (delay bound : graph.EventId → Nat) (base : graph.BehavioralProfile)
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
    let reference := effectiveOpening base
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
  intro reference traffic observe honest players stop phase noise factor ordered native
    boundary bounded
  obtain ⟨nextNoise, joint⟩ := foreign_publication_checkpoint_successor_traffic_factor serial
    scheduler delay bound base contract timely focal owner deviation foreign event solitary
    binding checks outputEq codeEq node prior execution config noise factor ordered native
    boundary bounded
  exact ⟨nextNoise, primary_rank_traffic_of_checkpoint_law prior phase config (fun final =>
    final.application.config) execution traffic observe event reference nextNoise ordered joint⟩

end Checkpoints

section PhysicalPrefix

variable {timeouts : EventTimeouts graph.sequentialize}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize)}

local notation "G" => graph.sequentialize
local notation "app" => reactiveApplication timeouts leaks

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
  apply foreign_physicalPrefix_policyStep scheduler players inputs horizon reference
    focal owner event (nodeView_resolve_actor outputEq codeEq) contract.completes
  exact foreign_publication_checkpoint_primary_traffic_factor (graph := graph.sequentialize)
    (timeouts := timeouts) (leaks := leaks)
    (fun next => (graph.sequentialize_solitary next).ownerSolitary)
    scheduler delay bound base contract timely focal owner deviation foreign event
    (graph.sequentialize_solitary event) binding checks outputEq codeEq node
    (physicalPrefix timeouts leaks scheduler players inputs horizon event.val)
    id (fun execution => Config.rankPrefix event.val execution.application.config)

end PhysicalPrefix

end Vegas.EventGraphRuntime
