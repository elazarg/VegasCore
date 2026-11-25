module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ChancePhaseTraffic
public import Vegas.Pending.OwnedCompletionConfig
public import Vegas.Pending.FirstTurnSimulation
public import Vegas.EventGraph.PolicyPatch

@[expose] public section

/-! # Transport of a native decision following public chance -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Compose the initialized public chance phase, the focal decision, and the
supplied local reference steps at every later rank. -/
private theorem focal_after_chance_config_law_of_event_steps
    (timeouts : EventTimeouts graph.sequentialize)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    (scheduler : (reactiveApplication timeouts leaks).Scheduler)
    (bound : graph.EventId → Nat) (turns : Nat)
    (timing : EventGraphRuntime.TurnTiming graph.sequentialize turns)
    (inputs : PMF graph.sequentialize.Inputs) (reference : graph.sequentialize.BehavioralProfile)
    (focal : Player) (deviation : (reactiveApplication timeouts leaks).Policy)
    (sample decision : graph.sequentialize.EventId) (sampleRank : sample.val = 0)
    (decisionRank : decision.val = 1)
    (ownerless : graph.sequentialize.actor? sample = none)
    (owned : graph.sequentialize.actor? decision = some focal)
    (only : ∀ other, graph.sequentialize.actor? other = some focal → other = decision)
    (horizon : Nat)
    (completes : CompletesPlay timeouts leaks (inputs.map State.initial) horizon scheduler)
    (localStep :
      let app := reactiveApplication timeouts leaks
      let players := Function.update (turnPolicy timeouts leaks bound turns timing reference)
        focal deviation
      ∀ (event : graph.sequentialize.EventId) (before : app.Execution)
        (boundary : PrefixBoundary (inputs.map State.initial) scheduler players event.val before),
        2 ≤ event.val → before.environmentRecall.length ≤ horizon →
        (app.runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon before).map
            (fun final => final.application.config) =
          (eventStep reference before.application.config event
            (boundary.ordered.ready event.isLt)).map State.drainConfig) :
    let app := reactiveApplication timeouts leaks
    let players := Function.update (turnPolicy timeouts leaks bound turns timing reference)
      focal deviation
    ∃ policy : graph.sequentialize.BehavioralPolicy focal,
      (app.roundsFrom (inputs.map State.initial) scheduler players horizon).map
        (fun final => final.application.config) =
      inputs.bind (graph.sequentialize.runPolicies graph.sequentialize.canonicalScheduler
        (Function.update reference focal policy)) := by
  classical
  intro app players
  let G := graph.sequentialize
  let initial := Config.initial (graph := G)
  let start := fun seed => ReactiveApplication.Execution.initial app (State.initial seed)
  let stopSample := fun final : app.Execution => sample ∈ final.application.config.cut.completed
  let stopDecision := fun final : app.Execution =>
    decision ∈ final.application.config.cut.completed
  let phaseSample := fun seed =>
    app.runUntilHorizon scheduler players stopSample horizon (start seed)
  let phaseDecision := fun execution =>
    app.runUntilHorizon scheduler players stopDecision horizon execution
  let stopped := inputs.bind phaseSample
  let config := fun execution : app.Execution => execution.application.config
  let traffic := (bindingTraffic timeouts) leaks focal
  let plan := G.policyPlan reference G.canonicalScheduler
  let onward := fun current : G.Config => G.runPlan plan current.remaining current
  let action := EventCode.actionOfActorNone (G.nodes sample) ownerless
  have orderedSample : (EventOrder.Cut.empty G.order).IsPrefix sample.val :=
    sampleRank ▸ EventOrder.Cut.empty_isPrefix _
  have readySample : (EventOrder.Cut.empty G.order).Ready sample :=
    orderedSample.ready sample.isLt
  let chance := inputs.bind fun seed => (initial seed).step sample readySample action
  have initialBoundary (seed : G.Inputs) (present : seed ∈ inputs.support) :
      PrefixBoundary (inputs.map State.initial) scheduler players 0 (start seed) :=
    PrefixBoundary.initial _ scheduler players (State.initial seed)
      ((PMF.mem_support_map_iff _ _ _).mpr ⟨seed, present, rfl⟩)
      (EventOrder.Cut.empty_isPrefix _)
  have sampleProgress (seed : G.Inputs) (present : seed ∈ inputs.support)
      (next : app.Execution) (member : next ∈ (phaseSample seed).support) :
      next ∈ (app.roundsFrom (inputs.map State.initial) scheduler players
        next.environmentRecall.length).support ∧
      next.environmentRecall.length ≤ horizon ∧ stopSample next :=
    let progress := runUntilHorizon_event_progress completes sample (start seed) next
      (initialBoundary seed present).supported (Nat.zero_le _) readySample.1 member
    ⟨progress.1, progress.2.1, progress.2.2.1⟩
  obtain ⟨noise, initialFactor⟩ := initial_bindingTraffic_factorization timeouts leaks focal inputs
  obtain ⟨nextNoise, primaryLaw, drained⟩ := chance_primary_traffic_factor timeouts leaks
    (fun event => (graph.sequentialize_solitary event).ownerSolitary) scheduler bound turns
    timing reference focal deviation
    sample ownerless (graph.sequentialize_solitary sample) horizon inputs start
    (fun _ => readySample) noise initialFactor
    (fun seed present next member => (sampleProgress seed present next member).2.2)
  have chanceSupport (next : G.Config) (present : next ∈ chance.support) :
      next.cut.IsPrefix 1 ∧ next.defaulted = ∅ := by
    obtain ⟨seed, _, moved⟩ := (PMF.mem_support_bind_iff _ _ _).mp present
    refine ⟨?_, (Config.step_defaulted_of_actor_none _ _ _ _ _ moved ownerless).trans rfl⟩
    rw [(initial seed).step_cut sample readySample action next moved]
    change ((EventOrder.Cut.empty G.order).complete sample readySample).IsPrefix 1
    simpa only [sampleRank, Nat.zero_add] using
      orderedSample.complete_at sample readySample rfl
  have chanceDrain (next : G.Config) (present : next ∈ chance.support) :
      State.drainConfig next = next := by
    apply State.drainConfig_of_quiescent (State.ofConfig next)
    intro event automatic
    obtain ⟨owner, _, inactive⟩ := automatic.owned
    change owner ∈ next.defaulted at inactive
    rw [(chanceSupport next present).2] at inactive
    exact Finset.notMem_empty owner inactive
  have factor : stopped.map (fun next => (config next, traffic next)) =
      chance.bind (fun next => (nextNoise (G.playerObserve focal next)).map fun extra =>
        (next, extra)) := by
    have transport := congrArg (PMF.map (fun pair : G.Config × BindingTraffic timeouts leaks =>
      (State.drainConfig pair.1, pair.2))) primaryLaw
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at transport
    refine Eq.trans ?_ (transport.trans ?_)
    · rw [PMF.map_bind]
      apply bind_congr_on_support _
      intro seed present
      apply map_congr_on_support _
      intro next member
      exact Prod.ext (drained seed present next member) rfl
    · apply bind_congr_on_support _
      intro next present
      rw [chanceDrain next present]
  have marginal : stopped.map config = chance := by
    have same := congrArg (PMF.map Prod.fst) factor
    simp only [PMF.map_comp, PMF.map_bind, Function.comp_def, pmf_map_fun_const] at same
    exact same.trans (PMF.bind_pure _)
  have postSample (next : app.Execution) (present : next ∈ stopped.support) :=
    chanceSupport (config next) (marginal ▸ (PMF.mem_support_map_iff _ _ _).mpr
      ⟨next, present, rfl⟩)
  have readyDecision (next : app.Execution) (present : next ∈ stopped.support) :
      (config next).cut.Ready decision :=
    ((decisionRank.symm ▸ (postSample next present).1) : (config next).cut.IsPrefix
      decision.val).ready decision.isLt
  have progressDecision (before : app.Execution) (present : before ∈ stopped.support)
      (final : app.Execution) (member : final ∈ (phaseDecision before).support) :
      stopDecision final := by
    obtain ⟨seed, supported, stoppedMember⟩ := (PMF.mem_support_bind_iff _ _ _).mp present
    obtain ⟨seen, bounded, _⟩ := sampleProgress seed supported before stoppedMember
    exact (runUntilHorizon_event_progress completes decision before final seen bounded
      (readyDecision before present).1 member).2.2.1
  obtain ⟨law, decisionLaw⟩ := focal_owned_completed_config_law timeouts leaks scheduler bound
    turns timing reference focal deviation decision owned (graph.sequentialize_solitary decision)
    horizon stopped id nextNoise (factor.trans (by rw [← marginal]; rfl))
    readyDecision
    (fun before present => by
      change focal ∉ (config before).defaulted
      rw [(postSample before present).2]
      exact Finset.notMem_empty _)
    progressDecision
  have suffixLaw := eventCompletionLaw_of_event_steps (scheduler := scheduler)
    (players := players) inputs reference 2 localStep
  have sampleBoundary (seed : G.Inputs) (present : seed ∈ inputs.support) :
      PrefixBoundary (inputs.map State.initial) scheduler players sample.val (start seed) := by
    rw [sampleRank]
    exact initialBoundary seed present
  have boundaryDecision (seed : G.Inputs) (present : seed ∈ inputs.support)
      (before : app.Execution) (member : before ∈ (phaseSample seed).support) :
      PrefixBoundary (inputs.map State.initial) scheduler players decision.val before := by
    obtain ⟨_, rank, _, boundary⟩ := PrefixBoundary.stopped timeouts leaks
      sample (start seed) (sampleBoundary seed present) (Nat.zero_le _) before member
      (sampleProgress seed present before member).2.2
    have supported : before ∈ stopped.support :=
      (PMF.mem_support_bind_iff _ _ _).mpr ⟨seed, present, member⟩
    have rankEq := boundary.ordered.unique (postSample before supported).1
    rwa [rankEq, ← decisionRank] at boundary
  let stoppedDecision := stopped.bind (fun before => (phaseDecision before).map config)
  have native :
      (app.roundsFrom (inputs.map State.initial) scheduler players horizon).map config =
        stoppedDecision.bind onward := by
    unfold stoppedDecision stopped
    rw [ReactiveApplication.roundsFrom, PMF.map_bind, PMF.bind_map, PMF.bind_bind, PMF.bind_bind]
    apply bind_congr_on_support _
    intro seed present
    change (app.runToHorizon scheduler players horizon (start seed)).map config = _
    rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players stopSample, PMF.map_bind]
    apply bind_congr_on_support _
    intro before stoppedMember
    have beforeSupport : before ∈ stopped.support :=
      (PMF.mem_support_bind_iff _ _ _).mpr ⟨seed, present, stoppedMember⟩
    rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players stopDecision, PMF.map_bind,
      PMF.bind_map]
    apply bind_congr_on_support _
    intro final reached
    have done := progressDecision before beforeSupport final reached
    have bounded := (sampleProgress seed present before stoppedMember).2.1
    obtain ⟨within, rank, later, nextBoundary⟩ := PrefixBoundary.stopped timeouts leaks
      decision before (boundaryDecision seed present before stoppedMember) bounded final
      reached done
    have above : 2 ≤ rank := by omega
    have tail := suffixLaw.runToHorizon completes final ⟨rank, above, nextBoundary⟩
      nextBoundary.supported within
    simpa only [Function.comp_def, id_eq, PMF.map_id] using tail
  let policy : G.BehavioralPolicy focal := fun event actor view _ =>
    cast (congrArg (fun current => PMF (G.Action current)) (only event actor).symm) (law view)
  refine ⟨policy, ?_⟩
  let updated := Function.update reference focal policy
  let updatedPlan := G.policyPlan updated G.canonicalScheduler
  have tails (current : G.Config) (done : decision ∈ current.cut.completed) :
      G.runPlan updatedPlan current.remaining current = onward current := by
    have agree (config : G.Config) (event : G.EventId) (different : event ≠ decision) :
        actionLaw updated config event = actionLaw reference config event := by
      change actionLaw (Function.update reference focal policy) config event =
        actionLaw reference config event
      cases actor : G.actor? event with
      | none => rw [actionLaw_of_ownerless _ _ actor, actionLaw_of_ownerless _ _ actor]
      | some owner =>
          have unfocal : owner ≠ focal := fun same => different (only event (same ▸ actor))
          rw [actionLaw_of_actor _ _ actor, actionLaw_of_actor _ _ actor]
          by_cases inactive : owner ∈ config.defaulted
          · rw [dite_eq_left inactive, dite_eq_left inactive]
          · rw [dite_eq_right inactive, dite_eq_right inactive,
              Function.update_of_ne unfocal]
    exact runPlan_congr_of_actionLaw G.canonicalScheduler (fun event => event = decision)
      agree current.remaining current (fun _ same => same.symm ▸ done)
  let finish (before : G.Config) :=
    if ready : before.cut.Ready decision then
      (law (G.playerObserve focal before)).bind fun chosen =>
        (before.step decision ready chosen).map State.drainConfig
    else PMF.pure before
  have focalLaw : stoppedDecision = chance.bind finish := by
    change stoppedDecision = chance.bind _
    rw [← marginal, PMF.bind_map]
    exact decisionLaw
  rw [native, focalLaw, PMF.bind_bind]
  unfold chance
  rw [PMF.bind_bind]
  apply bind_congr_on_support _
  intro seed present
  change ((initial seed).step sample readySample action).bind
      (fun before => (finish before).bind onward) =
    G.runPlan updatedPlan (initial seed).remaining (initial seed)
  have leastSample (other : G.EventId) (_ : (initial seed).cut.Ready other) : sample ≤ other :=
    Fin.le_iff_val_le_val.mpr (by rw [sampleRank]; exact Nat.zero_le _)
  rw [runPlan_remaining_canonical_step _ (initial seed) sample readySample leastSample,
    eventStep, actionLaw_of_ownerless _ _ ownerless, PMF.pure_bind]
  apply bind_congr_on_support _
  intro before member
  have beforeSupport : before ∈ chance.support :=
    (PMF.mem_support_bind_iff _ _ _).mpr ⟨seed, present, member⟩
  have ordered : before.cut.IsPrefix decision.val :=
    decisionRank ▸ (chanceSupport before beforeSupport).1
  have ready : before.cut.Ready decision := ordered.ready decision.isLt
  have active : focal ∉ before.defaulted := by
    rw [(chanceSupport before beforeSupport).2]
    exact Finset.notMem_empty _
  have leastDecision (other : G.EventId) (enabled : before.cut.Ready other) :
      decision ≤ other :=
    Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt fun earlier =>
      enabled.1 ((ordered.2 other).mpr earlier))
  rw [runPlan_remaining_canonical_step _ before decision ready leastDecision,
    eventStep, actionLaw_of_actor _ _ owned, dite_eq_right active]
  simp only [finish, dite_eq_left ready, updated, Function.update_self, policy, cast_eq,
    PMF.bind_bind]
  apply bind_congr_on_support _
  intro chosen _
  rw [PMF.bind_map]
  apply bind_congr_on_support _
  intro after moved
  have done : decision ∈ after.cut.completed := by
    rw [before.step_cut decision ready chosen after moved, EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  have drained : onward (State.drainConfig after) = onward after :=
    (State.drain_runPlan_canonical graph reference (State.ofConfig after)).symm
  exact drained.trans (tails after done).symm

/-- In a two-event sequential graph with a public chance event followed by one
owned decision, every raw deviation has an observation-local graph realization
with the exact full terminal configuration law. -/
theorem focal_after_chance_config_law
    (timeouts : EventTimeouts graph.sequentialize)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    (scheduler : (reactiveApplication timeouts leaks).Scheduler)
    (bound : graph.EventId → Nat) (turns : Nat)
    (timing : EventGraphRuntime.TurnTiming graph.sequentialize turns)
    (inputs : PMF graph.sequentialize.Inputs) (reference : graph.sequentialize.BehavioralProfile)
    (focal : Player) (deviation : (reactiveApplication timeouts leaks).Policy)
    (sample decision : graph.sequentialize.EventId) (sampleRank : sample.val = 0)
    (decisionRank : decision.val = 1) (count : graph.order.eventCount = 2)
    (ownerless : graph.sequentialize.actor? sample = none)
    (owned : graph.sequentialize.actor? decision = some focal)
    (horizon : Nat)
    (completes : CompletesPlay timeouts leaks (inputs.map State.initial) horizon scheduler) :
    let app := reactiveApplication timeouts leaks
    let players := Function.update (turnPolicy timeouts leaks bound turns timing reference)
      focal deviation
    ∃ policy : graph.sequentialize.BehavioralPolicy focal,
      (app.roundsFrom (inputs.map State.initial) scheduler players horizon).map
        (fun final => final.application.config) =
      inputs.bind (graph.sequentialize.runPolicies graph.sequentialize.canonicalScheduler
        (Function.update reference focal policy)) := by
  apply focal_after_chance_config_law_of_event_steps timeouts leaks scheduler bound turns timing
    inputs reference focal deviation sample decision sampleRank decisionRank ownerless owned
    ?_ horizon completes ?_
  · intro other actor
    have inside := other.isLt
    change other.val < graph.order.eventCount at inside
    have nonzero : other.val ≠ 0 := by
      intro zero
      have same : other = sample := Fin.ext (zero.trans sampleRank.symm)
      rw [same, ownerless] at actor
      cases actor
    exact Fin.ext (by omega)
  · intro _ _ event _ _ later _
    have inside := event.isLt
    change event.val < graph.order.eventCount at inside
    omega

/-- If public chance precedes the focal player's sole decision, all subsequent
foreign and chance events retain their canonical continuation law. -/
theorem focal_after_chance_config_law_with_suffix
    (timeouts : EventTimeouts graph.sequentialize)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    (scheduler : (reactiveApplication timeouts leaks).Scheduler)
    (bound : graph.EventId → Nat) (turns : Nat)
    (delay : graph.sequentialize.EventId → Nat)
    (inputs : PMF graph.sequentialize.Inputs) (reference : graph.sequentialize.BehavioralProfile)
    (focal : Player) (deviation : (reactiveApplication timeouts leaks).Policy)
    (sample decision : graph.sequentialize.EventId) (sampleRank : sample.val = 0)
    (decisionRank : decision.val = 1)
    (ownerless : graph.sequentialize.actor? sample = none)
    (owned : graph.sequentialize.actor? decision = some focal)
    (only : ∀ other, graph.sequentialize.actor? other = some focal → other = decision)
    (horizon : Nat)
    (contract : AsyncContract timeouts leaks (inputs.map State.initial) horizon scheduler
      delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (realizable : RealizableProfile (graph := graph.sequentialize) inputs reference) :
    let app := reactiveApplication timeouts leaks
    let players := Function.update (turnPolicy timeouts leaks bound turns
      (EventGraphRuntime.firstTurnTiming graph.sequentialize turns) reference)
      focal deviation
    ∃ policy : graph.sequentialize.BehavioralPolicy focal,
      (app.roundsFrom (inputs.map State.initial) scheduler players horizon).map
        (fun final => final.application.config) =
      inputs.bind (graph.sequentialize.runPolicies graph.sequentialize.canonicalScheduler
        (Function.update reference focal policy)) := by
  intro app players
  let timing := EventGraphRuntime.firstTurnTiming graph.sequentialize turns
  refine focal_after_chance_config_law_of_event_steps timeouts leaks scheduler bound turns timing
    inputs reference focal deviation sample decision sampleRank decisionRank ownerless owned only
    horizon contract.completes ?_
  intro _ _ event before boundary later within
  refine firstTurn_event_config_law_of_owner_follows timeouts leaks (turns := turns)
    scheduler delay bound inputs reference contract timely realizable event players
    ?_ before boundary within
  intro who actor
  have unfocal : who ≠ focal := by
    rintro rfl
    have equal := only event actor
    rw [equal, decisionRank] at later
    omega
  exact Function.update_of_ne unfocal _ _

end Vegas.EventGraphRuntime
