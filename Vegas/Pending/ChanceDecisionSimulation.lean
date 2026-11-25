module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ChancePhaseTraffic
public import Vegas.Pending.OwnedCompletionConfig
public import Vegas.Pending.PrefixBoundary

@[expose] public section

/-! # Transport of a native decision following public chance -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

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
  have allEvents (event : G.EventId) : event = sample ∨ event = decision := by
    have inside := event.isLt
    change event.val < graph.order.eventCount at inside
    rcases show event.val = 0 ∨ event.val = 1 by omega with zero | one
    · exact Or.inl (Fin.ext (zero.trans sampleRank.symm))
    · exact Or.inr (Fin.ext (one.trans decisionRank.symm))
  have terminal (final : G.Config) (sampleDone : sample ∈ final.cut.completed)
      (decisionDone : decision ∈ final.cut.completed) : final.cut.Terminal := by
    apply Finset.eq_univ_iff_forall.mpr
    intro event
    rcases allEvents event with rfl | rfl <;> assumption
  have native :
      (app.roundsFrom (inputs.map State.initial) scheduler players horizon).map config =
        stopped.bind (fun before => (phaseDecision before).map config) := by
    rw [ReactiveApplication.roundsFrom, PMF.map_bind, PMF.bind_map, PMF.bind_bind]
    apply bind_congr_on_support _
    intro seed present
    change (app.runToHorizon scheduler players horizon (start seed)).map config = _
    rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players stopSample, PMF.map_bind]
    apply bind_congr_on_support _
    intro before stoppedMember
    have beforeSupport : before ∈ stopped.support :=
      (PMF.mem_support_bind_iff _ _ _).mpr ⟨seed, present, stoppedMember⟩
    rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players stopDecision, PMF.map_bind,
      ← PMF.bind_pure_comp]
    apply bind_congr_on_support _
    intro final reached
    have afterDecision := progressDecision before beforeSupport final reached
    have retained := EventGraph.Config.Step.path_completed_mono
      (reactive_runUntil_graph_steps timeouts leaks scheduler players stopDecision
        (horizon - before.environmentRecall.length) before final reached)
      (sampleProgress seed present before stoppedMember).2.2
    have finished := terminal _ retained afterDecision
    change (app.runRounds scheduler players _ final).map config = PMF.pure (config final)
    rw [map_congr_on_support _ (g := fun _ => config final) (fun last reached =>
      Config.Step.path_eq_of_terminal
        (reactive_runRounds_graph_steps timeouts leaks scheduler players _ final last reached)
          finished), pmf_map_fun_const]
  let policy : G.BehavioralPolicy focal := fun event actor view _ =>
    cast (congrArg (fun current => PMF (G.Action current)) (by
      rcases allEvents event with same | same
      · rw [same, ownerless] at actor
        cases actor
      · exact same.symm)) (law view)
  refine ⟨policy, ?_⟩
  let updated := Function.update reference focal policy
  let plan := G.policyPlan updated G.canonicalScheduler
  have ideal : inputs.bind (G.runPolicies G.canonicalScheduler updated) =
      chance.bind (fun before =>
        if ready : before.cut.Ready decision then
          (law (G.playerObserve focal before)).bind fun chosen =>
            (before.step decision ready chosen).map State.drainConfig
        else PMF.pure before) := by
    rw [PMF.bind_bind]
    apply bind_congr_on_support _
    intro seed present
    change G.runPlan plan graph.order.eventCount (initial seed) = _
    have leastSample (other : G.EventId) (_ : (initial seed).cut.Ready other) : sample ≤ other :=
      Fin.le_iff_val_le_val.mpr (by rw [sampleRank]; exact Nat.zero_le _)
    rw [count, show 2 = 1 + 1 from rfl, runPlan_canonical_succ _ 1 (initial seed)
      readySample.not_terminal sample readySample leastSample,
      eventStep, actionLaw_of_ownerless _ _ ownerless, PMF.pure_bind]
    apply bind_congr_on_support _
    intro before member
    have beforeSupport : before ∈ chance.support :=
      (PMF.mem_support_bind_iff _ _ _).mpr ⟨seed, present, member⟩
    have ordered : before.cut.IsPrefix decision.val :=
      decisionRank ▸ (chanceSupport before beforeSupport).1
    have ready : before.cut.Ready decision := ordered.ready decision.isLt
    have active : focal ∉ before.defaulted := by
      rw [(chanceSupport before beforeSupport).2]; exact Finset.notMem_empty _
    have leastDecision (other : G.EventId) (enabled : before.cut.Ready other) :
        decision ≤ other :=
      Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt fun earlier =>
        enabled.1 ((ordered.2 other).mpr earlier))
    rw [runPlan_canonical_succ _ 0 before ready.not_terminal decision ready leastDecision,
      eventStep, actionLaw_of_actor _ _ owned, dite_eq_right active, dite_eq_left ready]
    simp only [EventGraph.runPlan, PMF.bind_pure, updated, Function.update_self, policy, cast_eq]
    apply bind_congr_on_support _
    intro chosen _
    symm
    rw [map_congr_on_support _ (g := id) ?_, PMF.map_id]
    intro final moved
    apply State.drainConfig_of_quiescent (State.ofConfig final)
    intro event automatic
    have orderedFinal : final.cut.IsPrefix graph.order.eventCount := by
      have finalPrefix := ordered.complete_at decision ready rfl
      rw [before.step_cut decision ready chosen final moved]
      simpa only [decisionRank, count] using finalPrefix
    exact automatic.1.not_terminal orderedFinal.terminal
  rw [native, ideal]
  change stopped.bind (fun before => (phaseDecision before).map config) = _
  rw [← marginal, PMF.bind_map]
  exact decisionLaw

end Vegas.EventGraphRuntime
