module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.FirstTurnSimulation
public import Vegas.Pending.OwnedCompletionConfig
public import Vegas.EventGraph.PolicyPatch

@[expose] public section

/-! # Initial unilateral decisions and canonical suffixes -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- If the first event is the only decision of the focal player, every native
deviation has the full terminal configuration law of a single graph policy. -/
theorem focal_initial_decision_config_distribution
    (timeouts : EventTimeouts graph.sequentialize)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    {horizon turns : Nat} (scheduler : (reactiveApplication timeouts leaks).Scheduler)
    (delay bound : graph.sequentialize.EventId → Nat)
    (inputs : PMF graph.sequentialize.Inputs) (reference : graph.sequentialize.BehavioralProfile)
    (contract : AsyncContract timeouts leaks (inputs.map State.initial) horizon scheduler
      delay bound)
    (timely : AsyncTimely timeouts delay bound)
    (realizable : RealizableProfile (graph := graph.sequentialize) inputs reference)
    (focal : Player) (deviation : (reactiveApplication timeouts leaks).Policy)
    (event : graph.EventId) (first : event.val = 0)
    (owned : graph.sequentialize.actor? event = some focal)
    (only : ∀ other, graph.sequentialize.actor? other = some focal → other = event) :
    let app := reactiveApplication timeouts leaks
    let players := Function.update
      (turnPolicy timeouts leaks bound turns
        (EventGraphRuntime.firstTurnTiming graph.sequentialize turns) reference)
      focal deviation
    ∃ policy : graph.sequentialize.BehavioralPolicy focal,
      (app.roundsFrom (inputs.map State.initial) scheduler players horizon).map
        (fun final => final.application.config) =
      inputs.bind (graph.sequentialize.runPolicies graph.sequentialize.canonicalScheduler
        (Function.update reference focal policy)) := by
  classical
  intro app players
  let G := graph.sequentialize
  let timing := EventGraphRuntime.firstTurnTiming G turns
  let start := fun seed => ReactiveApplication.Execution.initial app (State.initial seed)
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
  let phase := fun seed => app.runUntilHorizon scheduler players stop horizon (start seed)
  let plan := G.policyPlan reference G.canonicalScheduler
  let onward := fun config : G.Config => G.runPlan plan config.remaining config
  have ordered : (EventOrder.Cut.empty G.order).IsPrefix event.val :=
    first ▸ EventOrder.Cut.empty_isPrefix _
  have ready := ordered.ready event.isLt
  obtain ⟨law, phaseLaw⟩ := focal_initial_completed_config_distribution timeouts leaks scheduler
    bound turns
    timing reference focal deviation event owned (graph.sequentialize_solitary event) ready
    inputs horizon contract.completes
  let policy : G.BehavioralPolicy focal :=
    fun other ownerEq observed active =>
      if same : other = event then
        cast (congrArg (fun current => PMF (G.Action current)) same.symm) (law observed)
      else reference focal other ownerEq observed active
  refine ⟨policy, ?_⟩
  have localLaw := eventCompletionPreservesReadout_of_event_steps (scheduler := scheduler)
    (players := players)
    inputs reference 1 (by
      intro other before boundary later within
      refine firstTurn_event_config_distribution_of_owner_follows timeouts leaks (turns := turns)
        scheduler delay bound inputs reference contract timely realizable other players
        ?_ before boundary within
      intro owner ownerEq
      have different : owner ≠ focal := by
        rintro rfl
        have same := only other ownerEq
        rw [same, first] at later
        omega
      exact Function.update_of_ne different _ _)
  have native :
      (app.roundsFrom (inputs.map State.initial) scheduler players horizon).map
          (fun final => final.application.config) =
        (inputs.bind fun seed => (phase seed).map (fun final => final.application.config)).bind
          onward := by
    rw [ReactiveApplication.roundsFrom, PMF.map_bind, PMF.bind_map, PMF.bind_bind]
    apply bind_congr_on_support _
    intro seed present
    have boundary : PrefixBoundary (inputs.map State.initial) scheduler players event.val
        (start seed) := by
      rw [first]
      exact PrefixBoundary.initial _ scheduler players (State.initial seed)
        ((PMF.mem_support_map_iff _ _ _).mpr ⟨seed, present, rfl⟩)
        (EventOrder.Cut.empty_isPrefix _)
    change (app.runToHorizon scheduler players horizon (start seed)).map _ = _
    rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players stop, PMF.map_bind,
      PMF.bind_map]
    apply bind_congr_on_support _
    intro stopped reached
    have progress := runUntilHorizon_event_progress contract.completes event (start seed)
      stopped boundary.supported (Nat.zero_le _) ready.1 reached
    obtain ⟨within, rank, later, nextBoundary⟩ := PrefixBoundary.stopped timeouts leaks
      event (start seed) boundary (Nat.zero_le _) stopped reached progress.2.2.1
    have above : 1 ≤ rank := by omega
    have suffix := localLaw.runToHorizon contract.completes stopped
      ⟨rank, above, nextBoundary⟩ nextBoundary.supported within
    simpa only [Function.comp_def, PMF.map_id, id_eq] using suffix
  have tails (config : G.Config) (completed : event ∈ config.cut.completed) :
      G.runPlan (G.policyPlan (Function.update reference focal policy) G.canonicalScheduler)
        config.remaining config = onward config := by
    have agree (current : G.Config) (other : G.EventId) (different : other ≠ event) :
        EventGraph.actionDistribution (Function.update reference focal policy) current other =
          EventGraph.actionDistribution reference current other := by
      cases actor : G.actor? other with
      | none => rw [EventGraph.actionDistribution_of_ownerless _ _ actor,
          EventGraph.actionDistribution_of_ownerless _ _ actor]
      | some owner =>
          have unfocal : owner ≠ focal := fun same => different (only other (same ▸ actor))
          rw [EventGraph.actionDistribution_of_actor _ _ actor,
            EventGraph.actionDistribution_of_actor _ _ actor]
          by_cases inactive : owner ∈ current.defaulted
          · rw [dite_eq_left inactive, dite_eq_left inactive]
          · rw [dite_eq_right inactive, dite_eq_right inactive, Function.update_of_ne unfocal]
    exact EventGraph.runPlan_congr_of_actionDistribution G.canonicalScheduler
      (fun other => other = event)
      agree config.remaining config (fun _ same => same.symm ▸ completed)
  rw [native, phaseLaw, PMF.bind_bind]
  apply bind_congr_on_support _
  intro seed _
  let initial : G.Config := EventGraph.Config.initial seed
  have active : focal ∉ initial.defaulted := by change focal ∉ (∅ : Finset Player); simp
  change (((law (G.playerObserve focal initial)).bind fun action =>
    (initial.step event ready action).map State.drainConfig).bind onward) =
      G.runPlan (G.policyPlan (Function.update reference focal policy) G.canonicalScheduler)
        initial.remaining initial
  rw [EventGraph.runPlan_remaining_canonical_step _ initial event ready
    (fun other _ => Fin.le_iff_val_le_val.mpr (by rw [first]; exact Nat.zero_le _)),
    EventGraph.eventStep, EventGraph.actionDistribution_of_actor _ _ owned, dite_eq_right active,
    Function.update_self, PMF.bind_bind, PMF.bind_bind]
  simp only [policy, dite_eq_left rfl, cast_eq]
  apply bind_congr_on_support _
  intro action _
  rw [PMF.bind_map]
  apply bind_congr_on_support _
  intro next member
  have completed : event ∈ next.cut.completed := by
    rw [initial.step_cut event ready action next member, EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  have drained : onward (State.drainConfig next) = onward next :=
    (State.drain_runPlan_canonical graph reference (State.ofConfig next)).symm
  exact drained.trans (tails next completed).symm

end Vegas.EventGraphRuntime
