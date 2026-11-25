module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.GraphCompletionDistribution
public import Vegas.Pending.PrefixBoundary
public import Vegas.Pending.ConfigDrain
public import Vegas.Pending.ExclusionPolicyDistribution
public import Vegas.EventGraph.SchedulerErasure

@[expose] public section

/-! # Terminal graph configuration distributions from native event steps -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {timeouts : EventTimeouts graph.sequentialize}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize)}
  {horizon : Nat} {scheduler : ((reactiveApplication timeouts) leaks).Scheduler}
  {players : Player → ((reactiveApplication timeouts) leaks).Policy}

local notation "app" => (reactiveApplication timeouts) leaks

/-- Local step laws above a minimum rank determine a graph continuation from
every reached boundary in that suffix. -/
theorem eventCompletionPreservesReadout_of_event_steps (inputs : PMF graph.sequentialize.Inputs)
    (reference : graph.sequentialize.BehavioralProfile) (minimum : Nat)
    (localStep : ∀ (event : graph.EventId) (before : (app).Execution)
      (boundary : PrefixBoundary (inputs.map State.initial) scheduler players event.val before),
      minimum ≤ event.val → before.environmentRecall.length ≤ horizon →
      ((app).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon before).map
          (fun final => final.application.config) =
        (EventGraph.eventStep reference before.application.config event
          (boundary.ordered.ready event.isLt)).map State.drainConfig) :
    EventCompletionPreservesReadout
      (graph.sequentialize.policyPlan reference graph.sequentialize.canonicalScheduler)
      id scheduler players horizon
      (fun before => ∃ rank, minimum ≤ rank ∧
        PrefixBoundary (inputs.map State.initial) scheduler players rank before) := by
  let plan := graph.sequentialize.policyPlan reference graph.sequentialize.canonicalScheduler
  let onward := fun config : graph.sequentialize.Config =>
    graph.sequentialize.runPlan plan config.remaining config
  intro before ⟨rank, above, boundary⟩ within nonterminal
  have active : rank < graph.order.eventCount := by
    apply lt_of_le_of_ne boundary.ordered.1
    intro equal
    exact nonterminal (equal ▸ boundary.ordered).terminal
  let event : graph.EventId := ⟨rank, active⟩
  have ready := boundary.ordered.ready event.isLt
  refine ⟨event, ready.1, ?_, ?_⟩
  · intro after reached done
    obtain ⟨_, next, advances, later⟩ := PrefixBoundary.stopped timeouts leaks event before boundary
      within after reached done
    exact ⟨next, above.trans advances.le, later⟩
  · have composed := congrArg (fun law => PMF.bind law onward)
      (localStep event before boundary above within)
    simp only [PMF.bind_map, Function.comp_def] at composed
    simp only [PMF.map_id]
    refine composed.trans ?_
    have same (config : graph.sequentialize.Config) :
        onward (State.drainConfig config) = onward config :=
      (State.drain_runPlan_canonical graph reference (State.ofConfig config)).symm
    simp only [same]
    exact (EventGraph.runPlan_remaining_canonical_step reference before.application.config event
      ready (fun _ other => graph.sequentialize_ready_le_unfinished _ ready other.1)).symm

/-- If each native prefix stop simulates its next graph step followed by automatic
draining, the clients implement the canonical terminal graph configuration law. -/
theorem config_distribution_of_event_steps (inputs : PMF graph.sequentialize.Inputs)
    (reference : graph.sequentialize.BehavioralProfile)
    (completes : CompletesPlay timeouts leaks (inputs.map State.initial) horizon scheduler)
    (localStep : ∀ (event : graph.EventId) (before : (app).Execution)
      (boundary : PrefixBoundary (inputs.map State.initial) scheduler players event.val before),
      before.environmentRecall.length ≤ horizon →
      ((app).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon before).map
          (fun final => final.application.config) =
        (EventGraph.eventStep reference before.application.config event
          (boundary.ordered.ready event.isLt)).map State.drainConfig) :
    ((app).roundsFrom (inputs.map State.initial) scheduler players horizon).map
      (fun final => final.application.config) =
      ((graph.sequentialize.canonicalGame inputs).play reference).map Subtype.val := by
  let plan := graph.sequentialize.policyPlan reference graph.sequentialize.canonicalScheduler
  have localLaw := eventCompletionPreservesReadout_of_event_steps inputs reference 0
    (fun event before boundary _ within => localStep event before boundary within)
  have starts : ∀ state ∈ (inputs.map State.initial).support,
      ∃ rank, 0 ≤ rank ∧ PrefixBoundary (inputs.map State.initial) scheduler players rank
        (ReactiveApplication.Execution.initial (app) state) := by
    intro state present
    obtain ⟨input, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp present
    exact ⟨0, Nat.le_refl 0, PrefixBoundary.initial _ scheduler players _ present
      (EventOrder.Cut.empty_isPrefix _)⟩
  have assembled := localLaw.roundsFrom completes starts
  simp only [PMF.map_id, id_eq, PMF.bind_map, Function.comp_def] at assembled
  refine assembled.trans ?_
  refine Eq.trans ?_ (EventGraph.gameForm_play_map_val graph.sequentialize inputs
    graph.sequentialize.canonicalScheduler reference).symm
  apply congrArg
  funext input
  change graph.sequentialize.runPlan plan
    (EventGraph.Config.initial input : graph.sequentialize.Config).remaining _ =
    graph.sequentialize.runPlan plan graph.order.eventCount _
  congr 1

end Vegas.EventGraphRuntime
