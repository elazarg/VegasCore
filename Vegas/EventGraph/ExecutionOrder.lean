module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.SchedulerPredraw
public import Vegas.EventGraph.TopologicalOrder

@[expose] public section

/-! # Completion orders of graph execution

The dependency relation determines exactly the possible complete event orders.
A deterministic public scheduler can impose any topological ordering, uniformly
over behavioral profiles and initial inputs. This concerns the event identities;
the decisions and values can still depend on the chosen order.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The completion history of a reachable terminal configuration is a topological ordering. -/
theorem Config.Reachable.topological {inputs : graph.Inputs} {config : graph.Config}
    (reach : config.Reachable inputs) (terminal : config.cut.Terminal) :
    graph.order.Topological (config.history.map EventCompletion.event) := by
  change config.cut.completed = Finset.univ at terminal
  refine ⟨(List.perm_ext_iff_of_nodup config.history_nodup (List.nodup_finRange _)).mpr ?_, ?_⟩
  · intro event
    simp only [config.history_exact, terminal, Finset.mem_univ, List.mem_finRange]
  · intro predecessor event member
    exact reach.predecessor_idxOf_lt event (terminal.symm ▸ Finset.mem_univ event)
      predecessor member

/-- Select the next entry of the specified list using only the public history length.
If that entry is absent or disabled, select the least enabled event. -/
def orderedScheduler (events : List graph.EventId) : graph.PublicScheduler :=
  assignedScheduler fun site => events[site.1.completionOrder.length]?

omit [DecidableEq Player] in
private theorem ready_of_topological_prefix (events : List graph.EventId)
    (topological : graph.order.Topological events) (config : graph.Config) (index : Nat)
    (orderedHistory : config.history.map EventCompletion.event = events.take index)
    (before : index < events.length) : config.cut.Ready events[index] := by
  have position := topological.nodup.idxOf_getElem index before
  constructor
  · intro completed
    have member : events[index] ∈ events.take index := by
      rw [← orderedHistory]
      exact (config.history_exact _).mpr completed
    have earlier := (List.mem_take_iff_idxOf_lt (topological.mem events[index])).mp member
    omega
  · intro predecessor member
    apply (config.history_exact predecessor).mp
    rw [orderedHistory]
    apply (List.mem_take_iff_idxOf_lt (topological.mem predecessor)).mpr
    have earlier := topological.predecessor_before predecessor events[index] member
    omega

omit [DecidableEq Player] in
private theorem orderedScheduler_at_prefix (events : List graph.EventId)
    (topological : graph.order.Topological events) (config : graph.Config) (index : Nat)
    (orderedHistory : config.history.map EventCompletion.event = events.take index)
    (length : config.history.length = index) (before : index < events.length)
    (notTerminal : ¬ config.cut.Terminal) :
    orderedScheduler events (graph.publicObserve config) config.cut.enabled
        (enabled_nonempty_of_not_terminal config notTerminal) =
      PMF.pure ⟨events[index], (EventOrder.Cut.mem_enabled _ _).mpr
        (ready_of_topological_prefix events topological config index orderedHistory before)⟩ := by
  have ready := (EventOrder.Cut.mem_enabled _ _).mpr
    (ready_of_topological_prefix events topological config index orderedHistory before)
  simp [orderedScheduler, assignedScheduler, schedulerOf, PMF.pure_map, selectAt,
    publicObserve_completionOrder, length, List.getElem?_eq_getElem before, ready]

private theorem runPlan_ordered_prefix (events : List graph.EventId)
    (topological : graph.order.Topological events) (profile : graph.BehavioralProfile) :
    ∀ fuel (config : graph.Config) (index : Nat),
      config.history.map EventCompletion.event = events.take index →
      config.history.length = index → index + fuel ≤ events.length →
      ∀ final ∈ (graph.runPlan (graph.policyPlan profile (orderedScheduler events))
        fuel config).support,
        final.history.map EventCompletion.event = events.take (index + fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro config index orderedHistory _ _ final supported
      have same : final = config := by simpa [EventGraph.runPlan] using supported
      simpa [same] using orderedHistory
  | succ fuel ih =>
      intro config index orderedHistory length bounded final supported
      have before : index < events.length := by omega
      have ready := ready_of_topological_prefix events topological config index
        orderedHistory before
      have notTerminal := ready.not_terminal
      rw [runPlan_policyPlan_succ profile (orderedScheduler events) fuel config notTerminal,
        orderedScheduler_at_prefix events topological config index orderedHistory
          length before notTerminal, PMF.pure_bind, PMF.support_bind] at supported
      simp only [Set.mem_iUnion] at supported
      obtain ⟨middle, stepped, rest⟩ := supported
      rw [eventStep, PMF.support_bind] at stepped
      simp only [Set.mem_iUnion] at stepped
      obtain ⟨action, _, stepped⟩ := stepped
      have extension := config.step_history_events events[index] ready action middle stepped
      have nextPrefix : middle.history.map EventCompletion.event = events.take (index + 1) := by
        rw [extension, orderedHistory, List.take_concat_get' events index before]
      have nextLength : middle.history.length = index + 1 := by
        have lengths := congrArg List.length extension
        simpa [length] using lengths
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih middle (index + 1) nextPrefix nextLength (by omega) final rest

/-- Every topological ordering is forced by one deterministic public scheduler,
for all behavioral profiles and initial inputs. -/
theorem runPolicies_orderedScheduler (events : List graph.EventId)
    (topological : graph.order.Topological events) (profile : graph.BehavioralProfile)
    (inputs : graph.Inputs) :
    (graph.runPolicies (orderedScheduler events) profile inputs).map
        (fun config => config.history.map EventCompletion.event) = PMF.pure events := by
  calc
    _ = (graph.runPolicies (orderedScheduler events) profile inputs).map
        (fun _ => events) := by
      apply map_congr_on_support
      intro final supported
      have orderedHistory := runPlan_ordered_prefix events topological profile
        graph.order.eventCount
        (Config.initial inputs) 0 (by simp [Config.initial]) (by simp [Config.initial])
        (by simp [topological.length]) final supported
      simpa only [Nat.zero_add, ← topological.length, List.take_length] using orderedHistory
    _ = _ := PMF.map_const _ _

/-- For a fixed profile and input, the supported complete orders, ranging over public
schedulers, are exactly the topological orderings of the dependency relation. -/
theorem topological_iff_supported_run (events : List graph.EventId)
    (profile : graph.BehavioralProfile) (inputs : graph.Inputs) :
    graph.order.Topological events ↔
      ∃ (scheduler : graph.PublicScheduler) (final : graph.Config),
        final ∈ (graph.runPolicies scheduler profile inputs).support ∧
          final.history.map EventCompletion.event = events := by
  constructor
  · intro topological
    obtain ⟨final, supported⟩ :=
      (graph.runPolicies (orderedScheduler events) profile inputs).support_nonempty
    refine ⟨orderedScheduler events, final, supported, ?_⟩
    have mapped : final.history.map EventCompletion.event ∈
        ((graph.runPolicies (orderedScheduler events) profile inputs).map
          (fun config => config.history.map EventCompletion.event)).support := by
      rw [PMF.support_map]
      exact ⟨final, supported, rfl⟩
    simpa [runPolicies_orderedScheduler events topological profile inputs] using mapped
  · rintro ⟨scheduler, final, supported, same⟩
    rw [← same]
    exact (graph.run_reachable inputs (graph.policyPlan profile scheduler)
      final supported).topological
      (graph.runPolicies_terminal scheduler profile inputs final supported)

end Vegas.EventGraph

