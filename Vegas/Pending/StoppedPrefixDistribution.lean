module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.PrefixConfiguration
public import Vegas.Pending.PrefixBoundary

@[expose] public section

/-! # The graph prefix read at an actual ledger stop -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- For any physical policies realizing a canonical terminal configuration law,
stopping at any event and reading through its rank gives exactly that many
canonical graph steps. One native round may have completed additional events. -/
theorem stopped_prefix_of_config_distribution
    (timeouts : EventTimeouts graph.sequentialize)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    (scheduler : (reactiveApplication timeouts leaks).Scheduler)
    (players : Player → (reactiveApplication timeouts leaks).Policy) (horizon : Nat)
    (inputs : PMF graph.sequentialize.Inputs)
    (completes : CompletesPlay timeouts leaks (inputs.map State.initial) horizon scheduler)
    (reference : graph.sequentialize.BehavioralProfile)
    (full : ((reactiveApplication timeouts leaks).roundsFrom (inputs.map State.initial)
      scheduler players horizon).map (fun final => final.application.config) =
      inputs.bind (graph.sequentialize.runPolicies graph.sequentialize.canonicalScheduler
        reference))
    (event : graph.EventId) :
    let app := reactiveApplication timeouts leaks
    (inputs.bind fun seed => (app.runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon
      (ReactiveApplication.Execution.initial app (State.initial seed))).map fun stopped =>
        Config.rankPrefix (event.val + 1) stopped.application.config) =
      inputs.bind fun seed => graph.sequentialize.runPlan
        (graph.sequentialize.policyPlan reference graph.sequentialize.canonicalScheduler)
        (event.val + 1) (Config.initial seed) := by
  intro app
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
  let read := Config.rankPrefix (graph := graph.sequentialize) (event.val + 1)
  have projected := congrArg (PMF.map read) full
  rw [PMF.map_comp, PMF.map_bind] at projected
  refine Eq.trans ?_ (projected.trans ?_)
  · unfold ReactiveApplication.roundsFrom
    rw [PMF.map_bind, PMF.bind_map]
    apply bind_congr_on_support _
    intro seed present
    let start := ReactiveApplication.Execution.initial app (State.initial seed)
    have empty : start.application.config.cut.IsPrefix 0 := EventOrder.Cut.empty_isPrefix _
    have boundary := PrefixBoundary.initial (inputs.map State.initial) scheduler players
      (State.initial seed) ((PMF.mem_support_map_iff _ _ _).mpr ⟨seed, present, rfl⟩) empty
    change (app.runUntilHorizon scheduler players stop horizon start).map _ =
      (app.runToHorizon scheduler players horizon start).map _
    rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players stop, PMF.map_bind,
      ← PMF.bind_pure_comp]
    apply bind_congr_on_support _
    intro stopped reached
    have done := (runUntilHorizon_event_progress completes event start stopped boundary.supported
      (Nat.zero_le _) (by change event ∉ (∅ : Finset graph.EventId); simp) reached).2.2.1
    have first := reactive_runUntil_graph_steps timeouts leaks scheduler players stop _ start
      stopped reached
    obtain ⟨rank, _, ordered⟩ := Config.Step.path_isPrefix_sequential graph first empty
    obtain ⟨primary, atRank, _, toStop⟩ := Config.Step.path_prefix_at first empty ordered
      (Nat.zero_le (event.val + 1)) ((ordered.2 event).mp done)
    have earlier := Config.rankPrefix_of_path atRank toStop
    symm
    change ((app.runRounds scheduler players _ stopped).map _) = PMF.pure (read _)
    rw [map_congr_on_support _ (g := fun _ => read stopped.application.config) ?_,
      pmf_map_fun_const]
    intro final member
    exact (Config.rankPrefix_of_path atRank (toStop.trans
      (reactive_runRounds_graph_steps timeouts leaks scheduler players _ stopped final
        member))).trans
        earlier.symm
  · apply bind_congr_on_support _
    intro seed _
    exact runPolicies_rankPrefix reference seed _ event.isLt

end Vegas.EventGraphRuntime
