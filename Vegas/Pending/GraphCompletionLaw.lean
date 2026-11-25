module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.EventCompletionStopping

@[expose] public section

/-! # From event completion laws to the terminal graph law

The ledger stops when a selected unfinished event completes. Further events may
complete in the same round. A boundary predicate records the information the
client proof needs at the next such stop.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
    {graph : Vegas.EventGraph Player L} {timeouts : EventTimeouts graph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
    {initial : PMF (State graph)} {horizon : Nat}
    {scheduler : ((reactiveApplication timeouts) leaks).Scheduler}
    {players : Player → ((reactiveApplication timeouts) leaks).Policy}

local notation "app" => (reactiveApplication timeouts) leaks

/-- From each nonterminal boundary, choose an unfinished event. Once it completes, the
stopped ledger is a boundary again, and finishing there with the graph plan gives
the same outcome distribution as running the graph plan from the original boundary. -/
def EventCompletionLaw {Outcome : Type*} (plan : graph.EventPlan) (read : graph.Config → Outcome)
    (scheduler : (app).Scheduler) (players : Player → (app).Policy) (horizon : Nat)
    (boundary : (app).Execution → Prop) : Prop :=
  ∀ before, boundary before → before.environmentRecall.length ≤ horizon →
    ¬ before.application.config.cut.Terminal →
      ∃ event : graph.EventId, event ∉ before.application.config.cut.completed ∧
        let stopped := (app).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon before
        (∀ after ∈ stopped.support, event ∈ after.application.config.cut.completed →
          boundary after) ∧
          stopped.bind (fun after => (graph.runPlan plan after.application.config.remaining
            after.application.config).map read) =
          (graph.runPlan plan before.application.config.remaining
            before.application.config).map read

/-- A local law for completing one unfinished event at every nonterminal boundary
determines the entire distribution of the selected terminal graph readout. -/
theorem EventCompletionLaw.runToHorizon {Outcome : Type*} {plan : graph.EventPlan}
    {read : graph.Config → Outcome} {boundary : (app).Execution → Prop}
    (localLaw : EventCompletionLaw plan read scheduler players horizon boundary)
    (completes : CompletesPlay timeouts leaks initial horizon scheduler)
    (start : (app).Execution) (atBoundary : boundary start)
    (supported : start ∈ ((app).roundsFrom initial scheduler players
      start.environmentRecall.length).support)
    (bounded : start.environmentRecall.length ≤ horizon) :
    ((app).runToHorizon scheduler players horizon start).map (fun final =>
      read final.application.config) =
      (graph.runPlan plan start.application.config.remaining
        start.application.config).map read := by
  classical
  generalize countEq : start.application.config.remaining = count
  induction count using Nat.strong_induction_on generalizing start with
  | ind count ih =>
    rw [← countEq]
    by_cases terminal : start.application.config.cut.Terminal
    · rw [start.application.config.terminal_iff_remaining_zero.mp terminal, EventGraph.runPlan,
        PMF.pure_map]
      change ((app).runRounds scheduler players _ start).map _ = _
      rw [map_congr_on_support _ (g := fun _ => read start.application.config)
        (fun final reached => congrArg read (EventGraph.Config.Step.path_eq_of_terminal
          (reactive_runRounds_graph_steps timeouts leaks scheduler players _ start final reached)
          terminal)), pmf_map_fun_const]
    · obtain ⟨event, unfinished, closed, agrees⟩ := localLaw start atBoundary bounded terminal
      rw [(app).runToHorizon_eq_runUntilHorizon_bind scheduler players
        (fun final => event ∈ final.application.config.cut.completed), PMF.map_bind]
      refine Eq.trans (bind_congr_on_support _ ?_) agrees
      intro after reached
      obtain ⟨seen, within, done, less⟩ := runUntilHorizon_event_progress completes event start
        after supported bounded unfinished reached
      exact ih after.application.config.remaining (less.trans_eq countEq) after
        (closed after reached done) seen within rfl

/-- Mixing over initial states yields the graph readout law from the original
initializer. The initial distribution and graph reader can be supplied by any frontend. -/
theorem EventCompletionLaw.roundsFrom {Outcome : Type*} {plan : graph.EventPlan}
    {read : graph.Config → Outcome} {boundary : (app).Execution → Prop}
    (localLaw : EventCompletionLaw plan read scheduler players horizon boundary)
    (completes : CompletesPlay timeouts leaks initial horizon scheduler)
    (starts : ∀ state ∈ initial.support,
      boundary (ReactiveApplication.Execution.initial (app) state)) :
    ((app).roundsFrom initial scheduler players horizon).map
        (fun final => read final.application.config) =
      initial.bind fun state =>
        (graph.runPlan plan state.config.remaining state.config).map read := by
  rw [ReactiveApplication.roundsFrom, PMF.map_bind]
  apply bind_congr_on_support _
  intro state present
  let start := ReactiveApplication.Execution.initial (app) state
  have seen : start ∈ ((app).roundsFrom initial scheduler players 0).support := by
    rw [ReactiveApplication.roundsFrom, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨state, present, by simp [ReactiveApplication.runRounds, start]⟩
  exact localLaw.runToHorizon completes start (starts state present) seen (Nat.zero_le _)

end Vegas.EventGraphRuntime
