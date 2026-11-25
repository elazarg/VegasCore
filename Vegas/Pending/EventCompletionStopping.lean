module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveGraphSteps
public import Vegas.Pending.ReactiveAsyncContract
public import Interaction.ReactiveRawRoundTrace
public import Interaction.ReactiveStopping

@[expose] public section

/-! # Progress at the first scheduler boundary completing a graph event -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
    {graph : Vegas.EventGraph Player L} {timeouts : EventTimeouts graph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

local notation "app" => (reactiveApplication timeouts) leaks

variable {initial : PMF ((reactiveApplication timeouts) leaks).State} {horizon : Nat}
    {scheduler : ((reactiveApplication timeouts) leaks).Scheduler}
    {players : Player → ((reactiveApplication timeouts) leaks).Policy}

/-- At the first completion of an unfinished event the stopped execution is still supported
within the horizon, the event is complete, and the number of remaining graph events decreases.
Several events may complete in the same scheduler round. -/
theorem runUntilHorizon_event_progress
    (completes : CompletesPlay timeouts leaks initial horizon scheduler)
    (event : graph.EventId) (before after : (app).Execution)
    (supported : before ∈ ((app).roundsFrom initial scheduler players
      before.environmentRecall.length).support)
    (bounded : before.environmentRecall.length ≤ horizon)
    (unfinished : event ∉ before.application.config.cut.completed)
    (reached : after ∈ ((app).runUntilHorizon scheduler players
      (fun execution => event ∈ execution.application.config.cut.completed) horizon
        before).support) :
    after ∈ ((app).roundsFrom initial scheduler players after.environmentRecall.length).support ∧
      after.environmentRecall.length ≤ horizon ∧ event ∈ after.application.config.cut.completed ∧
      after.application.config.remaining < before.application.config.remaining := by
  let stop := fun execution : (app).Execution => event ∈ execution.application.config.cut.completed
  have afterSupported := (app).roundsFrom_runUntil scheduler players initial stop _ before after
    supported reached
  have done : event ∈ after.application.config.cut.completed := by
    rcases (app).runUntilHorizon_stopped scheduler players stop horizon
        (horizon - before.environmentRecall.length) before after (by omega) reached with hit | spent
    · exact hit
    · rw [spent] at afterSupported
      obtain ⟨trace⟩ := (app).raw_trace_roundsFrom initial horizon scheduler players horizon
        le_rfl after afterSupported
      have terminal := completes _ trace ⟨Nat.sub_self _, rfl⟩
      exact Finset.eq_univ_iff_forall.mp terminal event
  obtain ⟨used, within, _, length⟩ := (app).runUntil_runRounds scheduler players stop
    (horizon - before.environmentRecall.length) before after reached
  have path := reactive_runUntil_graph_steps timeouts leaks scheduler players stop _
    before after reached
  have proper := Finset.ssubset_iff_subset_ne.mpr
    ⟨EventGraph.Config.Step.path_completed_mono path, fun eq => unfinished (eq ▸ done)⟩
  have less := Finset.card_lt_card proper
  have atMost : after.application.config.cut.completed.card ≤ graph.order.eventCount := by
    simpa using Finset.card_le_card (Finset.subset_univ after.application.config.cut.completed)
  exact ⟨afterSupported, by omega, done, by unfold EventGraph.Config.remaining; omega⟩

end Vegas.EventGraphRuntime
