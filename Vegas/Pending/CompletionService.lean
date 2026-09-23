/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventService
import Vegas.Pending.EventProgress

/-! # A bounded completion contract for event service

An epoch advances time once, samples ready chance events, and expires due
strategic events. These local facts suffice for bounded completion regardless
of packet traffic, player policies, or the execution state's recall format.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

structure CompletionService (runtime : EventGraphRuntime graph) (Execution : Type) where
  state : Execution → State graph
  epoch : Execution → FinDist Execution
  progress : ∀ inputs before after, (state before).Invariant inputs →
    after ∈ (epoch before).support → State.ServiceProgress inputs 1 (state before) (state after)
  chance : ∀ inputs event before after, (state before).Invariant inputs →
    (state before).config.cut.Ready event → graph.actor? event = none →
    after ∈ (epoch before).support → event ∈ (state after).config.cut.completed
  due : ∀ inputs event entered before after, (state before).Invariant inputs →
    (state before).config.cut.Ready event → (graph.actor? event).isSome = true →
    (state before).activatedAt event = some entered →
    runtime.deadline event ≤ (state before).clock + 1 - entered →
    after ∈ (epoch before).support → event ∈ (state after).config.cut.completed

namespace CompletionService

variable {runtime : EventGraphRuntime graph} {Execution : Type}

def run (service : CompletionService runtime Execution) : Nat → Execution → FinDist Execution
  | 0, execution => FinDist.pure execution
  | count + 1, execution => (service.epoch execution).bind (run service count)

theorem run_add (service : CompletionService runtime Execution) (first second : Nat)
    (execution : Execution) :
    service.run (first + second) execution =
      (service.run first execution).bind (service.run second) := by
  induction first generalizing execution with
  | zero => simp only [Nat.zero_add, run, FinDist.pure_bind]
  | succ first ih =>
      simp only [Nat.succ_add, run, FinDist.bind_bind]
      exact FinDist.bind_congr fun next _ => ih next

theorem run_progress (service : CompletionService runtime Execution) (inputs : graph.Inputs)
    (count : Nat) (before after : Execution) (invariant : (service.state before).Invariant inputs)
    (supported : after ∈ (service.run count before).support) :
    State.ServiceProgress inputs count (service.state before) (service.state after) := by
  induction count generalizing before with
  | zero => cases FinDist.mem_support_pure.mp supported; exact .refl invariant
  | succ count ih =>
      obtain ⟨middle, moved, finished⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      have first := service.progress inputs before middle invariant moved
      simpa only [Nat.add_comm 1 count] using first.trans (ih middle first.invariant finished)

theorem window_completes_ready (service : CompletionService runtime Execution)
    (inputs : graph.Inputs) (event : graph.EventId) (before after : Execution)
    (invariant : (service.state before).Invariant inputs)
    (ready : (service.state before).config.cut.Ready event)
    (supported : after ∈ (service.run (runtime.maxDeadline + 1) before).support) :
    event ∈ (service.state after).config.cut.completed := by
  rw [service.run_add runtime.maxDeadline 1] at supported
  obtain ⟨middle, moved, finished⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  have progress := service.run_progress inputs runtime.maxDeadline before middle invariant moved
  rcases progress.ready_or_completed event ready with completed | middleReady
  · exact (service.run_progress inputs 1 middle after progress.invariant finished).completed
      completed
  · have last : after ∈ (service.epoch middle).support := by
      simpa only [run, FinDist.bind_pure] using finished
    cases actor : graph.actor? event with
    | none =>
        exact service.chance inputs event middle after progress.invariant middleReady actor last
    | some owner =>
        have strategic : (graph.actor? event).isSome = true := by
          simp only [actor, Option.isSome_some]
        obtain ⟨entered, activated⟩ := Option.isSome_iff_exists.mp
          ((invariant.activated_iff event).2 ⟨ready, strategic⟩)
        have middleActivated := progress.activated event entered activated middleReady.1
        have enteredLe := invariant.activated_le event entered activated
        have deadlineLe : runtime.deadline event ≤ runtime.maxDeadline :=
          Finset.le_sup (f := runtime.deadline) (Finset.mem_univ event)
        have due : runtime.deadline event ≤ (service.state middle).clock + 1 - entered := by
          rw [progress.clock]
          omega
        exact service.due inputs event entered middle after progress.invariant middleReady
          strategic middleActivated due last

private theorem remaining_lt (before after : graph.Config)
    (subset : before.cut.completed ⊆ after.cut.completed)
    (event : graph.EventId) (fresh : event ∉ before.cut.completed)
    (done : event ∈ after.cut.completed) : after.remaining < before.remaining := by
  have proper : before.cut.completed ⊂ after.cut.completed :=
    Finset.ssubset_iff_subset_ne.mpr ⟨subset, fun same => fresh (same ▸ done)⟩
  have cardLt := Finset.card_lt_card proper
  have beforeLe : before.cut.completed.card ≤ graph.order.eventCount := by
    simpa using Finset.card_le_card (Finset.subset_univ before.cut.completed)
  have afterLe : after.cut.completed.card ≤ graph.order.eventCount := by
    simpa using Finset.card_le_card (Finset.subset_univ after.cut.completed)
  simp only [EventGraph.Config.remaining]
  omega

/-- Each deadline window completes a ready event unless the graph is already
terminal. At most one such window per event is sufficient. -/
theorem terminal (service : CompletionService runtime Execution) (inputs : graph.Inputs)
    (before after : Execution) (invariant : (service.state before).Invariant inputs)
    (supported : after ∈ (service.run runtime.serviceEpochs before).support) :
    (service.state after).config.cut.Terminal := by
  have bounded : ∀ fuel (start finish : Execution),
      (service.state start).Invariant inputs →
      (service.state start).config.remaining ≤ fuel →
      finish ∈ (service.run (fuel * (runtime.maxDeadline + 1)) start).support →
      (service.state finish).config.cut.Terminal := by
    intro fuel
    induction fuel with
    | zero =>
        intro start finish _ remaining finishMem
        have done := (service.state start).config.terminal_iff_remaining_zero.mpr (by omega)
        simp only [Nat.zero_mul, run, FinDist.mem_support_pure] at finishMem
        subst finish
        exact done
    | succ fuel ih =>
        intro start finish startInvariant remaining finishMem
        rw [Nat.succ_mul, Nat.add_comm, service.run_add] at finishMem
        obtain ⟨middle, moved, finished⟩ :=
          Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ finishMem)
        have progress := service.run_progress inputs (runtime.maxDeadline + 1)
          start middle startInvariant moved
        by_cases stopped : (service.state start).config.cut.Terminal
        · have middleTerminal : (service.state middle).config.cut.Terminal := by
            rw [EventOrder.Cut.Terminal] at stopped ⊢
            apply Finset.Subset.antisymm (Finset.subset_univ _)
            intro event _
            apply progress.completed
            rw [stopped]
            exact Finset.mem_univ event
          apply ih middle finish progress.invariant _ finished
          rw [(service.state middle).config.terminal_iff_remaining_zero.mp middleTerminal]
          omega
        · obtain ⟨event, ready⟩ :=
            (service.state start).config.cut.exists_ready_of_not_terminal stopped
          have done := service.window_completes_ready inputs event start middle
            startInvariant ready moved
          have decreased := remaining_lt (service.state start).config
            (service.state middle).config progress.completed event ready.1 done
          exact ih middle finish progress.invariant (by omega) finished
  apply bounded graph.order.eventCount before after invariant
  · simp [EventGraph.Config.remaining]
  · exact supported

end CompletionService
end Vegas.EventGraphRuntime
