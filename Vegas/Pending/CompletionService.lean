/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ServicePlan
import Vegas.Pending.EventProgress
import Vegas.EventGraph.DependencyHeight

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
  epoch : Execution → PMF Execution
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

def run (service : CompletionService runtime Execution) : Nat → Execution → PMF Execution
  | 0, execution => PMF.pure execution
  | count + 1, execution => (service.epoch execution).bind (run service count)

theorem run_add (service : CompletionService runtime Execution) (first second : Nat)
    (execution : Execution) :
    service.run (first + second) execution =
      (service.run first execution).bind (service.run second) := by
  induction first generalizing execution with
  | zero => simp only [Nat.zero_add, run, PMF.pure_bind]
  | succ first ih =>
      simp only [Nat.succ_add, run, PMF.bind_bind]
      exact bind_congr_on_support _ fun next _ => ih next

theorem run_progress (service : CompletionService runtime Execution) (inputs : graph.Inputs)
    (count : Nat) (before after : Execution) (invariant : (service.state before).Invariant inputs)
    (supported : after ∈ (service.run count before).support) :
    State.ServiceProgress inputs count (service.state before) (service.state after) := by
  induction count generalizing before with
  | zero => cases (PMF.mem_support_pure_iff _ _).mp supported; exact .refl invariant
  | succ count ih =>
      obtain ⟨middle, moved, finished⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      have first := service.progress inputs before middle invariant moved
      simpa only [Nat.add_comm 1 count] using first.trans (ih middle first.invariant finished)

theorem window_completes_ready (service : CompletionService runtime Execution)
    (inputs : graph.Inputs) (event : graph.EventId) (before after : Execution)
    (invariant : (service.state before).Invariant inputs)
    (ready : (service.state before).config.cut.Ready event)
    (supported : after ∈ (service.run (runtime.maxDeadline + 1) before).support) :
    event ∈ (service.state after).config.cut.completed := by
  rw [service.run_add runtime.maxDeadline 1] at supported
  obtain ⟨middle, moved, finished⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  have progress := service.run_progress inputs runtime.maxDeadline before middle invariant moved
  rcases progress.ready_or_completed event ready with completed | middleReady
  · exact (service.run_progress inputs 1 middle after progress.invariant finished).completed
      completed
  · have last : after ∈ (service.epoch middle).support := by
      simpa only [run, PMF.bind_pure] using finished
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

/-- Each deadline window clears one complete layer of the dependency graph. -/
theorem completed_of_dependencyDepth_le (service : CompletionService runtime Execution)
    (inputs : graph.Inputs) (windows : Nat) (before after : Execution)
    (invariant : (service.state before).Invariant inputs)
    (supported : after ∈ (service.run (windows * (runtime.maxDeadline + 1)) before).support)
    (event : graph.EventId) (depth : graph.order.dependencyDepth event ≤ windows) :
    event ∈ (service.state after).config.cut.completed := by
  induction windows generalizing after event with
  | zero => have positive := graph.order.dependencyDepth_pos event; omega
  | succ windows ih =>
      rw [Nat.succ_mul, service.run_add] at supported
      obtain ⟨middle, moved, finished⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      have progress := service.run_progress inputs (windows * (runtime.maxDeadline + 1))
        before middle invariant moved
      by_cases completed : event ∈ (service.state middle).config.cut.completed
      · exact (service.run_progress inputs (runtime.maxDeadline + 1) middle after
          progress.invariant finished).completed completed
      · apply service.window_completes_ready inputs event middle after progress.invariant
          ⟨completed, ?_⟩ finished
        intro predecessor member
        have smaller := graph.order.predecessor_depth_lt member
        exact ih middle moved predecessor (by omega)

/-- Dependency height suffices independently of the number of parallel events. -/
theorem terminal_of_dependencyHeight (service : CompletionService runtime Execution)
    (inputs : graph.Inputs) (before after : Execution)
    (invariant : (service.state before).Invariant inputs)
    (supported : after ∈ (service.run
      (graph.order.dependencyHeight * (runtime.maxDeadline + 1)) before).support) :
    (service.state after).config.cut.Terminal := by
  apply Finset.eq_univ_of_forall
  intro event
  exact service.completed_of_dependencyDepth_le inputs graph.order.dependencyHeight before after
    invariant supported event (graph.order.dependencyDepth_le_height event)

/-- Each deadline window completes a ready event unless the graph is already
terminal. At most one such window per event is sufficient. -/
theorem terminal (service : CompletionService runtime Execution) (inputs : graph.Inputs)
    (before after : Execution) (invariant : (service.state before).Invariant inputs)
    (supported : after ∈ (service.run runtime.serviceEpochs before).support) :
    (service.state after).config.cut.Terminal := by
  apply Finset.eq_univ_of_forall
  intro event
  exact service.completed_of_dependencyDepth_le inputs graph.order.eventCount before after
    invariant supported event ((graph.order.dependencyDepth_le_height event).trans
      graph.order.dependencyHeight_le_eventCount)

end CompletionService
end Vegas.EventGraphRuntime
