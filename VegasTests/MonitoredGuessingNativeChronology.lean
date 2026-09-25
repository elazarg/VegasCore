/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeSchedule

/-! # Timely completion of each monitored native service visit -/

noncomputable section
namespace VegasTests.MonitoredGuessing
open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def nativeBefore (count : Nat) : List (ServiceInstruction nativeGraph) :=
  [.player alice, .player watcher, .wire] ++
    ((List.finRange nativeGraph.order.eventCount).take count).flatMap nativeVisit

theorem nativeBefore_succ (event : nativeGraph.EventId) :
    nativeBefore (event.val + 1) = nativeBefore event.val ++ nativeVisit event := by
  fin_cases event <;> rfl

theorem nativeBefore_ticks (event : nativeGraph.EventId) :
    serviceTicks (nativeBefore event.val) = nativeRuntime.deadline event - 1 := by
  fin_cases event <;> decide

theorem native_deadline_pos (event : nativeGraph.EventId) :
    0 < nativeRuntime.deadline event := by
  fin_cases event <;> decide

theorem nativeVisit_prefix_ticks (event : nativeGraph.EventId) :
    serviceTicks ([.grant event, .player (nativeOwner event),
      .includeLatest event (nativeOwner event)] ++
      List.replicate (nativeRuntime.deadline event) .tick) = nativeRuntime.deadline event := by
  fin_cases event <;> decide

theorem native_visit_completes (bit : Bool) (players : Player → nativeApp.Policy)
    (event : nativeGraph.EventId) (execution next : nativeApp.Execution)
    (invariant : execution.application.Invariant (nativeInputs bit))
    (available : event ∈ execution.application.config.cut.completed ∨
      execution.application.config.cut.Ready event)
    (reached : next ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      (nativeVisit event) execution).support) :
    event ∈ next.application.config.cut.completed := by
  rcases available with completed | ready
  · exact (nativeRuntime.runInteractionPlan_facts nativeLeaks (nativeInputs bit) players
      nativeNetwork _ execution next invariant reached).completed completed
  have strategic : (nativeGraph.actor? event).isSome = true := by rw [native_actor]; rfl
  obtain ⟨entered, activated⟩ :=
    invariant.activatedAt_eq_some_of_ready_actor event ready strategic
  have enteredLe := invariant.activated_le event entered activated
  obtain ⟨prior, priorMem, expired, expiredMem, finalMem⟩ :=
    nativeRuntime.runInteractionPlan_support_instruction nativeLeaks players nativeNetwork
      ([.grant event, .player (nativeOwner event), .includeLatest event (nativeOwner event)] ++
        List.replicate (nativeRuntime.deadline event) .tick) [] (.expire event)
      execution next reached
  have progress := nativeRuntime.runInteractionPlan_facts nativeLeaks (nativeInputs bit) players
    nativeNetwork _ execution prior invariant priorMem
  have expiredProgress := nativeRuntime.interactionStep_facts nativeLeaks (nativeInputs bit) players
    nativeNetwork (.expire event) prior expired progress.invariant expiredMem
  have suffix := nativeRuntime.runInteractionPlan_facts nativeLeaks (nativeInputs bit) players
    nativeNetwork [] expired next expiredProgress.invariant finalMem
  rcases progress.ready_or_completed event ready with completed | stillReady
  · exact suffix.completed (expiredProgress.completed completed)
  · apply suffix.completed
    apply nativeRuntime.interactionStep_expire_complete nativeLeaks players nativeNetwork
      event prior expired stillReady strategic entered
      (progress.activated event entered activated stillReady.1) _ expiredMem
    rw [progress.clock, nativeVisit_prefix_ticks]
    omega

theorem native_before_invariant (bit : Bool) (players : Player → nativeApp.Policy)
    (count : Nat) (execution : nativeApp.Execution)
    (reached : execution ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      (nativeBefore count) (nativeStart bit)).support) :
    execution.application.Invariant (nativeInputs bit) :=
  (nativeRuntime.runInteractionPlan_facts nativeLeaks (nativeInputs bit) players nativeNetwork _
    (nativeStart bit) execution (State.initial_invariant (nativeInputs bit)) reached).invariant

theorem native_before_completed (bit : Bool) (players : Player → nativeApp.Policy)
    (count : Nat) (bounded : count ≤ nativeGraph.order.eventCount)
    (execution : nativeApp.Execution)
    (reached : execution ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      (nativeBefore count) (nativeStart bit)).support) :
    ∀ event : nativeGraph.EventId, event.val < count →
      event ∈ execution.application.config.cut.completed := by
  induction count generalizing execution with
  | zero => intro event earlier; omega
  | succ count ih =>
      let current : nativeGraph.EventId := ⟨count, by omega⟩
      rw [nativeBefore_succ current, runInteractionPlan_append] at reached
      obtain ⟨prior, priorMem, visitMem⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      have earlier := ih (by omega) prior priorMem
      have invariant := native_before_invariant bit players count prior priorMem
      have progress := nativeRuntime.runInteractionPlan_facts nativeLeaks (nativeInputs bit) players
        nativeNetwork _ prior execution invariant visitMem
      intro event eventLt
      by_cases before : event.val < count
      · exact progress.completed (earlier event before)
      · have eqCurrent : event = current := Fin.ext (by dsimp [current]; omega)
        subst event
        apply native_visit_completes bit players current prior execution invariant _ visitMem
        by_cases completed : current ∈ prior.application.config.cut.completed
        · exact Or.inl completed
        · refine Or.inr ⟨completed, ?_⟩
          intro predecessor member
          exact earlier predecessor (nativeGraph.order.predecessor_lt member)

theorem native_before_available (bit : Bool) (players : Player → nativeApp.Policy)
    (event : nativeGraph.EventId) (execution : nativeApp.Execution)
    (reached : execution ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      (nativeBefore event.val) (nativeStart bit)).support) :
    event ∈ execution.application.config.cut.completed ∨
      execution.application.config.cut.Ready event := by
  by_cases completed : event ∈ execution.application.config.cut.completed
  · exact Or.inl completed
  · refine Or.inr ⟨completed, ?_⟩
    intro predecessor member
    exact native_before_completed bit players event.val (Nat.le_of_lt event.isLt) execution
      reached predecessor (nativeGraph.order.predecessor_lt member)

theorem native_before_timely (bit : Bool) (players : Player → nativeApp.Policy)
    (event : nativeGraph.EventId) (execution : nativeApp.Execution)
    (reached : execution ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      (nativeBefore event.val) (nativeStart bit)).support)
    (unfinished : event ∉ execution.application.config.cut.completed) :
    execution.application.WithinDeadline nativeRuntime event := by
  have ready :=
    (native_before_available bit players event execution reached).resolve_left unfinished
  have progress := nativeRuntime.runInteractionPlan_facts nativeLeaks (nativeInputs bit) players
    nativeNetwork _ (nativeStart bit) execution (State.initial_invariant (nativeInputs bit))
      reached
  obtain ⟨entered, activated⟩ := progress.invariant.activatedAt_eq_some_of_ready_actor event
    ready (by rw [native_actor]; rfl)
  simp only [State.WithinDeadline, activated]
  have clockEq := progress.clock
  rw [nativeBefore_ticks] at clockEq
  change execution.application.clock = 0 + (nativeRuntime.deadline event - 1) at clockEq
  have positive := native_deadline_pos event
  omega

theorem native_plan_complete (bit : Bool) (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution)
    (reached : execution ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      nativePlan (nativeStart bit)).support) :
    execution.application.config.cut.Terminal := by
  apply Finset.eq_univ_of_forall
  intro event
  exact native_before_completed bit players nativeGraph.order.eventCount (by rfl)
    execution reached event event.isLt


end VegasTests.MonitoredGuessing
