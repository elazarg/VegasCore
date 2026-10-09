/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeServiceCompletion
import Vegas.Pending.ReactiveServiceOpportunity

/-! # Owner opportunities in the public two-late service

The argument covers every raw history. An event that has not yet had an owner
callback must have become ready after the previous callback. Its activation
timestamp then bounds its age until the next scheduled callback.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeService

open SourceProgram EventGraph EventGraphRuntime Interaction
  GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource

private def servedAfter (event : nativeGraph.EventId) : Nat :=
  if event = aliceEvent then 1 else if event = bobBindEvent then 12 else 20

private def unservedFloor (event : nativeGraph.EventId) (position : Nat) : Nat :=
  if event = aliceEvent then 0 else if position < 5 then 0 else
    if event = bobBindEvent then 1 else if position < 12 then 1 else 3

private theorem clock_monotone : Monotone clockAt := by
  apply monotone_nat_of_le_succ
  intro position
  rw [clockAt_succ]
  omega

private theorem floor_before_clock (event : nativeGraph.EventId) (position : Nat) :
    unservedFloor event (position + 1) ≤ clockAt position := by
  unfold unservedFloor
  split
  · omega
  · split
    · omega
    · have first : 1 ≤ clockAt position := by
        have increasing := clock_monotone (show 3 ≤ position by omega)
        simpa only [show clockAt 3 = 1 by decide] using increasing
      split
      · exact first
      · split
        · exact first
        · have increasing := clock_monotone (show 10 ≤ position by omega)
          simpa only [show clockAt 10 = 3 by decide] using increasing

private theorem floor_increase_activation (weight : ℝ) (nonnegative : 0 ≤ weight)
    (event : nativeGraph.EventId) (owner : Player) (position : Nat)
    (view : app.EnvironmentView) (owned : nativeGraph.actor? event = some owner)
    (increasing : ¬ unservedFloor event (position + 1) ≤ unservedFloor event position) :
    stageChoice weight nonnegative position view = PMF.pure (.activate owner) := by
  change Fin 3 at event
  fin_cases event
  · change ¬ (0 ≤ 0) at increasing
    omega
  · have same : owner = bob := Option.some.inj owned.symm
    subst owner
    have positionEq : position = 4 := by
      simp only [unservedFloor, bobBindEvent, aliceEvent, ↓reduceIte] at increasing
      split_ifs at increasing <;> omega
    rw [positionEq]
    rfl
  · have same : owner = bob := Option.some.inj owned.symm
    subst owner
    have positionEq : position = 4 ∨ position = 11 := by
      simp only [unservedFloor, bobBindEvent, aliceEvent] at increasing
      split_ifs at increasing <;> omega
    rcases positionEq with rfl | rfl <;> rfl

private theorem record_activation (execution next : app.Execution)
    (event : nativeGraph.EventId) (owner : Player) (entered : Nat)
    (activated : execution.application.activatedAt event = some entered)
    (ready : execution.application.config.cut.Ready event)
    (reached : next ∈ (execution.environmentStep app (.activate owner)).support) :
    runtime.OwnerActivatedSince leaks next.environmentRecall event owner entered := by
  rw [environmentStep_recall_append execution next _ reached]
  refine ⟨⟨execution.observeEnvironment app, .activate owner⟩, by simp, rfl, activated, ?_⟩
  exact (State.publicView_eventReady _ event).mpr ready

private theorem ready_before_callback (execution next : app.Execution)
    (phase : CompletedPhase execution) {inputs : nativeGraph.Inputs} {ticks : Nat}
    (progress : State.ServiceProgress inputs ticks execution.application next.application)
    (event : nativeGraph.EventId)
    (position : servedAfter event - 1 ≤ execution.environmentRecall.length)
    (unfinished : event ∉ next.application.config.cut.completed) :
    execution.application.config.cut.Ready event := by
  have beforeUnfinished : event ∉ execution.application.config.cut.completed :=
    fun done => unfinished (progress.completed done)
  refine ⟨beforeUnfinished, ?_⟩
  change Fin 3 at event
  fin_cases event
  · change ∅ ⊆ execution.application.config.cut.completed
    exact Finset.empty_subset _
  · have aliceDone := (phase.afterAlice (by
      change 12 - 1 ≤ _ at position
      omega)).1
    intro predecessor earlier
    fin_cases predecessor
    · exact aliceDone
    · exact ((by decide : (1 : Fin 3) ∉ nativeGraph.order.predecessors bobBindEvent) earlier).elim
    · exact ((by decide : (2 : Fin 3) ∉ nativeGraph.order.predecessors bobBindEvent) earlier).elim
  · have bindingDone := (phase.afterBinding (by
      change 20 - 1 ≤ _ at position
      omega)).1
    have aliceDone := (phase.afterAlice (by
      change 20 - 1 ≤ _ at position
      omega)).1
    intro predecessor earlier
    fin_cases predecessor
    · exact aliceDone
    · exact bindingDone
    · exact ((by decide : (2 : Fin 3) ∉ nativeGraph.order.predecessors bobRevealEvent) earlier).elim

private theorem callback_command (weight : ℝ) (nonnegative : 0 ≤ weight)
    (event : nativeGraph.EventId) (owner : Player) (view : app.EnvironmentView)
    (owned : nativeGraph.actor? event = some owner) :
    stageChoice weight nonnegative (servedAfter event - 1) view =
      PMF.pure (.activate owner) := by
  change Fin 3 at event
  fin_cases event
  · have same : owner = alice := Option.some.inj owned.symm
    subst owner
    rfl
  · have same : owner = bob := Option.some.inj owned.symm
    subst owner
    rfl
  · have same : owner = bob := Option.some.inj owned.symm
    subst owner
    rfl

private structure OpportunityPhase (execution : app.Execution) : Prop where
  completed : CompletedPhase execution
  lower : ∀ event owner, nativeGraph.actor? event = some owner → ∀ entered,
    execution.application.activatedAt event = some entered →
      runtime.OwnerActivatedSince leaks execution.environmentRecall event owner entered ∨
        unservedFloor event execution.environmentRecall.length ≤ entered
  served : ∀ event owner, nativeGraph.actor? event = some owner →
    servedAfter event ≤ execution.environmentRecall.length → ∀ entered,
    execution.application.activatedAt event = some entered →
      runtime.OwnerActivatedSince leaks execution.environmentRecall event owner entered

private theorem opportunity_invariant (weight : ℝ) (nonnegative : 0 ≤ weight) :
    app.ServiceInvariant (scheduler weight nonnegative) OpportunityPhase where
  respond execution who action valid := by
    have timers := congrArg PublicView.activatedAt
      (runtime.reactive_respond_application leaks execution who action).2
    change (execution.respond app who action).application.activatedAt =
      execution.application.activatedAt at timers
    refine ⟨(completion_invariant weight nonnegative).respond execution who action valid.completed,
      ?_, ?_⟩
    · rw [app.respond_environmentRecall, timers]
      exact valid.lower
    · rw [app.respond_environmentRecall, timers]
      exact valid.served
  environment execution next command valid selected reached := by
    obtain ⟨inputs, invariant⟩ := valid.completed.invariant
    have progress := runtime.reactive_environment_progress leaks inputs execution next command
      invariant reached
    have start := (runtime.reactiveActivationStart leaks).environmentStep execution next command
      reached
    have appended := environmentStep_recall_append execution next command reached
    have length : next.environmentRecall.length = execution.environmentRecall.length + 1 := by
      rw [appended, List.length_append, List.length_singleton]
    have ready (event : nativeGraph.EventId) (entered : Nat)
        (activated : next.application.activatedAt event = some entered) :
        next.application.config.cut.Ready event :=
      ((progress.invariant.activated_iff event).mp (by rw [activated]; rfl)).1
    have carry {event : nativeGraph.EventId} {owner : Player} {entered : Nat}
        (recorded : runtime.OwnerActivatedSince leaks execution.environmentRecall
          event owner entered) :
        runtime.OwnerActivatedSince leaks next.environmentRecall event owner entered := by
      rw [appended]
      exact ownerActivatedSince_append recorded _
    refine ⟨(completion_invariant weight nonnegative).environment execution next command
      valid.completed selected reached, ?_, ?_⟩
    · intro event owner owned entered activated
      rw [length]
      rcases start.activationOrigin event entered activated (ready event entered activated).1
        with prior | recent
      · rcases valid.lower event owner owned entered prior with recorded | lower
        · exact Or.inl (carry recorded)
        · by_cases nonincreasing : unservedFloor event (execution.environmentRecall.length + 1) ≤
              unservedFloor event execution.environmentRecall.length
          · exact Or.inr (nonincreasing.trans lower)
          · have scheduled := floor_increase_activation weight nonnegative event owner
              execution.environmentRecall.length (execution.observeEnvironment app) owned
              nonincreasing
            change command ∈ (stageChoice weight nonnegative execution.environmentRecall.length
              (execution.observeEnvironment app)).support at selected
            rw [scheduled, PMF.mem_support_pure_iff] at selected
            have priorReady := ((invariant.activated_iff event).mp (by rw [prior]; rfl)).1
            exact Or.inl (record_activation execution next event owner entered prior priorReady
              (selected ▸ reached))
      · exact Or.inr ((floor_before_clock event execution.environmentRecall.length).trans
          (valid.completed.clocked ▸ recent))
    · intro event owner owned late entered activated
      rw [length] at late
      have position : servedAfter event - 1 ≤ execution.environmentRecall.length := by omega
      have priorReady := ready_before_callback execution next valid.completed progress event
        position (ready event entered activated).1
      obtain ⟨priorEntered, prior⟩ := invariant.activatedAt_eq_some_of_ready_actor event priorReady
        (by rw [owned]; rfl)
      have kept := progress.activated event priorEntered prior (ready event entered activated).1
      have same := Option.some.inj (kept.symm.trans activated)
      subst entered
      by_cases before : servedAfter event ≤ execution.environmentRecall.length
      · exact carry (valid.served event owner owned before priorEntered prior)
      · have exactPosition : execution.environmentRecall.length = servedAfter event - 1 := by
          change Fin 3 at event
          fin_cases event <;> simp only [servedAfter, aliceEvent, bobBindEvent,
            ↓reduceIte] at before late ⊢ <;> omega
        have scheduled := callback_command weight nonnegative event owner
          (execution.observeEnvironment app) owned
        change command ∈ (stageChoice weight nonnegative execution.environmentRecall.length
          (execution.observeEnvironment app)).support at selected
        rw [exactPosition, scheduled, PMF.mem_support_pure_iff] at selected
        exact record_activation execution next event owner priorEntered prior priorReady
          (selected ▸ reached)

private theorem opportunity_initial (state : app.State) (supported : state ∈ initial.support) :
    OpportunityPhase (ReactiveApplication.Execution.initial app state) := by
  obtain ⟨source, _, rfl⟩ := PMF.support_map .. ▸ supported
  refine ⟨⟨⟨setup.eventInputs source, State.initial_invariant _⟩, rfl, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro entered activated
    change some 0 = some entered at activated
    exact (Option.some.inj activated).symm
  · intro impossible
    change 11 ≤ 0 at impossible
    omega
  · intro impossible
    change 19 ≤ 0 at impossible
    omega
  · intro impossible
    change 26 ≤ 0 at impossible
    omega
  · intro event owner _ entered _
    right
    change unservedFloor event 0 ≤ entered
    simp [unservedFloor]
  · intro event owner _ impossible
    change servedAfter event ≤ 0 at impossible
    unfold servedAfter at impossible
    split_ifs at impossible <;> omega

private theorem clock_age_before_service (event : nativeGraph.EventId) (position entered : Nat)
    (before : position < servedAfter event)
    (lower : unservedFloor event position ≤ entered) :
    clockAt position ≤ entered + delay event := by
  change Fin 3 at event
  fin_cases event
  · change position < 1 at before
    have zero : position = 0 := by omega
    rw [zero]
    change 0 ≤ entered + 0
    omega
  · change position < 12 at before
    by_cases early : position < 5
    · have increasing := clock_monotone (show position ≤ 4 by omega)
      have clock : clockAt position ≤ 1 := by
        simpa only [show clockAt 4 = 1 by decide] using increasing
      change clockAt position ≤ entered + 2
      omega
    · have increasing := clock_monotone (show position ≤ 11 by omega)
      have clock : clockAt position ≤ 3 := by
        simpa only [show clockAt 11 = 3 by decide] using increasing
      have floor : 1 ≤ entered := by
        simpa [unservedFloor, aliceEvent, bobBindEvent, early] using lower
      change clockAt position ≤ entered + 2
      omega
  · change position < 20 at before
    by_cases early : position < 5
    · have increasing := clock_monotone (show position ≤ 4 by omega)
      have clock : clockAt position ≤ 1 := by
        simpa only [show clockAt 4 = 1 by decide] using increasing
      change clockAt position ≤ entered + 3
      omega
    · by_cases middle : position < 12
      · have increasing := clock_monotone (show position ≤ 11 by omega)
        have clock : clockAt position ≤ 3 := by
          simpa only [show clockAt 11 = 3 by decide] using increasing
        change clockAt position ≤ entered + 3
        omega
      · have increasing := clock_monotone (show position ≤ 19 by omega)
        have clock : clockAt position ≤ 6 := by
          simpa only [show clockAt 19 = 6 by decide] using increasing
        have floor : 3 ≤ entered := by
          simpa [unservedFloor, aliceEvent, bobBindEvent, early, middle] using lower
        change clockAt position ≤ entered + 3
        omega

/-- The actual public scheduler supplies an owner callback within the declared
reaction delay on every legal raw history. -/
theorem opportunity (weight : ℝ) (nonnegative : 0 ≤ weight) :
    runtime.Opportunity leaks initial horizon (scheduler weight nonnegative) delay := by
  intro control trace event owner entered owned _ activated aged
  have valid := (opportunity_invariant weight nonnegative).history initial horizon
    opportunity_initial trace
  change OpportunityPhase control.execution at valid
  by_cases served : servedAfter event ≤ control.execution.environmentRecall.length
  · exact valid.served event owner owned served entered activated
  · rcases valid.lower event owner owned entered activated with recorded | lower
    · exact recorded
    · have age := clock_age_before_service event control.execution.environmentRecall.length
        entered (by omega) lower
      rw [← valid.completed.clocked] at age
      omega

end Vegas.Examples.LateOpeningRuntimeService
