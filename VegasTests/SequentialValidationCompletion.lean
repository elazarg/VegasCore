/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationResponse

/-! # All player behavior reaches a completed graph before the native horizon -/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

def nativeTailTicks : Nat → Nat → Nat
  | _, 0 => 0
  | index, count + 1 => (nativeTailCommand index).clockTicks + nativeTailTicks (index + 1) count

theorem native_tail_add (index first second : Nat) (state : State nativeGraph) :
    nativeTail index (first + second) state =
      (nativeTail index first state).bind (nativeTail (index + first) second) := by
  induction first generalizing index state with
  | zero => simp only [Nat.zero_add, Nat.add_zero, nativeTail, FinDist.pure_bind]
  | succ first ih =>
      simp only [Nat.succ_add, nativeTail, FinDist.bind_bind]
      apply FinDist.bind_congr
      intro next _
      simpa only [Nat.add_assoc, Nat.add_comm 1 first] using ih (index + 1) next

theorem native_tail_progress (inputs : nativeGraph.Inputs) (index count : Nat)
    (state next : State nativeGraph) (valid : state.Invariant inputs)
    (reached : next ∈ (nativeTail index count state).support) :
    State.ServiceProgress inputs (nativeTailTicks index count) state next := by
  induction count generalizing index state with
  | zero => cases FinDist.mem_support_pure.mp reached; exact .refl valid
  | succ count ih =>
      obtain ⟨middle, supported, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      have step : State.ServiceProgress inputs (nativeTailCommand index).clockTicks state middle :=
        ⟨environmentStep_invariant nativeRuntime state middle _ valid supported,
          environmentStep_completed_subset nativeRuntime state middle _ supported,
          environmentStep_clock nativeRuntime state middle _ supported,
          environmentStep_activatedAt_of_not_completed nativeRuntime state middle _ valid supported⟩
      exact step.trans (ih (index + 1) middle step.invariant moved)

theorem native_window_completes (inputs : nativeGraph.Inputs) (event : nativeGraph.EventId)
    (state next : State nativeGraph) (valid : state.Invariant inputs)
    (ready : state.config.cut.Ready event)
    (reached : next ∈ (nativeTail (12 + 11 * event.val) 11 state).support) :
    event ∈ next.config.cut.completed := by
  rw [show 11 = 10 + 1 from rfl, native_tail_add] at reached
  obtain ⟨middle, supported, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  have progress := native_tail_progress inputs _ _ state middle valid supported
  have ticks : nativeTailTicks (12 + 11 * event.val) 10 = 10 := by fin_cases event <;> decide
  have command : nativeTailCommand (12 + 11 * event.val + 10) = .expire event := by
    fin_cases event <;> rfl
  have last : next ∈ (environmentStep nativeRuntime middle (.expire event)).support := by
    simpa only [nativeTail, command, FinDist.bind_pure] using moved
  rcases progress.ready_or_completed event ready with done | stillReady
  · exact environmentStep_completed_subset nativeRuntime middle next _ last done
  · have strategic : (nativeGraph.actor? event).isSome = true := by fin_cases event <;> decide
    obtain ⟨entered, activated⟩ := Option.isSome_iff_exists.mp
      ((valid.activated_iff event).2 ⟨ready, strategic⟩)
    have middleActivated := progress.activated event entered activated stillReady.1
    have enteredLe := valid.activated_le event entered activated
    apply environmentStep_expire_complete nativeRuntime middle next event stillReady strategic
      entered middleActivated _ last
    have clock := progress.clock
    rw [ticks] at clock
    change 10 ≤ middle.clock - entered
    omega

theorem native_predecessor_index (event predecessor : nativeGraph.EventId)
    (prior : predecessor ∈ nativeGraph.order.predecessors event) : predecessor.val < event.val := by
  fin_cases event <;> fin_cases predecessor <;> first | contradiction | (decide +kernel)

theorem native_tail_completes (inputs : nativeGraph.Inputs) (state next : State nativeGraph)
    (valid : state.Invariant inputs) (reached : next ∈ (nativeTail 12 44 state).support) :
    next.config.cut.Terminal := by
  have finish : ∀ count index (before after : State nativeGraph), index + count = 4 →
      before.Invariant inputs →
      (∀ event : nativeGraph.EventId, event.val < index → event ∈ before.config.cut.completed) →
      after ∈ (nativeTail (12 + 11 * index) (count * 11) before).support →
        after.config.cut.Terminal := by
    intro count
    induction count with
    | zero =>
        intro index before after sum _ completedBefore member
        simp only [nativeTail, FinDist.mem_support_pure] at member
        subst after
        change before.config.cut.completed = Finset.univ
        apply Finset.eq_univ_of_forall
        intro event
        apply completedBefore event
        have bound : event.val < 4 := event.isLt
        omega
    | succ count ih =>
        intro index before after sum invariant completedBefore member
        let event : nativeGraph.EventId := ⟨index, by change index < 4; omega⟩
        rw [show (count + 1) * 11 = 11 + count * 11 by omega, native_tail_add] at member
        obtain ⟨middle, supported, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ member)
        have progress := native_tail_progress inputs _ _ before middle invariant supported
        have done : event ∈ middle.config.cut.completed := by
          by_cases already : event ∈ before.config.cut.completed
          · exact progress.completed already
          · apply native_window_completes inputs event before middle invariant _ supported
            refine ⟨already, ?_⟩
            intro predecessor earlier
            exact completedBefore predecessor (native_predecessor_index event predecessor earlier)
        apply ih (index + 1) middle after (by omega) progress.invariant
        · intro query earlier
          by_cases old : query.val < index
          · exact progress.completed (completedBefore query old)
          · have same : query = event := Fin.ext (by change query.val = index; omega)
            exact same.symm ▸ done
        · convert moved using 1
  exact finish 4 0 state next rfl valid (by intro event impossible; omega) reached

theorem native_rounds_length (players : Bool → nativeApp.Policy) (count : Nat)
    (execution next : nativeApp.Execution)
    (reached : next ∈ (nativeApp.runRounds nativeScheduler players count execution).support) :
    next.environmentRecall.length = execution.environmentRecall.length + count := by
  induction count generalizing execution with
  | zero => cases FinDist.mem_support_pure.mp reached; omega
  | succ count ih =>
      obtain ⟨middle, supported, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      rw [ih middle moved, native_round_length players execution middle supported]
      omega

/-- The timeout suffix completes the actual graph under arbitrary raw player policies. -/
theorem native_runtime_completes (players : Bool → nativeApp.Policy) (bit : Bool)
    (next : nativeApp.Execution)
    (reached : next ∈ (nativeApp.runRounds nativeScheduler players 56
      (nativeInitialExecution bit)).support) : next.application.config.cut.Terminal := by
  rw [show 56 = 12 + 44 from rfl, nativeApp.runRounds_add] at reached
  obtain ⟨middle, supported, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  have position : middle.environmentRecall.length = 12 :=
    native_rounds_length players 12 _ middle supported
  have valid := ((nativeRuntime.reactiveStateInvariant nativeLeaks
    (sourceSetup.eventInputs (initialState bit))).policyInvariant nativeApp players).runRounds
      nativeScheduler 12 (nativeInitialExecution bit) middle (State.initial_invariant _) supported
  have projected : next.application ∈
      ((nativeApp.runRounds nativeScheduler players 44 middle).map
        ReactiveApplication.Execution.application).support := by
    rw [FinDist.support_map]
    exact ⟨next, moved, rfl⟩
  rw [native_run_tail players 44 12 middle position (by omega) (by omega)] at projected
  exact native_tail_completes _ middle.application next.application valid projected

end VegasTests.SequentialValidation
