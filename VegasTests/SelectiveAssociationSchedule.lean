/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationNative
import Vegas.Pending.ReactiveServiceCompletion

/-! # Timely service and completion of the selective-association game

The fixed calendar offers each owner an unrestricted response before its
reserved inclusion. Its powers-of-two deadlines make that response timely
even when earlier players omitted every action. Each visit then settles its
event, so these facts quantify over all behavioral policies.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

variable {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}

def nativeRoot : (serviceApp observation).Execution := .initial (serviceApp observation)
  nativeInitial

def nativeBefore (count : Nat) : List (ServiceInstruction nativeGraph) :=
  [.player alice, .player bob] ++
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

theorem native_visit_completes (players : Player → (serviceApp observation).Policy)
    (event : nativeGraph.EventId) (execution next : (serviceApp observation).Execution)
    (invariant : execution.application.Invariant nativeInputs)
    (available : event ∈ execution.application.config.cut.completed ∨
      execution.application.config.cut.Ready event)
    (reached : next ∈ (nativeRuntime.runInteractionPlan observation players (serviceNetwork
      observation)
      (nativeVisit event) execution).support) :
    event ∈ next.application.config.cut.completed := by
  rcases available with completed | ready
  · exact (nativeRuntime.runInteractionPlan_facts observation nativeInputs players
      (serviceNetwork observation) _ execution next invariant reached).completed completed
  have strategic : (nativeGraph.actor? event).isSome = true := by rw [native_actor]; rfl
  obtain ⟨entered, activated⟩ :=
    invariant.activatedAt_eq_some_of_ready_actor event ready strategic
  have enteredLe := invariant.activated_le event entered activated
  obtain ⟨prior, priorMem, expired, expiredMem, finalMem⟩ :=
    nativeRuntime.runInteractionPlan_support_instruction observation players (serviceNetwork
      observation)
      ([.grant event, .player (nativeOwner event), .includeLatest event (nativeOwner event)] ++
        List.replicate (nativeRuntime.deadline event) .tick) [] (.expire event)
      execution next reached
  have progress := nativeRuntime.runInteractionPlan_facts observation nativeInputs players
    (serviceNetwork observation) _ execution prior invariant priorMem
  have expiredProgress := nativeRuntime.interactionStep_facts observation nativeInputs players
    (serviceNetwork observation) (.expire event) prior expired progress.invariant expiredMem
  have suffix := nativeRuntime.runInteractionPlan_facts observation nativeInputs players
    (serviceNetwork observation) [] expired next expiredProgress.invariant finalMem
  rcases progress.ready_or_completed event ready with completed | stillReady
  · exact suffix.completed (expiredProgress.completed completed)
  · apply suffix.completed
    apply nativeRuntime.interactionStep_expire_complete observation players (serviceNetwork
      observation)
      event prior expired stillReady strategic entered
      (progress.activated event entered activated stillReady.1) _ expiredMem
    rw [progress.clock, nativeVisit_prefix_ticks]
    omega

theorem native_before_invariant (players : Player → (serviceApp observation).Policy)
    (count : Nat) (execution : (serviceApp observation).Execution)
    (reached : execution ∈ (nativeRuntime.runInteractionPlan observation players (serviceNetwork
      observation)
      (nativeBefore count) nativeRoot).support) :
    execution.application.Invariant nativeInputs :=
  (nativeRuntime.runInteractionPlan_facts observation nativeInputs players (serviceNetwork
    observation) _
    nativeRoot execution (State.initial_invariant nativeInputs) reached).invariant

theorem native_before_completed (players : Player → (serviceApp observation).Policy)
    (count : Nat) (bounded : count ≤ nativeGraph.order.eventCount)
    (execution : (serviceApp observation).Execution)
    (reached : execution ∈ (nativeRuntime.runInteractionPlan observation players (serviceNetwork
      observation)
      (nativeBefore count) nativeRoot).support) :
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
      have invariant := native_before_invariant players count prior priorMem
      have progress := nativeRuntime.runInteractionPlan_facts observation nativeInputs players
        (serviceNetwork observation) _ prior execution invariant visitMem
      intro event eventLt
      by_cases before : event.val < count
      · exact progress.completed (earlier event before)
      · have eqCurrent : event = current := Fin.ext (by dsimp [current]; omega)
        subst event
        apply native_visit_completes players current prior execution invariant _ visitMem
        by_cases completed : current ∈ prior.application.config.cut.completed
        · exact Or.inl completed
        · refine Or.inr ⟨completed, ?_⟩
          intro predecessor member
          exact earlier predecessor (nativeGraph.order.predecessor_lt member)

theorem native_before_available (players : Player → (serviceApp observation).Policy)
    (event : nativeGraph.EventId) (execution : (serviceApp observation).Execution)
    (reached : execution ∈ (nativeRuntime.runInteractionPlan observation players (serviceNetwork
      observation)
      (nativeBefore event.val) nativeRoot).support) :
    event ∈ execution.application.config.cut.completed ∨
      execution.application.config.cut.Ready event := by
  by_cases completed : event ∈ execution.application.config.cut.completed
  · exact Or.inl completed
  · refine Or.inr ⟨completed, ?_⟩
    intro predecessor member
    exact native_before_completed players event.val (Nat.le_of_lt event.isLt) execution
      reached predecessor (nativeGraph.order.predecessor_lt member)

theorem native_before_timely (players : Player → (serviceApp observation).Policy)
    (event : nativeGraph.EventId) (execution : (serviceApp observation).Execution)
    (reached : execution ∈ (nativeRuntime.runInteractionPlan observation players (serviceNetwork
      observation)
      (nativeBefore event.val) nativeRoot).support)
    (unfinished : event ∉ execution.application.config.cut.completed) :
    execution.application.WithinDeadline nativeRuntime event := by
  have ready := (native_before_available players event execution reached).resolve_left unfinished
  have progress := nativeRuntime.runInteractionPlan_facts observation nativeInputs players
    (serviceNetwork observation) _ nativeRoot execution (State.initial_invariant nativeInputs)
      reached
  obtain ⟨entered, activated⟩ := progress.invariant.activatedAt_eq_some_of_ready_actor event
    ready (by rw [native_actor]; rfl)
  simp only [State.WithinDeadline, activated]
  have clockEq := progress.clock
  rw [nativeBefore_ticks] at clockEq
  change execution.application.clock = 0 + (nativeRuntime.deadline event - 1) at clockEq
  have positive := native_deadline_pos event
  omega

theorem native_plan_complete (players : Player → (serviceApp observation).Policy)
    (execution : (serviceApp observation).Execution)
    (reached : execution ∈ (nativeRuntime.runInteractionPlan observation players (serviceNetwork
      observation)
      nativePlan nativeRoot).support) :
    execution.application.config.cut.Terminal := by
  apply Finset.eq_univ_of_forall
  intro event
  exact native_before_completed players nativeGraph.order.eventCount (by rfl)
    execution reached event event.isLt

/-- The explicit instruction evaluator is exactly the native scheduler, at
every suffix and for arbitrary behavioral policies. -/
theorem native_segment_rounds (players : Player → (serviceApp observation).Policy)
    (before rest after : List (ServiceInstruction nativeGraph))
    (split : nativePlan = before ++ rest ++ after) (execution : (serviceApp observation).Execution)
    (position : execution.environmentRecall.length = before.length) :
    (serviceApp observation).runRounds (serviceScheduler observation) players rest.length
      execution =
      nativeRuntime.runInteractionPlan observation players (serviceNetwork observation) rest
        execution := by
  induction rest generalizing before execution with
  | nil => rfl
  | cons instruction rest ih =>
      have selected : nativePlan[before.length]? = some instruction := by
        rw [split, List.append_assoc, List.getElem?_append_right (by omega), Nat.sub_self]
        rfl
      have step : (serviceApp observation).round (serviceScheduler observation) players execution =
          nativeRuntime.interactionStep observation players (serviceNetwork observation) instruction
            execution := by
        simp only [ReactiveApplication.round, serviceScheduler, position, selected,
          interactionStep]
      rw [List.length_cons, ReactiveApplication.runRounds, step, runInteractionPlan]
      apply FinDist.bind_congr
      intro next supported
      apply ih (before ++ [instruction])
      · simpa only [List.append_assoc, List.singleton_append] using split
      · have advanced := nativeRuntime.interactionStep_recall observation players
          (serviceNetwork observation)
          instruction execution next supported
        simp only [List.length_append, List.length_singleton]
        omega

theorem native_plan_rounds (players : Player → (serviceApp observation).Policy) :
    (serviceApp observation).runRounds (serviceScheduler observation) players nativeHorizon
      nativeRoot =
      nativeRuntime.runInteractionPlan observation players (serviceNetwork observation)
        nativePlan nativeRoot :=
  native_segment_rounds players [] nativePlan [] (List.append_nil _).symm nativeRoot rfl

theorem native_prefix_rounds (players : Player → (serviceApp observation).Policy)
    (before after : List (ServiceInstruction nativeGraph))
    (split : nativePlan = before ++ after) :
    (serviceApp observation).runRounds (serviceScheduler observation) players before.length
      nativeRoot =
      nativeRuntime.runInteractionPlan observation players (serviceNetwork observation) before
        nativeRoot :=
  native_segment_rounds players [] before after split nativeRoot rfl

theorem native_rounds_complete (players : Player → (serviceApp observation).Policy)
    (execution : (serviceApp observation).Execution)
    (reached : execution ∈ ((serviceApp observation).runRounds (serviceScheduler observation)
      players nativeHorizon
      nativeRoot).support) : execution.application.config.cut.Terminal := by
  rw [native_plan_rounds] at reached
  exact native_plan_complete players execution reached

end VegasTests.SelectiveAssociation
