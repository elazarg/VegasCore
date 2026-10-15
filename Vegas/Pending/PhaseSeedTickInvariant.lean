/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedClosedBound
import Vegas.Pending.PhaseSeedClockProgress
import Vegas.Pending.PhaseSeedCalendarProperties

/-! # Actual calendar tick closure preserves original event deadlines

The invariant follows genuine unrestricted player responses and commands of the
fixed original-seed calendar. A still-ready coordinate closed at this clock is
strictly before its deadline; a due query instead resolves its physical event.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
/-- Every actual expiry reply resolves the selected old physical coordinate,
including the immediate-normalization case where the static event is retried. -/
theorem environment_expiry_resolves (execution next : (app).Execution)
    {inputs : graph.Inputs} (valid : execution.application.Invariant inputs)
    (ordered : execution.application.Ordered) {owner : Player}
    {coordinate : CommitAttemptEvent graph}
    (request : execution.application.SeedRequest owner coordinate)
    (due : runtime.deadline coordinate.event ≤ execution.application.current.native.clock -
      (execution.application.current.native.activatedAt coordinate.event).getD
        execution.application.current.native.clock)
    (reached : next ∈ (execution.environmentStep app
      (.application (.expire coordinate.event))).support) :
    coordinate.attempt ≠ next.application.attempt ∨
      coordinate.event ∈ next.application.current.native.config.cut.completed := by
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at reached
  obtain ⟨state, moved, rfl⟩ := PMF.support_map .. ▸ reached
  exact PhaseRuntimeState.expire_resolves_of_request runtime execution.application state
    valid ordered request due moved

theorem selected_bound (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (execution next : (app).Execution)
    {inputs : graph.Inputs} (valid : execution.application.Invariant inputs)
    (ordered : execution.application.Ordered) (command : (app).Command)
    (chosen : command = (controller runtime leaks delay bound priority).choose seeds
      execution.environmentRecall (execution.observeEnvironment app))
    (reached : next ∈ (execution.environmentStep app command).support)
    (coordinate : PhaseSeedAddress graph)
    (selected : selectOpen runtime leaks
      (replayClosed runtime leaks priority seeds.1 execution.environmentRecall)
      (execution.observeEnvironment app)
      (priority seeds.1 execution.environmentRecall
        (execution.observeEnvironment app)) = some coordinate) :
    ∃ entered, ClosedCoordinateBound runtime execution.application.current.native.clock entered
      coordinate.1 next.application := by
  have member := (Finset.mem_filter.mp (selectOpen_mem runtime leaks selected)).1
  obtain ⟨owner, publicRequest⟩ := (PhaseSeedScheduler.mem_eligible runtime leaks _ _).mp member
  have request := (PhaseRuntimeState.requests_publicView _ valid owner coordinate.1).mp
    publicRequest
  have namespaceProgress := (phaseApplication_namespace_progress runtime leaks).environmentStep
    execution next command reached ordered
  have clockProgress := (phaseApplication_clock_monotone runtime leaks).environmentStep
    execution next command reached
  have ready := request.2.2.1
  have acting := request.2.2.2.1
  obtain ⟨entered, activated⟩ := valid.active.activatedAt_eq_some_of_ready_actor
    coordinate.1.event ready (by simp only [acting, Option.isSome_some])
  have enteredLe := valid.active.activated_le coordinate.1.event entered activated
  refine ⟨entered, clockProgress, enteredLe, ?_, ?_, ?_⟩
  · rw [request.1]
    exact namespaceProgress.1
  · rw [request.1]
    exact namespaceProgress.2
  · intro current
    have same : execution.application.attempt = next.application.attempt :=
      request.1.symm.trans current
    obtain ⟨ticks, progress⟩ :=
      (phaseApplication_serviceProgress runtime leaks).environmentStep execution next command
        reached inputs valid ordered same
    by_cases completed : coordinate.1.event ∈ next.application.current.native.config.cut.completed
    · exact Or.inl completed
    · right
      have readyAfter := progress.ready_or_completed coordinate.1.event ready
      rcases readyAfter with impossible | readyAfter
      · exact False.elim (completed impossible)
      · refine ⟨readyAfter,
          progress.activated coordinate.1.event entered activated completed, ?_⟩
        by_contra notEarly
        have due : runtime.deadline coordinate.1.event ≤
            execution.application.current.native.clock -
              (execution.application.current.native.activatedAt coordinate.1.event).getD
                execution.application.current.native.clock := by
          rw [activated, Option.getD_some]
          omega
        let query := PhaseSeedInput.operational coordinate.1.attempt
          (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner
            execution.environmentRecall (execution.observeEnvironment app))
        have queryDue : runtime.deadline coordinate.1.event ≤ query.elapsed := due
        have expires := decision_deadline runtime delay bound coordinate (seeds.2 coordinate)
          query queryDue
        dsimp only [query] at expires
        have commandEq : command = .application (.expire coordinate.1.event) := by
          rw [chosen]
          simp only [ReactiveApplication.AddressedScheduler.choose, controller, selected,
            Option.bind_some, acting, Option.map_some, reply, expires]
        have resolved := environment_expiry_resolves runtime leaks execution next valid ordered
          request due (by rwa [← commandEq])
        rcases resolved with retired | done
        · exact retired current
        · exact completed done

structure TickSafe (delay : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (inputs : graph.Inputs) (execution : (app).Execution) : Prop where
  invariant : execution.application.Invariant inputs
  ordered : execution.application.Ordered
  closed : ∀ key ∈ replayClosed runtime leaks priority seeds.1 execution.environmentRecall,
    ∃ entered, ClosedCoordinateBound runtime key.1 entered key.2.1 execution.application

theorem initial_tickSafe (delay : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    {inputs : graph.Inputs} (state : PhaseRuntimeState graph)
    (valid : state.Invariant inputs) (ordered : state.Ordered) :
    TickSafe runtime leaks delay priority seeds inputs
      (ReactiveApplication.Execution.initial app state) := by
  refine ⟨valid, ordered, ?_⟩
  intro key member
  exact False.elim (Finset.notMem_empty key member)

/-- Actual player responses are unrestricted. The environment side is exactly
the immutable original-seed calendar, with no native service contract premise. -/
theorem tickSafe_invariant (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (inputs : graph.Inputs) :
    (app).ServiceInvariant ((controller runtime leaks delay bound priority).family seeds)
      (TickSafe runtime leaks delay priority seeds inputs) where
  respond execution who action safe := by
    refine ⟨(phaseApplication_invariant runtime leaks inputs).respond execution who action
      safe.invariant, (phaseApplication_seedOrder runtime leaks).respond execution who action
        safe.ordered, ?_⟩
    intro key member
    rw [(app).respond_environmentRecall] at member
    obtain ⟨entered, closed⟩ := safe.closed key member
    exact ⟨entered, ClosedCoordinateBound.respond runtime leaks execution who action safe.invariant
      safe.ordered closed⟩
  environment execution next command safe chosen reached := by
    have chosenEq : command = (controller runtime leaks delay bound priority).choose seeds
        execution.environmentRecall (execution.observeEnvironment app) :=
      (PMF.mem_support_pure_iff _ _).mp chosen
    refine ⟨(phaseApplication_invariant runtime leaks inputs).environmentStep execution next command
      safe.invariant reached,
      (phaseApplication_seedOrder runtime leaks).environmentStep execution next command
        safe.ordered reached, ?_⟩
    intro key member
    rw [(app).environmentStep_environmentRecall execution next command reached,
      replayClosed_snoc] at member
    unfold closeAfter at member
    split at member
    · cases selected : selectOpen runtime leaks
          (replayClosed runtime leaks priority seeds.1 execution.environmentRecall)
          (execution.observeEnvironment app)
          (priority seeds.1 execution.environmentRecall
            (execution.observeEnvironment app)) with
      | none =>
          simp only [selected, Option.elim_none] at member
          obtain ⟨entered, closed⟩ := safe.closed key member
          exact ⟨entered, ClosedCoordinateBound.environmentStep runtime leaks execution next command
            safe.invariant safe.ordered reached closed⟩
      | some coordinate =>
          simp only [selected, Option.elim_some, Finset.mem_insert] at member
          rcases member with rfl | previous
          · exact selected_bound runtime leaks delay bound priority seeds execution next
              safe.invariant safe.ordered command chosenEq reached coordinate selected
          · obtain ⟨entered, closed⟩ := safe.closed key previous
            exact ⟨entered, ClosedCoordinateBound.environmentStep runtime leaks execution next
              command safe.invariant safe.ordered reached closed⟩
    · obtain ⟨entered, closed⟩ := safe.closed key member
      exact ⟨entered, ClosedCoordinateBound.environmentStep runtime leaks execution next command
        safe.invariant safe.ordered reached closed⟩

end Vegas.EventGraphRuntime.PhaseSeedCalendar
