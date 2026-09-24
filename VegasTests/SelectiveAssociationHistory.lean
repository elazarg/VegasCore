/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSchedule
import Interaction.ReactiveRoundReachability

/-! # Native service facts at arbitrary decision histories

The service analysis uses round evaluation. These lemmas connect an arbitrary
legal menu history at an event's response cursor to that evaluation, including
histories that have probability zero under a proposed equilibrium.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def nativeBeforeResponse (event : nativeGraph.EventId) : List (ServiceInstruction nativeGraph) :=
  nativeBefore event.val ++ [.grant event]

def nativeAfterResponse (event : nativeGraph.EventId) : List (ServiceInstruction nativeGraph) :=
  [.includeLatest event (nativeOwner event)] ++
    List.replicate (nativeRuntime.deadline event) .tick ++ [.expire event] ++
      ((List.finRange nativeGraph.order.eventCount).drop (event.val + 1)).flatMap nativeVisit

theorem native_response_split (event : nativeGraph.EventId) :
    nativePlan = nativeBeforeResponse event ++
      .player (nativeOwner event) :: nativeAfterResponse event := by
  fin_cases event <;> rfl

theorem native_response_selected (event : nativeGraph.EventId) :
    nativePlan[(nativeBeforeResponse event).length]? = some (.player (nativeOwner event)) := by
  rw [native_response_split event, List.getElem?_append_right (by omega), Nat.sub_self]
  rfl

theorem native_roundsFrom_prefix (players : Player → nativeApp.Policy)
    (before after : List (ServiceInstruction nativeGraph))
    (split : nativePlan = before ++ after) :
    nativeApp.roundsFrom (FinDist.pure nativeInitial) nativeScheduler players before.length =
      nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork before nativeRoot := by
  rw [ReactiveApplication.roundsFrom, FinDist.pure_bind]
  exact native_prefix_rounds players before after split

/-- A legal pending response has an actual predecessor under full-support
play. The equilibrium strategy and beliefs play no role in this fact. -/
theorem native_decision_predecessor (event : nativeGraph.EventId) (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control))
    (active : control.actor = some (nativeOwner event))
    (position : control.execution.environmentRecall.length =
      (nativeBeforeResponse event).length + 1) :
    control.remaining + (nativeBeforeResponse event).length + 1 = nativeHorizon ∧
    ∃ prior ∈ (nativeRuntime.runInteractionPlan nativeLeaks nativeMenu.uniformResponses
        nativeNetwork (nativeBeforeResponse event) nativeRoot).support,
      control.execution ∈
        (prior.environmentStep nativeApp (.activate (nativeOwner event))).support := by
  have valid := nativeMenu.roundSupported_uniform (FinDist.pure nativeInitial) nativeHorizon
    nativeScheduler trace
  rcases valid with ⟨accounted, supported⟩
  rw [active] at supported
  obtain ⟨count, prior, command, countEq, priorMem, commandMem, _, observed⟩ := supported
  have countSame : count = (nativeBeforeResponse event).length := by omega
  subst count
  refine ⟨by omega, prior, ?_, ?_⟩
  · rw [native_roundsFrom_prefix nativeMenu.uniformResponses (nativeBeforeResponse event)
      (.player (nativeOwner event) :: nativeAfterResponse event) (native_response_split event)]
      at priorMem
    exact priorMem
  · have cursor := nativeApp.roundsFrom_recall (FinDist.pure nativeInitial) nativeScheduler
      nativeMenu.uniformResponses _ prior priorMem
    simp only [nativeScheduler, cursor, native_response_selected, interactionInstruction,
      FinDist.mem_support_pure] at commandMem
    subst command
    exact observed

theorem native_response_prefix_facts (players : Player → nativeApp.Policy)
    (event : nativeGraph.EventId) (execution : nativeApp.Execution)
    (reached : execution ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      (nativeBeforeResponse event) nativeRoot).support) :
    execution.application.Invariant nativeInputs ∧
    execution.application.clock = nativeRuntime.deadline event - 1 ∧
    (∀ earlier : nativeGraph.EventId, earlier.val < event.val →
      earlier ∈ execution.application.config.cut.completed) := by
  rw [nativeBeforeResponse, runInteractionPlan_append] at reached
  obtain ⟨prior, priorMem, grantMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  have before := nativeRuntime.runInteractionPlan_facts nativeLeaks nativeInputs players
    nativeNetwork _ nativeRoot prior (State.initial_invariant nativeInputs) priorMem
  have grant := nativeRuntime.runInteractionPlan_facts nativeLeaks nativeInputs players
    nativeNetwork _ prior execution before.invariant grantMem
  refine ⟨grant.invariant, ?_, ?_⟩
  · rw [grant.clock, before.clock, nativeBefore_ticks]
    change 0 + (nativeRuntime.deadline event - 1) + 0 = nativeRuntime.deadline event - 1
    omega
  · intro earlier beforeEvent
    exact grant.completed (native_before_completed players event.val
      (Nat.le_of_lt event.isLt) prior priorMem earlier beforeEvent)

/-- At every legal history at the response cursor, the current event is
already settled or ready within its deadline; all earlier events are settled. -/
theorem native_decision_service (event : nativeGraph.EventId) (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control))
    (active : control.actor = some (nativeOwner event))
    (position : control.execution.environmentRecall.length =
      (nativeBeforeResponse event).length + 1) :
    control.execution.application.Invariant nativeInputs ∧
    (event ∈ control.execution.application.config.cut.completed ∨
      (control.execution.application.config.cut.Ready event ∧
        control.execution.application.WithinDeadline nativeRuntime event)) := by
  obtain ⟨_, prior, priorMem, activated⟩ :=
    native_decision_predecessor event control trace active position
  obtain ⟨invariant, clockEq, earlier⟩ :=
    native_response_prefix_facts nativeMenu.uniformResponses event prior priorMem
  have progress := nativeRuntime.reactive_environment_progress nativeLeaks nativeInputs prior
    control.execution (.activate (nativeOwner event)) invariant activated
  refine ⟨progress.invariant, ?_⟩
  by_cases completed : event ∈ control.execution.application.config.cut.completed
  · exact Or.inl completed
  · have ready : control.execution.application.config.cut.Ready event := by
      refine ⟨completed, ?_⟩
      intro predecessor member
      exact progress.completed (earlier predecessor (nativeGraph.order.predecessor_lt member))
    refine Or.inr ⟨ready, ?_⟩
    obtain ⟨entered, entry⟩ := progress.invariant.activatedAt_eq_some_of_ready_actor event ready
      (by rw [native_actor]; rfl)
    simp only [State.WithinDeadline, entry]
    have clockAfter := progress.clock
    change control.execution.application.clock = prior.application.clock + 0 at clockAfter
    have positive := native_deadline_pos event
    omega

end VegasTests.SelectiveAssociation
