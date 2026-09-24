/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationGuessSelection
import VegasTests.SelectiveAssociationOpeningEquilibrium

/-! # Settlement of Bob's final binding response

An omitted or rejected packet reaches ordinary timeout failure before later
players act. Successful binding results persist throughout the remaining play.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory GameTheory.Protocol

def nativeBobBindingDelay : List (ServiceInstruction nativeGraph) :=
  List.replicate (nativeRuntime.deadline bobBinding) .tick ++ [.expire bobBinding]

theorem native_bob_binding_plan_preserves (players : Player → nativeApp.Policy)
    (value : PublicationResult Bool) (plan : List (ServiceInstruction nativeGraph))
    (execution next : nativeApp.Execution)
    (stored : bobBindingRef.get? execution.application.config.store = some value)
    (supported : next ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      plan execution).support) :
    bobBindingRef.get? next.application.config.store = some value := by
  induction plan generalizing execution with
  | nil => cases FinDist.mem_support_pure.mp supported; exact stored
  | cons instruction rest ih =>
      obtain ⟨middle, middleMem, restMem⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      obtain ⟨command, _, stepped⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ middleMem)
      exact ih middle ((ReactiveApplication.Invariant.policyInvariant nativeApp
        (native_binding_invariant bob value) players).dispatch
          command execution middle stored stepped) restMem

theorem native_bob_binding_timeout (players : Player → nativeApp.Policy)
    (execution next : nativeApp.Execution)
    (valid : execution.application.Invariant nativeInputs)
    (ready : execution.application.config.cut.Ready bobBinding)
    (supported : next ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      nativeBobBindingDelay execution).support) :
    bobBindingRef.get? next.application.config.store = some .failure := by
  rw [nativeBobBindingDelay, runInteractionPlan_append] at supported
  obtain ⟨ticked, tickedMem, expiryMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  have ticks := native_ticks_application players _ execution ticked tickedMem
  obtain ⟨entered, activated⟩ := valid.activatedAt_eq_some_of_ready_actor
    bobBinding ready (by rfl)
  have enteredLe := valid.activated_le _ entered activated
  have expireMem : next ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.expire bobBinding) ticked).support := by
    simpa only [runInteractionPlan, FinDist.bind_pure] using expiryMem
  have moved := nativeRuntime.reactive_application_support nativeLeaks players
    (.expire bobBinding) ticked next (by
      simpa only [interactionStep, interactionInstruction, FinDist.pure_bind] using expireMem)
  rw [environmentStep_expire_bind_eq nativeRuntime ticked.application bobBinding
    (by simpa only [ticks.1] using ready) entered
    (by simpa only [ticks.2.1] using activated)
    (by rw [ticks.2.2]; omega) bob .bool rfl rfl rfl] at moved
  have same := FinDist.mem_support_pure.mp moved
  rw [same]
  simp [bobBindingRef, State.complete, EventGraph.Config.store, EventGraph.FieldRef.get?]

theorem native_bob_binding_settlement (players : Player → nativeApp.Policy)
    (execution next : nativeApp.Execution)
    (valid : execution.application.Invariant nativeInputs)
    (available : bobBinding ∈ execution.application.config.cut.completed ∨
      execution.application.config.cut.Ready bobBinding)
    (supported : next ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      nativeBobBindingDelay execution).support) :
    bobBindingRef.get? next.application.config.store =
      some ((bobBindingRef.get? execution.application.config.store).getD .failure) := by
  cases stored : bobBindingRef.get? execution.application.config.store with
  | some value =>
      exact native_bob_binding_plan_preserves players value _ execution next stored supported
  | none =>
      have unfinished : bobBinding ∉ execution.application.config.cut.completed := by
        intro completed
        have output := execution.application.config.output_available bobBinding |>.mpr completed
        have present := bobBindingRef.get?_isSome execution.application.config.store output
        rw [stored] at present
        cases present
      exact native_bob_binding_timeout players execution next valid
        (available.resolve_left unfinished) supported

/-- Complete native execution settles Bob's binding before any later response;
its final value is exactly the reserved inclusion result, defaulting to failure. -/
theorem native_bob_response_settlement_finish (players : Player → nativeApp.Policy)
    (control : nativeApp.Control) (trace : nativeArena.Trace (some control))
    (response : nativeApp.Action) (active : control.actor = some bob)
    (granted : control.execution.application.serviceGrant = some bobBinding)
    (unfinished : bobBinding ∉ control.execution.application.config.cut.completed)
    (chooses : players bob (control.execution.recall bob)
      (control.execution.observe nativeApp bob) = FinDist.pure response)
    (result : nativeApp.ProtocolState)
    (supported : result ∈ (nativeApp.finish (FinDist.pure nativeInitial) nativeHorizon
      nativeScheduler players (some control)).support) :
    ∃ middle ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
        (.includeLatest bobBinding bob)
        (control.execution.respond nativeApp bob response)).support,
      ∃ final, result = some final ∧ bobBindingRef.get? final.execution.application.config.store =
        some ((bobBindingRef.get? middle.application.config.store).getD .failure) := by
  have position := (native_decision_cursor bobBinding control trace bob active granted).2
  obtain ⟨valid, service⟩ := native_decision_service bobBinding control trace active position
  have ready := (service.resolve_left unfinished).1
  have accounted := (native_decision_predecessor bobBinding control trace active position).1
  have remainingEq : control.remaining = (nativeAfterResponse bobBinding).length := by
    have length := congrArg List.length (native_response_split bobBinding)
    simp only [List.length_append, List.length_cons] at length
    change nativeHorizon = _ at length
    omega
  let responded := control.execution.respond nativeApp bob response
  have runAfter : nativeApp.runRounds nativeScheduler players control.remaining responded =
      nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
        (nativeAfterResponse bobBinding) responded := by
    rw [remainingEq]
    have split : nativePlan = (nativeBeforeResponse bobBinding ++ [.player bob]) ++
        nativeAfterResponse bobBinding ++ [] := by
      simpa only [List.append_nil, List.append_assoc, List.singleton_append,
        show nativeOwner bobBinding = bob from rfl] using
        native_response_split bobBinding
    apply native_segment_rounds players (nativeBeforeResponse bobBinding ++ [.player bob])
      (nativeAfterResponse bobBinding) [] split responded
    rw [nativeApp.respond_environmentRecall]
    simpa only [List.length_append, List.length_singleton] using position
  simp only [ReactiveApplication.finish, active, ReactiveApplication.resume,
    ReactiveApplication.invoke, chooses, FinDist.map_pure, FinDist.pure_bind] at supported
  change result ∈ ((nativeApp.runRounds nativeScheduler players control.remaining responded).map
    nativeApp.finished).support at supported
  rw [runAfter] at supported
  obtain ⟨final, finalMem, rfl⟩ := FinDist.support_map .. ▸ supported
  have afterEq : nativeAfterResponse bobBinding =
      .includeLatest bobBinding bob :: (nativeBobBindingDelay ++
        ((List.finRange nativeGraph.order.eventCount).drop (bobBinding.val + 1)).flatMap
          nativeVisit) := by
    simp only [nativeAfterResponse, nativeBobBindingDelay, List.cons_append,
      List.append_assoc, List.nil_append]
    rfl
  rw [afterEq, runInteractionPlan] at finalMem
  obtain ⟨middle, middleMem, restMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ finalMem)
  rw [runInteractionPlan_append] at restMem
  obtain ⟨settled, settledMem, tailMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ restMem)
  have respondedValid := (nativeRuntime.reactiveStateInvariant nativeLeaks nativeInputs).respond
    control.execution bob response valid
  have respondedReady : responded.application.config.cut.Ready bobBinding := by
    change (control.execution.respond nativeApp bob response).application.config.cut.Ready _
    rw [(nativeRuntime.reactive_respond_application nativeLeaks control.execution bob response).1]
    exact ready
  have progress := nativeRuntime.interactionStep_facts nativeLeaks nativeInputs players
    nativeNetwork (.includeLatest bobBinding bob) responded middle respondedValid middleMem
  have settledValue := native_bob_binding_settlement players middle settled progress.invariant
    (progress.ready_or_completed bobBinding respondedReady) settledMem
  exact ⟨middle, middleMem, _, rfl,
    native_bob_binding_plan_preserves players _ _ settled final settledValue tailMem⟩

def nativeBobBindingAt (state : nativeApp.ProtocolState) : Option (PublicationResult Bool) :=
  state.bind (fun control => bobBindingRef.get? control.execution.application.config.store)

theorem native_bob_settlement_behavioral
    (profile : ∀ who, nativeModel.BehavioralPolicy who)
    (control : nativeApp.Control) (trace : nativeArena.Trace (some control))
    (response : nativeApp.Action) (active : control.actor = some bob)
    (granted : control.execution.application.serviceGrant = some bobBinding)
    (unfinished : bobBinding ∉ control.execution.application.config.cut.completed)
    (chooses : nativeMenu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
      profile bob (control.execution.recall bob) (control.execution.observe nativeApp bob) =
        FinDist.pure response)
    (final : nativeArena.History)
    (supported : final ∈ (nativeModel.runBehavioralFrom profile (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).support) :
    ∃ middle ∈ (nativeRuntime.interactionStep nativeLeaks
        (nativeMenu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
          profile) nativeNetwork (.includeLatest bobBinding bob)
        (control.execution.respond nativeApp bob response)).support,
      nativeBobBindingAt final.state =
        some ((bobBindingRef.get? middle.application.config.store).getD .failure) := by
  have law := nativeMenu.run_eq_finish (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
    profile (2 * nativeHorizon + 1) ⟨some control, trace⟩ (by
      change nativeApp.rank nativeHorizon (some control) ≤ 2 * nativeHorizon + 1
      have bound := nativeApp.trace_bound (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
        (nativeMenu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon nativeScheduler trace)
      omega)
  obtain ⟨middle, middleMem, result, stateEq, bound⟩ := native_bob_response_settlement_finish
    _ control trace response active granted unfinished chooses final.state (by
      rw [← law, FinDist.support_map]
      exact ⟨final, supported, rfl⟩)
  exact ⟨middle, middleMem, by
    simpa only [nativeBobBindingAt, stateEq, Option.bind_some] using bound⟩

end VegasTests.SelectiveAssociation
