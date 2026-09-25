/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationGuessSelection
import VegasTests.SelectiveAssociationPublication

/-! # Settlement of every native binding response

An omitted or rejected packet reaches ordinary timeout failure before later
players act. Successful binding results persist throughout the remaining play.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory GameTheory.Protocol

variable {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}

def nativeBindingDelay (who : Player) : List (ServiceInstruction nativeGraph) :=
  List.replicate (nativeRuntime.deadline (nativeBindingEvent who)) .tick ++ [.expire
    (nativeBindingEvent who)]

theorem native_binding_plan_preserves (who : Player) (players : Player → (serviceApp
  observation).Policy)
    (value : PublicationResult Bool) (plan : List (ServiceInstruction nativeGraph))
    (execution next : (serviceApp observation).Execution)
    (stored : (nativeBindingRef who).get? execution.application.config.store = some value)
    (supported : next ∈ (nativeRuntime.runInteractionPlan observation players (serviceNetwork
      observation)
      plan execution).support) :
    (nativeBindingRef who).get? next.application.config.store = some value := by
  induction plan generalizing execution with
  | nil => cases FinDist.mem_support_pure.mp supported; exact stored
  | cons instruction rest ih =>
      obtain ⟨middle, middleMem, restMem⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      obtain ⟨command, _, stepped⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ middleMem)
      exact ih middle ((ReactiveApplication.Invariant.policyInvariant (serviceApp observation)
        (native_binding_invariant who value) players).dispatch
          command execution middle stored stepped) restMem

theorem native_binding_timeout (who : Player) (players : Player → (serviceApp observation).Policy)
    (execution next : (serviceApp observation).Execution)
    (valid : execution.application.Invariant nativeInputs)
    (ready : execution.application.config.cut.Ready (nativeBindingEvent who))
    (supported : next ∈ (nativeRuntime.runInteractionPlan observation players (serviceNetwork
      observation)
      (nativeBindingDelay who) execution).support) :
    (nativeBindingRef who).get? next.application.config.store = some .failure := by
  rw [nativeBindingDelay, runInteractionPlan_append] at supported
  obtain ⟨ticked, tickedMem, expiryMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  have ticks := native_ticks_application players _ execution ticked tickedMem
  obtain ⟨entered, activated⟩ := valid.activatedAt_eq_some_of_ready_actor
    (nativeBindingEvent who) ready (by rw [native_actor, native_binding_owner]; rfl)
  have enteredLe := valid.activated_le _ entered activated
  have expireMem : next ∈ (nativeRuntime.interactionStep observation players (serviceNetwork
    observation)
      (.expire (nativeBindingEvent who)) ticked).support := by
    simpa only [runInteractionPlan, FinDist.bind_pure] using expiryMem
  have moved := nativeRuntime.reactive_application_support observation players
    (.expire (nativeBindingEvent who)) ticked next (by
      simpa only [interactionStep, interactionInstruction, FinDist.pure_bind] using expireMem)
  rw [environmentStep_expire_bind_eq nativeRuntime ticked.application (nativeBindingEvent who)
    (by simpa only [ticks.1] using ready) entered
    (by simpa only [ticks.2.1] using activated)
    (by rw [ticks.2.2]; omega) who .bool (native_binding_output who) (native_binding_code who)
      (native_binding_node who)] at moved
  have same := FinDist.mem_support_pure.mp moved
  rw [same]
  rw [native_binding_ref_eq]
  fin_cases who <;> simp [nativeBindingEvent, State.complete, EventGraph.Config.store,
    EventGraph.FieldRef.get?]

theorem native_binding_settlement (who : Player) (players : Player → (serviceApp
  observation).Policy)
    (execution next : (serviceApp observation).Execution)
    (valid : execution.application.Invariant nativeInputs)
    (available : (nativeBindingEvent who) ∈ execution.application.config.cut.completed ∨
      execution.application.config.cut.Ready (nativeBindingEvent who))
    (supported : next ∈ (nativeRuntime.runInteractionPlan observation players (serviceNetwork
      observation)
      (nativeBindingDelay who) execution).support) :
    (nativeBindingRef who).get? next.application.config.store =
      some (((nativeBindingRef who).get? execution.application.config.store).getD .failure) := by
  cases stored : (nativeBindingRef who).get? execution.application.config.store with
  | some value =>
      exact native_binding_plan_preserves who players value _ execution next stored supported
  | none =>
      have unfinished : (nativeBindingEvent who) ∉ execution.application.config.cut.completed := by
        intro completed
        have output := execution.application.config.output_available (nativeBindingEvent who)
          |>.mpr completed
        have present := (nativeBindingRef who).get?_isSome execution.application.config.store
          (by rw [native_binding_ref_eq]; exact output)
        rw [stored] at present
        cases present
      exact native_binding_timeout who players execution next valid
        (available.resolve_left unfinished) supported

/-- Complete native execution settles the owner's binding before any later response;
its final value is exactly the reserved inclusion result, defaulting to failure. -/
theorem native_binding_response_settlement_finish (who : Player) (players : Player → (serviceApp
  observation).Policy)
    (control : (serviceApp observation).Control) (trace : (serviceArena observation).Trace (some
      control))
    (response : (serviceApp observation).Action) (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativeBindingEvent who))
    (unfinished : (nativeBindingEvent who) ∉ control.execution.application.config.cut.completed)
    (chooses : players who (control.execution.recall who)
      (control.execution.observe (serviceApp observation) who) = FinDist.pure response)
    (result : (serviceApp observation).ProtocolState)
    (supported : result ∈ ((serviceApp observation).finish (FinDist.pure nativeInitial)
      nativeHorizon
      (serviceScheduler observation) players (some control)).support) :
    ∃ middle ∈ (nativeRuntime.interactionStep observation players (serviceNetwork observation)
        (.includeLatest (nativeBindingEvent who) who)
        (control.execution.respond (serviceApp observation) who response)).support,
      ∃ final, result = some final ∧ (nativeBindingRef who).get?
        final.execution.application.config.store =
        some (((nativeBindingRef who).get? middle.application.config.store).getD .failure) := by
  have position := (native_decision_cursor (nativeBindingEvent who) control trace who active
    granted).2
  obtain ⟨valid, service⟩ := native_decision_service (nativeBindingEvent who) control trace
      (by rwa [native_binding_owner]) position
  have ready := (service.resolve_left unfinished).1
  have accounted := (native_decision_predecessor (nativeBindingEvent who) control trace
    (by rwa [native_binding_owner]) position).1
  have remainingEq : control.remaining = (nativeAfterResponse (nativeBindingEvent who)).length := by
    have length := congrArg List.length (native_response_split (nativeBindingEvent who))
    simp only [List.length_append, List.length_cons] at length
    change nativeHorizon = _ at length
    omega
  let responded := control.execution.respond (serviceApp observation) who response
  have runAfter : (serviceApp observation).runRounds (serviceScheduler observation) players
    control.remaining responded =
      nativeRuntime.runInteractionPlan observation players (serviceNetwork observation)
        (nativeAfterResponse (nativeBindingEvent who)) responded := by
    rw [remainingEq]
    have split : nativePlan = (nativeBeforeResponse (nativeBindingEvent who) ++ [.player who]) ++
        nativeAfterResponse (nativeBindingEvent who) ++ [] := by
      simpa only [List.append_nil, List.append_assoc, List.singleton_append,
        native_binding_owner] using
        native_response_split (nativeBindingEvent who)
    apply native_segment_rounds players (nativeBeforeResponse (nativeBindingEvent who) ++
      [.player who])
      (nativeAfterResponse (nativeBindingEvent who)) [] split responded
    rw [(serviceApp observation).respond_environmentRecall]
    simpa only [List.length_append, List.length_singleton] using position
  simp only [ReactiveApplication.finish, active, ReactiveApplication.resume,
    ReactiveApplication.invoke, chooses, FinDist.map_pure, FinDist.pure_bind] at supported
  change result ∈ (((serviceApp observation).runRounds (serviceScheduler observation) players
    control.remaining responded).map
    (serviceApp observation).finished).support at supported
  rw [runAfter] at supported
  obtain ⟨final, finalMem, rfl⟩ := FinDist.support_map .. ▸ supported
  have afterEq : nativeAfterResponse (nativeBindingEvent who) =
      .includeLatest (nativeBindingEvent who) who :: ((nativeBindingDelay who) ++
        ((List.finRange nativeGraph.order.eventCount).drop ((nativeBindingEvent who).val +
          1)).flatMap
          nativeVisit) := by
    simp only [nativeAfterResponse, nativeBindingDelay, List.cons_append,
      List.append_assoc, List.nil_append, native_binding_owner]
  rw [afterEq, runInteractionPlan] at finalMem
  obtain ⟨middle, middleMem, restMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ finalMem)
  rw [runInteractionPlan_append] at restMem
  obtain ⟨settled, settledMem, tailMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ restMem)
  have respondedValid := (nativeRuntime.reactiveStateInvariant observation nativeInputs).respond
    control.execution who response valid
  have respondedReady : responded.application.config.cut.Ready (nativeBindingEvent who) := by
    change (control.execution.respond (serviceApp observation) who
      response).application.config.cut.Ready _
    rw [(nativeRuntime.reactive_respond_application observation control.execution who response).1]
    exact ready
  have progress := nativeRuntime.interactionStep_facts observation nativeInputs players
    (serviceNetwork observation) (.includeLatest (nativeBindingEvent who) who) responded middle
      respondedValid middleMem
  have settledValue := native_binding_settlement who players middle settled progress.invariant
    (progress.ready_or_completed (nativeBindingEvent who) respondedReady) settledMem
  exact ⟨middle, middleMem, _, rfl,
    native_binding_plan_preserves who players _ _ settled final settledValue tailMem⟩

def nativeBindingAt (who : Player) (state : (serviceApp observation).ProtocolState) : Option
  (PublicationResult Bool) :=
  state.bind (fun control => (nativeBindingRef who).get? control.execution.application.config.store)

theorem native_binding_settlement_behavioral (who : Player)
    (profile : ∀ who, (serviceModel observation).BehavioralPolicy who)
    (control : (serviceApp observation).Control) (trace : (serviceArena observation).Trace (some
      control))
    (response : (serviceApp observation).Action) (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativeBindingEvent who))
    (unfinished : (nativeBindingEvent who) ∉ control.execution.application.config.cut.completed)
    (chooses : (serviceMenu observation).decodeProfile (FinDist.pure nativeInitial) nativeHorizon
      (serviceScheduler observation)
      profile who (control.execution.recall who) (control.execution.observe (serviceApp
        observation) who) =
        FinDist.pure response)
    (final : (serviceArena observation).History)
    (supported : final ∈ ((serviceModel observation).runBehavioralFrom profile (2 * nativeHorizon
      + 1)
      ⟨some control, trace⟩).support) :
    ∃ middle ∈ (nativeRuntime.interactionStep observation
        ((serviceMenu observation).decodeProfile (FinDist.pure nativeInitial) nativeHorizon
          (serviceScheduler observation)
          profile) (serviceNetwork observation) (.includeLatest (nativeBindingEvent who) who)
        (control.execution.respond (serviceApp observation) who response)).support,
      (nativeBindingAt who) final.state =
        some (((nativeBindingRef who).get? middle.application.config.store).getD .failure) := by
  have law := (serviceMenu observation).run_eq_finish (FinDist.pure nativeInitial) nativeHorizon
    (serviceScheduler observation)
    profile (2 * nativeHorizon + 1) ⟨some control, trace⟩ (by
      change (serviceApp observation).rank nativeHorizon (some control) ≤ 2 * nativeHorizon + 1
      have bound := (serviceApp observation).trace_bound (FinDist.pure nativeInitial)
        nativeHorizon (serviceScheduler observation)
        ((serviceMenu observation).toRawTrace (FinDist.pure nativeInitial) nativeHorizon
          (serviceScheduler observation) trace)
      omega)
  obtain ⟨middle, middleMem, result, stateEq, bound⟩ :=
    native_binding_response_settlement_finish who
    _ control trace response active granted unfinished chooses final.state (by
      rw [← law, FinDist.support_map]
      exact ⟨final, supported, rfl⟩)
  exact ⟨middle, middleMem, by
    simpa only [nativeBindingAt, stateEq, Option.bind_some] using bound⟩

end VegasTests.SelectiveAssociation
