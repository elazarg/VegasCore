/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationOpeningContinuation

/-! # Settlement after an arbitrary publication response

The reserved inclusion may accept an opening, accept withholding, or leave
the event unfinished. The following clock-only segment then expires the
unfinished event. This proves the result of rejection without treating
rejection itself as an application completion.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def nativePublicationDelay (who : Player) : List (ServiceInstruction nativeGraph) :=
  List.replicate (nativeRuntime.deadline (nativePublicationEvent who)) .tick ++
    [.expire (nativePublicationEvent who)]

theorem native_publication_plan_preserves (players : Player → nativeApp.Policy)
    (who : Player) (publication : PublicationResult Bool)
    (plan : List (ServiceInstruction nativeGraph)) (execution next : nativeApp.Execution)
    (stored : (nativePublicationRef who).get? execution.application.config.store = some publication)
    (supported : next ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      plan execution).support) :
    (nativePublicationRef who).get? next.application.config.store = some publication := by
  induction plan generalizing execution with
  | nil => cases FinDist.mem_support_pure.mp supported; exact stored
  | cons instruction rest ih =>
      obtain ⟨middle, middleMem, restMem⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      obtain ⟨command, _, stepped⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ middleMem)
      exact ih middle ((ReactiveApplication.Invariant.policyInvariant nativeApp
        (native_publication_invariant who publication) players).dispatch
          command execution middle stored stepped) restMem

theorem native_ticks_application (players : Player → nativeApp.Policy)
    (count : Nat) (execution next : nativeApp.Execution)
    (supported : next ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      (List.replicate count .tick) execution).support) :
    next.application.config = execution.application.config ∧
      next.application.activatedAt = execution.application.activatedAt ∧
      next.application.clock = execution.application.clock + count := by
  induction count generalizing execution with
  | zero => cases FinDist.mem_support_pure.mp supported; exact ⟨rfl, rfl, rfl⟩
  | succ count ih =>
      rw [List.replicate_succ, runInteractionPlan] at supported
      obtain ⟨middle, middleMem, tailMem⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      have moved := nativeRuntime.reactive_application_support nativeLeaks players .advanceClock
        execution middle (by
          simpa only [interactionStep, interactionInstruction, FinDist.pure_bind] using middleMem)
      have applicationEq : middle.application =
          { execution.application with clock := execution.application.clock + 1 } :=
        FinDist.mem_support_pure.mp moved
      obtain ⟨configEq, activatedEq, clockEq⟩ := ih middle tailMem
      refine ⟨?_, ?_, ?_⟩
      · rw [configEq, applicationEq]
      · rw [activatedEq, applicationEq]
      · rw [clockEq, applicationEq]
        simp only
        omega

theorem native_publication_expire (players : Player → nativeApp.Policy)
    (execution next : nativeApp.Execution) (who : Player)
    (ready : execution.application.config.cut.Ready (nativePublicationEvent who))
    (entered : Nat)
    (activated : execution.application.activatedAt (nativePublicationEvent who) = some entered)
    (due : nativeRuntime.deadline (nativePublicationEvent who) ≤
      execution.application.clock - entered)
    (supported : next ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.expire (nativePublicationEvent who)) execution).support) :
    (nativePublicationRef who).get? next.application.config.store = some .failure := by
  obtain ⟨checks, codeEq, node, _⟩ := native_publication_rule who
  have moved := nativeRuntime.reactive_application_support nativeLeaks players
    (.expire (nativePublicationEvent who)) execution next (by
      simpa only [interactionStep, interactionInstruction, FinDist.pure_bind] using supported)
  rw [environmentStep_expire_resolve_eq nativeRuntime execution.application
    (nativePublicationEvent who) ready entered activated due who .bool (nativeBindingRef who)
    checks (native_publication_output who) codeEq node] at moved
  have stateEq := FinDist.mem_support_pure.mp moved
  rw [stateEq]
  fin_cases who <;> simp [nativePublicationRef, nativePublicationEvent, State.complete,
    EventGraph.Config.store, EventGraph.FieldRef.get?]

theorem native_publication_timeout (players : Player → nativeApp.Policy)
    (execution next : nativeApp.Execution) (who : Player)
    (valid : execution.application.Invariant nativeInputs)
    (ready : execution.application.config.cut.Ready (nativePublicationEvent who))
    (supported : next ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      (nativePublicationDelay who) execution).support) :
    (nativePublicationRef who).get? next.application.config.store = some .failure := by
  rw [nativePublicationDelay, runInteractionPlan_append] at supported
  obtain ⟨ticked, tickedMem, expiryMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  have ticks := native_ticks_application players _ execution ticked tickedMem
  obtain ⟨entered, activated⟩ := valid.activatedAt_eq_some_of_ready_actor
    (nativePublicationEvent who) ready (by rw [native_actor]; rfl)
  have enteredLe := valid.activated_le _ entered activated
  have expireMem : next ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.expire (nativePublicationEvent who)) ticked).support := by
    simpa only [runInteractionPlan, FinDist.bind_pure] using expiryMem
  apply native_publication_expire players ticked next who
    (by simpa only [ticks.1] using ready) entered
    (by simpa only [ticks.2.1] using activated) _ expireMem
  rw [ticks.2.2]
  omega

/-- Once inclusion has finished, the ownerless delay preserves an existing
publication and turns an unfinished ready publication into failure. -/
theorem native_publication_settlement (players : Player → nativeApp.Policy)
    (execution next : nativeApp.Execution) (who : Player)
    (valid : execution.application.Invariant nativeInputs)
    (available : nativePublicationEvent who ∈ execution.application.config.cut.completed ∨
      execution.application.config.cut.Ready (nativePublicationEvent who))
    (supported : next ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      (nativePublicationDelay who) execution).support) :
    (nativePublicationRef who).get? next.application.config.store =
      some (((nativePublicationRef who).get?
        execution.application.config.store).getD .failure) := by
  cases stored : (nativePublicationRef who).get? execution.application.config.store with
  | some publication =>
      exact native_publication_plan_preserves players who publication _ execution next stored
        supported
  | none =>
      have unfinished : nativePublicationEvent who ∉
          execution.application.config.cut.completed := by
        intro completed
        have present := execution.application.config.output_available (nativePublicationEvent who)
        have output : (execution.application.config.outputs (nativePublicationEvent who)).isSome :=
          present.mpr completed
        have field :
            (execution.application.config.store (.inr (nativePublicationEvent who))).isSome :=
          output
        have refPresent := (nativePublicationRef who).get?_isSome
          execution.application.config.store field
        rw [stored] at refPresent
        cases refPresent
      exact native_publication_timeout players execution next who valid
        (available.resolve_left unfinished) supported

/-- Every final publication is determined by the immediate reserved-inclusion
result, with absence mapped to ordinary timeout failure. Later player choices
cannot change it. -/
theorem native_response_settlement_finish (players : Player → nativeApp.Policy)
    (control : nativeApp.Control) (trace : nativeArena.Trace (some control))
    (who : Player) (response : nativeApp.Action) (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who))
    (unfinished : nativePublicationEvent who ∉ control.execution.application.config.cut.completed)
    (chooses : players who (control.execution.recall who)
      (control.execution.observe nativeApp who) = FinDist.pure response)
    (result : nativeApp.ProtocolState)
    (supported : result ∈ (nativeApp.finish (FinDist.pure nativeInitial) nativeHorizon
      nativeScheduler players (some control)).support) :
    ∃ middle ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
        (.includeLatest (nativePublicationEvent who) who)
        (control.execution.respond nativeApp who response)).support,
      ∃ final, result = some final ∧
        (nativePublicationRef who).get? final.execution.application.config.store =
          some (((nativePublicationRef who).get?
            middle.application.config.store).getD .failure) := by
  have position := (native_decision_cursor (nativePublicationEvent who) control trace who active
    granted).2
  have ownerActive : control.actor = some (nativeOwner (nativePublicationEvent who)) := by
    rwa [native_publication_owner]
  obtain ⟨valid, service⟩ := native_decision_service (nativePublicationEvent who) control trace
    ownerActive position
  have ready := (service.resolve_left unfinished).1
  have accounted := (native_decision_predecessor (nativePublicationEvent who) control trace
    ownerActive position).1
  have remainingEq : control.remaining =
      (nativeAfterResponse (nativePublicationEvent who)).length := by
    have length := congrArg List.length (native_response_split (nativePublicationEvent who))
    simp only [List.length_append, List.length_cons] at length
    change nativeHorizon = _ at length
    omega
  let responded := control.execution.respond nativeApp who response
  have runAfter : nativeApp.runRounds nativeScheduler players control.remaining responded =
      nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
        (nativeAfterResponse (nativePublicationEvent who)) responded := by
    rw [remainingEq]
    have split : nativePlan =
        (nativeBeforeResponse (nativePublicationEvent who) ++ [.player who]) ++
          nativeAfterResponse (nativePublicationEvent who) ++ [] := by
      simpa only [List.append_nil, List.append_assoc, List.singleton_append,
        native_publication_owner] using native_response_split (nativePublicationEvent who)
    apply native_segment_rounds players
      (nativeBeforeResponse (nativePublicationEvent who) ++ [.player who])
      (nativeAfterResponse (nativePublicationEvent who)) [] split responded
    rw [nativeApp.respond_environmentRecall]
    simpa only [List.length_append, List.length_singleton] using position
  simp only [ReactiveApplication.finish, active, ReactiveApplication.resume,
    ReactiveApplication.invoke, chooses, FinDist.map_pure, FinDist.pure_bind] at supported
  change result ∈ ((nativeApp.runRounds nativeScheduler players control.remaining responded).map
    nativeApp.finished).support at supported
  rw [runAfter] at supported
  obtain ⟨final, finalMem, rfl⟩ := FinDist.support_map .. ▸ supported
  have afterEq : nativeAfterResponse (nativePublicationEvent who) =
      .includeLatest (nativePublicationEvent who) who ::
        (nativePublicationDelay who ++
          ((List.finRange nativeGraph.order.eventCount).drop
            ((nativePublicationEvent who).val + 1)).flatMap nativeVisit) := by
    simp only [nativeAfterResponse, nativePublicationDelay, native_publication_owner,
      List.cons_append, List.append_assoc, List.nil_append]
  rw [afterEq, runInteractionPlan] at finalMem
  obtain ⟨middle, middleMem, restMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ finalMem)
  rw [runInteractionPlan_append] at restMem
  obtain ⟨settled, settledMem, tailMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ restMem)
  have respondedValid := (nativeRuntime.reactiveStateInvariant nativeLeaks nativeInputs).respond
    control.execution who response valid
  have respondedReady : responded.application.config.cut.Ready (nativePublicationEvent who) := by
    change (control.execution.respond nativeApp who response).application.config.cut.Ready _
    rw [(nativeRuntime.reactive_respond_application nativeLeaks control.execution who response).1]
    exact ready
  have progress := nativeRuntime.interactionStep_facts nativeLeaks nativeInputs players
    nativeNetwork (.includeLatest (nativePublicationEvent who) who) responded middle
    respondedValid middleMem
  have settledValue := native_publication_settlement players middle settled who progress.invariant
    (progress.ready_or_completed (nativePublicationEvent who) respondedReady) settledMem
  exact ⟨middle, middleMem, _, rfl,
    native_publication_plan_preserves players who _ _ settled final settledValue tailMem⟩

end VegasTests.SelectiveAssociation
