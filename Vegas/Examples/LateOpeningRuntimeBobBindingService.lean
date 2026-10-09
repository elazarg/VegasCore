/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobSuffix
import Vegas.Pending.ReactiveBindingResources

/-! # The first canonical Bob binding at an arbitrary native history

Alice's prior raw traffic is unrestricted. If all earlier Bob responses were
silent, his first prepared handle is fresh and his authenticated serial is
zero. A ready and timely answer binding then receives the actual immediate
author receipt. These facts are operational adapters for whole continuations;
readiness and timing still need to be established at the relevant callback.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobBindingService

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobAudit
  LateOpeningRuntimeReadout

def SilentRecall (execution : app.Execution) : Prop :=
  ∀ entry ∈ execution.recall bob, entry.action = ⟨none⟩

private theorem initial_law_eq :
    (setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph)) = initial := by
  rw [PMF.map_comp]
  rfl

theorem silent_resources (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (quiet : SilentRecall control.execution) :
    control.execution.network.nextSerial bob = 0 ∧
      ∀ serial, control.execution.application.candidates.lookup (bob, .prepared serial) =
        .fresh := by
  have allocated := app.serialRecall_history (LateOpeningRuntimeService.scheduler
    weight nonnegative) initial LateOpeningRuntimeService.horizon trace
  have empty : app.submissionCount (control.execution.recall bob) = 0 := by
    unfold ReactiveApplication.submissionCount
    apply List.countP_eq_zero.mpr
    intro entry member
    rw [quiet entry member]
    decide
  have zero : control.execution.network.nextSerial bob = 0 := (allocated bob).trans empty
  have original : (app.protocol ((setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph)))
      LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ).Trace (some control) := by
    rwa [initial_law_eq]
  have recalled := LateOpeningRuntimeService.runtime.candidateRecall_history leaks
    (setup.initialLaw.map setup.eventInputs) LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) original
  refine ⟨zero, ?_⟩
  intro serial
  apply recalled bob serial
  intro present
  obtain ⟨response, issued, selected⟩ := List.mem_filterMap.mp present
  obtain ⟨entry, member, rfl⟩ := List.mem_map.mp issued
  rw [quiet entry member] at selected
  cases selected

theorem binding_count_zero (physical : EventGraphRuntime.State nativeGraph)
    (unfinished : bobBindEvent ∉ physical.config.cut.completed) :
    physical.publicView.bindingCount bob = 0 := by
  unfold PublicView.bindingCount
  apply List.countP_eq_zero.mpr
  intro event member
  change Fin 3 at event
  fin_cases event
  · decide
  · exact (unfinished ((physical.config.history_exact bobBindEvent).mp member)).elim
  · decide

/-- Canonical first binding uses the actual fresh first prepared handle at
every ready history with silent own recall, regardless of Alice's packets. -/
theorem canonical_binding (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (quiet : SilentRecall control.execution)
    (ready : control.execution.application.config.cut.Ready bobBindEvent) (answer : Answer) :
    LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
      (control.execution.recall bob) (control.execution.observe app bob) bobBindEvent
        (.success answer) = LateOpeningRuntimeBobSuffix.binding answer := by
  have count := binding_count_zero control.execution.application ready.1
  apply LateOpeningRuntimeService.runtime.canonicalServiceDecision_binding leaks bob
    (control.execution.recall bob) (control.execution.observe app bob) bobBindEvent
      (.range 0 5) rfl rfl rfl 0 _ (.success answer)
  rw [← count]
  apply canonicalFreshSlot_canonical
  change control.execution.application.candidates.lookup
    (bob, .prepared (control.execution.application.publicView.bindingCount bob)) = .fresh
  rw [count]
  exact (silent_resources weight nonnegative control trace quiet).2 0

/-- The comparison binding is a genuine action in the existing bounded raw
menu, including at every hidden history with the same own information. -/
theorem canonical_binding_available (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (quiet : SilentRecall control.execution)
    (ready : control.execution.application.config.cut.Ready bobBindEvent) (answer : Answer) :
    LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
      (control.execution.recall bob) (control.execution.observe app bob) bobBindEvent
        (.success answer) ∈ rawMenu.actions bob (control.execution.recall bob)
          (control.execution.observe app bob) := by
  rw [canonical_binding weight nonnegative control trace quiet ready answer]
  exact LateOpeningRuntimeBobSuffix.binding_in_raw_menu answer bob _ _

theorem binding_packet (execution : app.Execution)
    (ready : execution.application.config.cut.Ready bobBindEvent) (answer : Answer) :
    app.packet (app.submit execution.application bob
      (LateOpeningRuntimeBobSuffix.bindingMaterial answer)) bob
        (execution.network.known bob) (LateOpeningRuntimeBobSuffix.bindingMaterial answer) =
      LateOpeningRuntimeBobSuffix.bindingMessage.payload := by
  dsimp only [LateOpeningRuntimeBobSuffix.bindingMaterial]
  rw [LateOpeningRuntimeService.runtime.reactiveApplication_packet_none]
  change WitnessedPacket.mk _ _ (execution.application.publicView.tokenFor
    (.commitment bobBindEvent (bob, .prepared 0))) = _
  rw [execution.application.publicView_tokenFor_of_ready
    (.commitment bobBindEvent (bob, .prepared 0)) bobBindEvent rfl ready]
  rfl

theorem reveal_ready_after_binding (physical : EventGraphRuntime.State nativeGraph)
    (ready : physical.config.cut.Ready bobBindEvent) :
    (physical.config.cut.complete bobBindEvent ready).Ready bobRevealEvent := by
  have before : bobRevealEvent ∉ physical.config.cut.completed := by
    intro completed
    apply ready.1
    exact physical.config.cut.predecessor_closed completed
      (by decide : bobBindEvent ∈ nativeGraph.order.predecessors bobRevealEvent)
  refine ⟨?_, ?_⟩
  · change bobRevealEvent ∉ insert bobBindEvent physical.config.cut.completed
    simpa only [Finset.mem_insert, show bobRevealEvent ≠ bobBindEvent by decide, false_or]
      using before
  · intro predecessor earlier
    change predecessor ∈ insert bobBindEvent physical.config.cut.completed
    change Fin 3 at predecessor
    fin_cases predecessor
    · exact Finset.mem_insert_of_mem (ready.2
        (by decide : aliceEvent ∈ nativeGraph.order.predecessors bobBindEvent))
    · exact Finset.mem_insert_self _ _
    · exact ((by decide : bobRevealEvent ∉ nativeGraph.order.predecessors bobRevealEvent)
        earlier).elim

/-- Every ready and timely first canonical binding is accepted by the actual
native handler and fixes exactly the selected typed answer. -/
theorem binding_acceptance (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (quiet : SilentRecall control.execution)
    (ready : control.execution.application.config.cut.Ready bobBindEvent)
    (timely : control.execution.application.WithinDeadline
      LateOpeningRuntimeService.runtime bobBindEvent) (answer : Answer) :
    ∃ state, app.handle (control.execution.respond app bob
        (LateOpeningRuntimeBobSuffix.binding answer)).application
          LateOpeningRuntimeBobSuffix.bindingMessage = some state ∧
      state.config.store (.inr bobBindEvent) = some (.success answer) ∧
      state.accepted (.inr bobBindEvent) = some (bob, .prepared 0) ∧
      state.config.cut.Ready bobRevealEvent ∧
      state.activatedAt bobRevealEvent = some control.execution.application.clock := by
  have original : (app.protocol ((setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph)))
      LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ).Trace (some control) := by
    rwa [initial_law_eq]
  have valid := LateOpeningRuntimeService.runtime.reactiveBindingInvariant_history leaks
    (setup.initialLaw.map setup.eventInputs) LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) original
  have fresh := (silent_resources weight nonnegative control trace quiet).2 0
  obtain ⟨bit, label, initialized⟩ := history_initial_invariant
    LateOpeningRuntimeService.runtime leaks LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) control trace
  have unactivated : control.execution.application.activatedAt bobRevealEvent = none := by
    cases timer : control.execution.application.activatedAt bobRevealEvent with
    | none => rfl
    | some entered =>
        have revealReady := ((initialized.activated_iff bobRevealEvent).mp
          (by rw [timer]; rfl)).1
        exact (ready.1 (revealReady.2
          (by decide : bobBindEvent ∈ nativeGraph.order.predecessors bobRevealEvent))).elim
  have vacant : control.execution.application.accepted (.inr bobBindEvent) = none := by
    cases associated : control.execution.application.accepted (.inr bobBindEvent) with
    | none => rfl
    | some candidate =>
        exact (ready.1 (valid.toAssociationInvariant.accepted_complete bobBindEvent candidate
          associated)).elim
  have unused : control.execution.application.HandleUnused (bob, .prepared 0) :=
    fun field associated => valid.accepted_fixed field _ associated fresh
  let submitted := control.execution.respond app bob (LateOpeningRuntimeBobSuffix.binding answer)
  have unchanged := LateOpeningRuntimeService.runtime.reactive_respond_application leaks
    control.execution bob (LateOpeningRuntimeBobSuffix.binding answer)
  have sameConfig : submitted.application.config = control.execution.application.config :=
    unchanged.1
  have samePublic : submitted.application.publicView = control.execution.application.publicView :=
    unchanged.2
  have sameClock : submitted.application.clock = control.execution.application.clock :=
    congrArg PublicView.clock samePublic
  have sameTimers : submitted.application.activatedAt = control.execution.application.activatedAt :=
    congrArg PublicView.activatedAt samePublic
  have sameAccepted : submitted.application.accepted = control.execution.application.accepted :=
    congrArg PublicView.accepted samePublic
  have readySubmitted : submitted.application.config.cut.Ready bobBindEvent := by
    rw [sameConfig]
    exact ready
  have timelySubmitted : submitted.application.WithinDeadline
      LateOpeningRuntimeService.runtime bobBindEvent := by
    unfold EventGraphRuntime.State.WithinDeadline
    rw [sameTimers, sameClock]
    exact timely
  have value := LateOpeningRuntimeService.runtime.reactiveBinding_result leaks bob bobBindEvent
    (.range 0 5) (.success answer) 0 control.execution fresh
  let state : EventGraphRuntime.State nativeGraph :=
    { submitted.application.complete bobBindEvent readySubmitted
        (.success answer) (.success answer) with
      accepted := Function.update submitted.application.accepted (.inr bobBindEvent)
        (some (bob, .prepared 0))
      candidates := submitted.application.candidates.freeze (bob, .prepared 0) }
  have handled : app.handle submitted.application LateOpeningRuntimeBobSuffix.bindingMessage =
      some state := by
    rw [LateOpeningRuntimeService.runtime.reactiveApplication_handle_of_tokenValid leaks
      _ _ (by rfl)]
    change handle LateOpeningRuntimeService.runtime submitted.application
      ⟨(bob, 0), .commitment bobBindEvent (bob, .prepared 0)⟩ = some state
    rw [LateOpeningRuntimeService.runtime.handle_commitment_eq submitted.application (bob, 0)
      bobBindEvent (bob, .prepared 0) bob (.range 0 5) rfl rfl rfl readySubmitted timelySubmitted
        rfl rfl ((congrFun sameAccepted (.inr bobBindEvent)).trans vacant) (by
          intro field associated
          apply unused field
          rwa [sameAccepted] at associated)]
    change some ({ submitted.application.complete bobBindEvent readySubmitted
      (submitted.application.bindingResult (bob, .prepared 0) (.range 0 5))
      (submitted.application.bindingResult (bob, .prepared 0) (.range 0 5)) with
        accepted := Function.update submitted.application.accepted (.inr bobBindEvent)
          (some (bob, .prepared 0))
        candidates := submitted.application.candidates.freeze (bob, .prepared 0) }) = some state
    rw [show submitted.application.bindingResult (bob, .prepared 0) (.range 0 5) =
      .success answer from value]
  have revealReady : state.config.cut.Ready bobRevealEvent :=
    reveal_ready_after_binding submitted.application readySubmitted
  refine ⟨state, handled, ?_, ?_, revealReady, ?_⟩
  · change (submitted.application.config.complete bobBindEvent readySubmitted
      (.success answer) (.success answer)).outputs bobBindEvent = some (.success answer)
    exact Config.complete_output_same _ _ _ _ _
  · change Function.update submitted.application.accepted (.inr bobBindEvent)
      (some (bob, .prepared 0)) (.inr bobBindEvent) = _
    simp only [Function.update_self]
  · change State.refreshActivated state.config submitted.application.clock
      submitted.application.activatedAt bobRevealEvent = _
    unfold State.refreshActivated
    rw [dite_eq_left revealReady]
    change (submitted.application.activatedAt bobRevealEvent).orElse
      (fun _ => some submitted.application.clock) = _
    rw [sameTimers, unactivated, sameClock]
    rfl

/-- At any actual Bob callback, the first canonical binding receives its
accepting receipt in the next physical round and starts the disclosure timer
at that callback's clock. Earlier Alice traffic and future policies are free. -/
theorem binding_round (weight : ℝ) (nonnegative : 0 ≤ weight) (remaining : Nat)
    (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining, some bob, execution⟩))
    (quiet : SilentRecall execution)
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (timely : execution.application.WithinDeadline
      LateOpeningRuntimeService.runtime bobBindEvent) (answer : Answer) :
    ∃ next, (∀ players : Player → app.Policy,
      app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
        (execution.respond app bob (LateOpeningRuntimeBobSuffix.binding answer)) = PMF.pure next) ∧
      next.application.config.store (.inr bobBindEvent) = some (.success answer) ∧
      ((bob, 0), true) ∈ next.receipts ∧
      next.application.config.cut.Ready bobRevealEvent ∧
      next.application.activatedAt bobRevealEvent = some execution.application.clock ∧
      CleanBindings next ∧
      next.network.inputs = execution.network.inputs ++
        [LateOpeningRuntimeBobSuffix.bindingMessage] := by
  have resources := silent_resources weight nonnegative ⟨remaining, some bob, execution⟩ trace quiet
  have serials := app.serialsBeforeNext_history (LateOpeningRuntimeService.scheduler
    weight nonnegative) initial LateOpeningRuntimeService.horizon trace
  obtain ⟨physical, accepted, stored, associated, revealReady, revealTimer⟩ :=
    binding_acceptance weight nonnegative ⟨remaining, some bob, execution⟩ trace quiet
      ready timely answer
  let submitted := execution.respond app bob (LateOpeningRuntimeBobSuffix.binding answer)
  let included := submitted.includePending app (bob, 0)
  let next : app.Execution := { included with environmentRecall :=
    submitted.environmentRecall ++ [⟨submitted.observeEnvironment app, .include (bob, 0)⟩] }
  have selected := latestAuthor_after_submit execution bob
    (LateOpeningRuntimeBobSuffix.bindingMaterial answer) serials
  have chosen : LateOpeningRuntimeService.scheduler weight nonnegative submitted.environmentRecall
      (submitted.observeEnvironment app) = PMF.pure (.include (bob, 0)) := by
    have served := protected_response_scheduler weight nonnegative
      ⟨remaining, some bob, execution⟩ trace bob rfl
        (LateOpeningRuntimeBobSuffix.binding answer) (Or.inl rfl)
    apply served.trans
    apply congrArg PMF.pure
    exact selected.trans (congrArg ReactiveApplication.Command.include
      (congrArg (fun serial => (bob, serial)) resources.1))
  have emitted := binding_packet execution ready answer
  have found : submitted.network.lookup (bob, 0) =
      some LateOpeningRuntimeBobSuffix.bindingMessage := by
    change (execution.network.submit bob
      (app.packet (app.submit execution.application bob
        (LateOpeningRuntimeBobSuffix.bindingMaterial answer)) bob
          (execution.network.known bob)
          (LateOpeningRuntimeBobSuffix.bindingMaterial answer))).2.lookup (bob, 0) = _
    rw [← resources.1, serials.lookup_submit, emitted]
    rw [resources.1]
    rfl
  have nextPhysical : next.application = physical := by
    change (submitted.includePending app (bob, 0)).application = physical
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [found]
    change (app.handle submitted.application LateOpeningRuntimeBobSuffix.bindingMessage).getD _ = _
    rw [accepted]
    rfl
  have receipt : ((bob, 0), true) ∈ next.receipts := by
    change ((bob, 0), true) ∈ (submitted.includePending app (bob, 0)).receipts
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [found]
    change ((bob, 0), true) ∈ submitted.receipts ++
      [((bob, 0),
        (app.handle submitted.application LateOpeningRuntimeBobSuffix.bindingMessage).isSome)]
    rw [accepted]
    simp
  have inputs : next.network.inputs = execution.network.inputs ++
      [LateOpeningRuntimeBobSuffix.bindingMessage] := by
    change (submitted.includePending app (bob, 0)).network.inputs = _
    rw [app.includePending_network]
    unfold MessageNetwork.includePending
    rw [found]
    change execution.network.inputs ++ [⟨(bob, execution.network.nextSerial bob),
      app.packet (app.submit execution.application bob
        (LateOpeningRuntimeBobSuffix.bindingMaterial answer)) bob
          (execution.network.known bob) (LateOpeningRuntimeBobSuffix.bindingMaterial answer)⟩] = _
    rw [resources.1, emitted]
    rfl
  refine ⟨next, ?_, nextPhysical ▸ stored, receipt, nextPhysical ▸ revealReady,
    nextPhysical ▸ revealTimer, ?_, inputs⟩
  · intro players
    rw [ReactiveApplication.round, chosen, PMF.pure_bind, ReactiveApplication.dispatch]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
    rfl
  · intro message present owner
    rw [inputs, List.mem_append, List.mem_singleton] at present
    rcases present with old | rfl
    · have earlier := serials.inputs message old
      change message.id.2 < execution.network.nextSerial message.id.1 at earlier
      change message.id.1 = bob at owner
      rw [owner, resources.1] at earlier
      exact (Nat.not_lt_zero _ earlier).elim
    · exact ⟨some ⟨bobBindEvent⟩, rfl, receipt⟩

end Vegas.Examples.LateOpeningRuntimeBobBindingService
