/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeEarlyBobSafeMenu

/-! # Fresh receiver bindings after arbitrary earlier raw responses

The live first binding can use an actually fresh prepared handle even when an
earlier response poisoned the canonical handle. The native handler accepts that
handle and fixes the selected answer. No assumption of silent own recall occurs.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobFreshBinding

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeBobBindingService LateOpeningRuntimeBobResponseMenu

/-- A genuine native binding response for an arbitrary prepared slot. -/
def response (serial : Nat) (answer : Answer) : app.Action :=
  LateOpeningRuntimeService.runtime.reactiveBinding leaks bob bobBindEvent
    (.range 0 5) (.success answer) serial

/-- The envelope uses the actual next message identifier, independently of
its prepared-handle serial. -/
def message (execution : app.Execution) (serial : Nat) : Message Player app.Payload :=
  ⟨(bob, execution.network.nextSerial bob),
    ⟨.commitment bobBindEvent (bob, .prepared serial), none, some ⟨bobBindEvent⟩⟩⟩

/-- The actual witnessed submission carried by the fresh binding response. -/
def material (serial : Nat) (answer : Answer) : WitnessedSubmission nativeGraph :=
  ⟨⟨.commitment bobBindEvent (bob, .prepared serial), some ⟨.range 0 5, answer⟩⟩, .none⟩

theorem fresh_binding_packet (execution : app.Execution) (serial : Nat)
    (ready : execution.application.config.cut.Ready bobBindEvent) (answer : Answer) :
    app.packet (app.submit execution.application bob (material serial answer)) bob
      (execution.network.known bob) (material serial answer) =
        (message execution serial).payload := by
  dsimp only [material]
  rw [LateOpeningRuntimeService.runtime.reactiveApplication_packet_none]
  change WitnessedPacket.mk _ _ (execution.application.publicView.tokenFor
    (.commitment bobBindEvent (bob, .prepared serial))) = _
  rw [execution.application.publicView_tokenFor_of_ready
    (.commitment bobBindEvent (bob, .prepared serial)) bobBindEvent rfl ready]
  rfl

/-- Handler acceptance does not make a fallback handle conforming to the
settled audit: the single Bob binding has canonical serial zero. -/
theorem noncanonical_binding_forbidden (record : SettledRecord nativeGraph)
    (execution : app.Execution) (serial : Nat) (different : serial ≠ 0)
    (completed : bobBindEvent ∈ record.view.observation.completionOrder) :
    record.permits (message execution serial) = false := by
  classical
  apply decide_eq_false_iff_not.mpr
  intro permitted
  change record.view.Unsettled bobBindEvent ∨
    (record.Accepts (message execution serial).id ∧
      record.SettledContent (message execution serial)) at permitted
  rcases permitted with unsettled | ⟨_, content⟩
  · exact unsettled completed
  · change (none : Option (OpeningFact nativeGraph)) = none ∧
      (bob, Slot.prepared (inputCount := nativeGraph.inputCount) serial) =
        (bob, Slot.prepared (record.view.bindingCountBefore bob bobBindEvent)) at content
    rw [LateOpeningRuntimeBobAudit.binding_count_before] at content
    cases content.2
    exact different rfl

/-- A fresh timely first binding is accepted even after an earlier raw
response, and opens the actual final-publication window. -/
theorem fresh_binding_acceptance (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (serial : Nat)
    (fresh : control.execution.application.candidates.lookup (bob, .prepared serial) = .fresh)
    (ready : control.execution.application.config.cut.Ready bobBindEvent)
    (timely : control.execution.application.WithinDeadline
      LateOpeningRuntimeService.runtime bobBindEvent) (answer : Answer) :
    ∃ state, app.handle (control.execution.respond app bob
        (response serial answer)).application
          (message control.execution serial) = some state ∧
      state.config.store (.inr bobBindEvent) = some (.success answer) ∧
      state.accepted (.inr bobBindEvent) = some (bob, .prepared serial) ∧
      state.config.cut.Ready bobRevealEvent ∧
      state.activatedAt bobRevealEvent = some control.execution.application.clock := by
  have original : (app.protocol ((setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph)))
      LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ).Trace (some control) := by
    have initialEq : (setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := nativeGraph)) = initial := by
      rw [PMF.map_comp]
      rfl
    rwa [initialEq]
  have valid := LateOpeningRuntimeService.runtime.reactiveBindingInvariant_history leaks
    (setup.initialLaw.map setup.eventInputs) LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) original
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
  have unused : control.execution.application.HandleUnused (bob, .prepared serial) :=
    fun field associated => valid.accepted_fixed field _ associated fresh
  let submitted := control.execution.respond app bob (response serial answer)
  have unchanged := LateOpeningRuntimeService.runtime.reactive_respond_application leaks
    control.execution bob (response serial answer)
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
    (.range 0 5) (.success answer) serial control.execution fresh
  let state : EventGraphRuntime.State nativeGraph :=
    { submitted.application.complete bobBindEvent readySubmitted
        (.success answer) (.success answer) with
      accepted := Function.update submitted.application.accepted (.inr bobBindEvent)
        (some (bob, .prepared serial))
      candidates := submitted.application.candidates.freeze (bob, .prepared serial) }
  have handled : app.handle submitted.application (message control.execution serial) =
      some state := by
    rw [LateOpeningRuntimeService.runtime.reactiveApplication_handle_of_tokenValid leaks
      _ _ (by rfl)]
    change handle LateOpeningRuntimeService.runtime submitted.application
      ⟨(bob, control.execution.network.nextSerial bob),
        .commitment bobBindEvent (bob, .prepared serial)⟩ = some state
    rw [LateOpeningRuntimeService.runtime.handle_commitment_eq submitted.application
      (bob, control.execution.network.nextSerial bob)
      bobBindEvent (bob, .prepared serial) bob (.range 0 5) rfl rfl rfl
        readySubmitted timelySubmitted
        rfl rfl ((congrFun sameAccepted (.inr bobBindEvent)).trans vacant) (by
          intro field associated
          apply unused field
          rwa [sameAccepted] at associated)]
    change some ({ submitted.application.complete bobBindEvent readySubmitted
      (submitted.application.bindingResult (bob, .prepared serial) (.range 0 5))
      (submitted.application.bindingResult (bob, .prepared serial) (.range 0 5)) with
        accepted := Function.update submitted.application.accepted (.inr bobBindEvent)
          (some (bob, .prepared serial))
        candidates := submitted.application.candidates.freeze (bob, .prepared serial) }) =
          some state
    rw [show submitted.application.bindingResult (bob, .prepared serial) (.range 0 5) =
      .success answer from value]
  have revealReady : state.config.cut.Ready bobRevealEvent :=
    reveal_ready_after_binding submitted.application readySubmitted
  refine ⟨state, handled, ?_, ?_, revealReady, ?_⟩
  · change (submitted.application.config.complete bobBindEvent readySubmitted
      (.success answer) (.success answer)).outputs bobBindEvent = some (.success answer)
    exact Config.complete_output_same _ _ _ _ _
  · change Function.update submitted.application.accepted (.inr bobBindEvent)
      (some (bob, .prepared serial)) (.inr bobBindEvent) = _
    simp only [Function.update_self]
  · change State.refreshActivated state.config submitted.application.clock
      submitted.application.activatedAt bobRevealEvent = _
    unfold State.refreshActivated
    rw [dite_eq_left revealReady]
    change (submitted.application.activatedAt bobRevealEvent).orElse
      (fun _ => some submitted.application.clock) = _
    rw [sameTimers, unactivated, sameClock]
    rfl

/-- The actual bounded canonical response selects a fresh slot even after
arbitrary earlier responses. Its handler acceptance needs no clean recall. -/
theorem fresh_binding_choice (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor = some bob)
    (ready : control.execution.application.config.cut.Ready bobBindEvent)
    (answer : Answer) :
    ∃ serial, serial < bounds.candidateCount ∧
      control.execution.application.candidates.lookup (bob, .prepared serial) = .fresh ∧
      LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
        (control.execution.recall bob) (control.execution.observe app bob) bobBindEvent
          (.success answer) = response serial answer ∧
      response serial answer ∈
        rawMenu.actions bob (control.execution.recall bob) (control.execution.observe app bob) := by
  have initialEq : (setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph)) = initial := by
    rw [PMF.map_comp]
    rfl
  have inputTrace : (rawMenu.protocol
      ((setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := nativeGraph)))
      LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control) := by
    rwa [initialEq]
  obtain ⟨unused, _, freshSlot⟩ :=
    LateOpeningRuntimeService.runtime.reactiveFreshSlot_lt_horizon leaks
      (setup.initialLaw.map setup.eventInputs) LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) control
      (rawMenu.toRawTrace _ _ _ inputTrace) bob active
  obtain ⟨serial, selected⟩ := canonicalFreshSlot_isSome bob
    (control.execution.observe app bob).application unused freshSlot
  have resources := bounded_resources weight nonnegative control trace active
  have small : serial < bounds.candidateCount := by
    unfold canonicalFreshSlot at selected
    split at selected
    · cases Option.some.inj selected
      change control.execution.application.publicView.bindingCount bob < 26
      rw [binding_count_zero control.execution.application ready.1]
      decide
    · exact resources.2 serial selected
  have fresh := canonicalFreshSlot_spec bob
    (control.execution.observe app bob).application serial selected
  have binding : LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
      (control.execution.recall bob) (control.execution.observe app bob) bobBindEvent
        (.success answer) = response serial answer :=
    LateOpeningRuntimeService.runtime.canonicalServiceDecision_binding leaks bob
      (control.execution.recall bob) (control.execution.observe app bob) bobBindEvent
        (.range 0 5) rfl rfl rfl serial selected (.success answer)
  refine ⟨serial, small, fresh, binding, ?_⟩
  rw [← binding]
  exact LateOpeningRuntimeEarlyBobSafeMenu.binding_available weight nonnegative answer
    control trace active ready.1

/-- The existing native answer policy uses the available fresh fallback slot. -/
theorem answerPolicy_fresh_binding (weight : ℝ) (nonnegative : 0 ≤ weight)
    (control : app.Control)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace (some control))
    (active : control.actor = some bob)
    (ready : control.execution.application.config.cut.Ready bobBindEvent)
    (clock : control.execution.application.clock = 3) (answer : Answer) :
    ∃ serial, serial < bounds.candidateCount ∧
      control.execution.application.candidates.lookup (bob, .prepared serial) = .fresh ∧
      LateOpeningRuntimeBobSafeContinuation.answerPolicy answer
        (control.execution.recall bob) (control.execution.observe app bob) =
          PMF.pure (response serial answer) := by
  obtain ⟨serial, small, fresh, binding, _⟩ :=
    fresh_binding_choice weight nonnegative control trace active ready answer
  have missing : bobBindEvent ∉
      (control.execution.observe app bob).application.publicView.observation.completionOrder := by
    intro completed
    exact ready.1 ((control.execution.application.config.history_exact bobBindEvent).mp completed)
  have viewed : (control.execution.observe app bob).application.publicView.clock = 3 := clock
  refine ⟨serial, small, fresh, ?_⟩
  simp only [LateOpeningRuntimeBobSafeContinuation.answerPolicy,
    ite_eq_left viewed, ite_eq_right missing]
  rw [binding]

/-- Fresh binding is serviced in one physical round, retaining all prior inputs. -/
theorem fresh_binding_round (weight : ℝ) (nonnegative : 0 ≤ weight) (remaining : Nat)
    (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining, some bob, execution⟩))
    (serial : Nat)
    (fresh : execution.application.candidates.lookup (bob, .prepared serial) = .fresh)
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (timely : execution.application.WithinDeadline
      LateOpeningRuntimeService.runtime bobBindEvent) (answer : Answer) :
    ∃ next, (∀ players : Player → app.Policy,
      app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
        (execution.respond app bob (response serial answer)) = PMF.pure next) ∧
      next.application.config.store (.inr bobBindEvent) = some (.success answer) ∧
      ((bob, execution.network.nextSerial bob), true) ∈ next.receipts ∧
      next.application.config.cut.Ready bobRevealEvent ∧
      next.application.activatedAt bobRevealEvent = some execution.application.clock ∧
      next.network.inputs = execution.network.inputs ++
        [(message execution serial)] := by
  have serials := app.serialsBeforeNext_history (LateOpeningRuntimeService.scheduler
    weight nonnegative) initial LateOpeningRuntimeService.horizon trace
  obtain ⟨physical, accepted, stored, associated, revealReady, revealTimer⟩ :=
    fresh_binding_acceptance weight nonnegative ⟨remaining, some bob, execution⟩ trace serial fresh
      ready timely answer
  let submitted := execution.respond app bob (response serial answer)
  let included := submitted.includePending app (bob, execution.network.nextSerial bob)
  let next : app.Execution := { included with environmentRecall :=
    submitted.environmentRecall ++
      [⟨submitted.observeEnvironment app, .include (bob, execution.network.nextSerial bob)⟩] }
  have selected := latestAuthor_after_submit execution bob
    (material serial answer) serials
  have chosen : LateOpeningRuntimeService.scheduler weight nonnegative submitted.environmentRecall
      (submitted.observeEnvironment app) =
        PMF.pure (.include (bob, execution.network.nextSerial bob)) := by
    have served := protected_response_scheduler weight nonnegative
      ⟨remaining, some bob, execution⟩ trace bob rfl
        (response serial answer) (Or.inl rfl)
    apply served.trans
    apply congrArg PMF.pure
    exact selected
  have emitted := fresh_binding_packet execution serial ready answer
  have found : submitted.network.lookup (bob, execution.network.nextSerial bob) =
      some (message execution serial) := by
    change (execution.network.submit bob
      (app.packet (app.submit execution.application bob
        (material serial answer)) bob
          (execution.network.known bob)
          (material serial answer))).2.lookup (bob, execution.network.nextSerial bob) = _
    rw [serials.lookup_submit, emitted]
    rfl
  have nextPhysical : next.application = physical := by
    change (submitted.includePending app
      (bob, execution.network.nextSerial bob)).application = physical
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [found]
    change (app.handle submitted.application (message execution serial)).getD _ = _
    rw [accepted]
    rfl
  have receipt : ((bob, execution.network.nextSerial bob), true) ∈ next.receipts := by
    change ((bob, execution.network.nextSerial bob), true) ∈
      (submitted.includePending app (bob, execution.network.nextSerial bob)).receipts
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [found]
    change ((bob, execution.network.nextSerial bob), true) ∈ submitted.receipts ++
      [((bob, execution.network.nextSerial bob),
        (app.handle submitted.application (message execution serial)).isSome)]
    rw [accepted]
    simp
  have inputs : next.network.inputs = execution.network.inputs ++
      [(message execution serial)] := by
    change (submitted.includePending app (bob, execution.network.nextSerial bob)).network.inputs = _
    rw [app.includePending_network]
    unfold MessageNetwork.includePending
    rw [found]
    change execution.network.inputs ++ [⟨(bob, execution.network.nextSerial bob),
      app.packet (app.submit execution.application bob
        (material serial answer)) bob
          (execution.network.known bob) (material serial answer)⟩] = _
    rw [emitted]
    rfl
  refine ⟨next, ?_, nextPhysical ▸ stored, receipt, nextPhysical ▸ revealReady,
    nextPhysical ▸ revealTimer, inputs⟩
  · intro players
    rw [ReactiveApplication.round, chosen, PMF.pure_bind, ReactiveApplication.dispatch]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
    rfl

end Vegas.Examples.LateOpeningRuntimeBobFreshBinding
