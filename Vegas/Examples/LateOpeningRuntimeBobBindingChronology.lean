/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobBindingPacket

/-! # Real activation metadata after the first accepted native binding

Every actual successful first binding makes Bob's disclosure ready and starts
its timer at clock three. The proof uses the actual handler transition and
allows every private submission representation with that successful result.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobBindingChronology

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeBobBindingService LateOpeningRuntimeBobBindingPacket
open LateOpeningRuntimeBobRawBinding (serviced serviced_physical)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

theorem accepted_handler (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (quiet : SilentRecall execution) (ready : execution.application.config.cut.Ready bobBindEvent)
    (material : app.Submission) (answer : Answer)
    (selected : (serviced execution ⟨some material⟩).application.config.store (.inr bobBindEvent) =
      some (.success answer)) :
    app.handle (execution.respond app bob ⟨some material⟩).application
      (responseMessage execution material) =
        some (serviced execution ⟨some material⟩).application := by
  let submitted := execution.respond app bob ⟨some material⟩
  have configSame := (LateOpeningRuntimeService.runtime.reactive_respond_application leaks
    execution bob ⟨some material⟩).1
  have absent : execution.application.config.store (.inr bobBindEvent) = none := by
    cases stored : execution.application.config.store (.inr bobBindEvent) with
    | none => rfl
    | some result =>
        have present : (execution.application.config.outputs bobBindEvent).isSome := by
          change (execution.application.config.store (.inr bobBindEvent)).isSome = true
          rw [stored]
          rfl
        exact (ready.1
          ((execution.application.config.output_available bobBindEvent).mp present)).elim
  rw [serviced_physical weight nonnegative execution trace quiet]
  change app.handle submitted.application (responseMessage execution material) =
    some ((app.handle submitted.application (responseMessage execution material)).getD
      submitted.application)
  cases handled : app.handle submitted.application (responseMessage execution material) with
  | some next => rfl
  | none =>
      rw [serviced_physical weight nonnegative execution trace quiet] at selected
      change ((app.handle submitted.application (responseMessage execution material)).getD
        submitted.application).config.store (.inr bobBindEvent) = _ at selected
      rw [handled] at selected
      change submitted.application.config.store (.inr bobBindEvent) = _ at selected
      rw [configSame, absent] at selected
      cases selected

theorem accepted_chronology (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (quiet : SilentRecall execution) (ready : execution.application.config.cut.Ready bobBindEvent)
    (response : app.Action) (answer : Answer)
    (selected : (serviced execution response).application.config.store (.inr bobBindEvent) =
      some (.success answer)) :
    (serviced execution response).application.config.cut.Ready bobRevealEvent ∧
      (serviced execution response).application.activatedAt bobRevealEvent = some 3 ∧
      (serviced execution response).application.clock = 3 := by
  obtain ⟨material, actionEq, ⟨candidate, call⟩, _, _, _⟩ := accepted_response weight nonnegative
    execution trace quiet ready response answer selected
  subst response
  let submitted := execution.respond app bob ⟨some material⟩
  let next := (serviced execution ⟨some material⟩).application
  have handled := accepted_handler weight nonnegative execution trace quiet ready material answer
    selected
  have raw := (reactiveApplication_handle_eq_some LateOpeningRuntimeService.runtime leaks
    submitted.application next (responseMessage execution material) handled).2
  have publicSame := (LateOpeningRuntimeService.runtime.reactive_respond_application leaks
    execution bob ⟨some material⟩).2
  obtain ⟨event, addressed, entered, action, member⟩ := handle_config_mem_step
    LateOpeningRuntimeService.runtime submitted.application next
      ⟨(bob, 0), (responseMessage execution material).payload.call⟩ raw
  have sameEvent : event = bobBindEvent := by
    simpa only [call, Payload.event?, Option.some.injEq] using addressed.symm
  subst event
  have revealReady : next.config.cut.Ready bobRevealEvent := by
    rw [Config.step, PMF.support_map] at member
    obtain ⟨value, _, sameConfig⟩ := member
    rw [← sameConfig]
    exact reveal_ready_after_binding submitted.application entered
  obtain ⟨bit, label, invariant⟩ := history_initial_invariant
    LateOpeningRuntimeService.runtime leaks LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) ⟨14, some bob, execution⟩ trace
  have unactivated : execution.application.activatedAt bobRevealEvent = none := by
    cases timer : execution.application.activatedAt bobRevealEvent with
    | none => rfl
    | some entered =>
        have beforeReady := ((invariant.activated_iff bobRevealEvent).mp
          (by rw [timer]; rfl)).1
        exact (ready.1 (beforeReady.2
          (by decide : bobBindEvent ∈ nativeGraph.order.predecessors bobRevealEvent))).elim
  have metadata := handle_clock_activated LateOpeningRuntimeService.runtime
    submitted.application next ⟨(bob, 0), (responseMessage execution material).payload.call⟩ raw
  have clock : execution.application.clock = 3 := by
    rw [clock_history weight nonnegative _ trace]
    have accounted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) trace
    change execution.environmentRecall.length + 14 = 26 at accounted
    have cursor : execution.environmentRecall.length = 12 := by omega
    rw [cursor]
    rfl
  have submittedClock : submitted.application.clock = 3 :=
    (congrArg PublicView.clock publicSame).trans clock
  refine ⟨revealReady, ?_, metadata.1.trans submittedClock⟩
  rw [metadata.2]
  unfold State.refreshActivated
  rw [dite_eq_left revealReady]
  change (submitted.application.activatedAt bobRevealEvent).orElse
    (fun _ => some submitted.application.clock) = _
  rw [show submitted.application.activatedAt = execution.application.activatedAt from
    congrArg PublicView.activatedAt publicSame, unactivated, submittedClock]
  rfl

theorem canonical_association (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (quiet : SilentRecall execution) (ready : execution.application.config.cut.Ready bobBindEvent)
    (material : app.Submission) (answer : Answer)
    (selected : (serviced execution ⟨some material⟩).application.config.store (.inr bobBindEvent) =
      some (.success answer))
    (packet : responseMessage execution material = LateOpeningRuntimeBobSuffix.bindingMessage) :
    (serviced execution ⟨some material⟩).application.accepted (.inr bobBindEvent) =
      some (bob, .prepared 0) := by
  have handled := accepted_handler weight nonnegative execution trace quiet ready material answer
    selected
  have raw := (reactiveApplication_handle_eq_some LateOpeningRuntimeService.runtime leaks
    _ _ _ handled).2
  have call : (responseMessage execution material).payload.call =
      .commitment bobBindEvent (bob, .prepared 0) := congrArg (fun message => message.payload.call)
        packet
  rw [call] at raw
  have tables := handle_commitment_tables LateOpeningRuntimeService.runtime _ _ (bob, 0)
    bobBindEvent (bob, .prepared 0) raw
  rw [tables.2.1]
  simp only [Function.update_self]

/-- Public packet certification and actual successful service identify Bob's
owner-visible immutable opening material; it is not a new cryptographic premise. -/
theorem canonical_openability (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (quiet : SilentRecall execution) (ready : execution.application.config.cut.Ready bobBindEvent)
    (material : app.Submission) (answer : Answer)
    (selected : (serviced execution ⟨some material⟩).application.config.store (.inr bobBindEvent) =
      some (.success answer))
    (packet : responseMessage execution material = LateOpeningRuntimeBobSuffix.bindingMessage) :
    (serviced execution ⟨some material⟩).application.accepted (.inr bobBindEvent) =
        some (bob, .prepared 0) ∧
      (serviced execution ⟨some material⟩).application.candidates.lookup (bob, .prepared 0) =
        .openable ⟨.range 0 5, answer⟩ := by
  have associated := canonical_association weight nonnegative execution trace quiet ready
    material answer selected packet
  obtain ⟨nextTrace⟩ := LateOpeningRuntimeBobRawBinding.serviced_trace weight nonnegative execution
    trace quiet ⟨some material⟩
  have aligned : (app.protocol ((setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := nativeGraph))) LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
      (some ⟨13, none, serviced execution ⟨some material⟩⟩) := by
    have initialEq : (setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := nativeGraph)) = initial := by
      rw [PMF.map_comp]
      rfl
    rwa [initialEq]
  have valid := LateOpeningRuntimeService.runtime.reactiveBindingInvariant_history leaks
    (setup.initialLaw.map setup.eventInputs) LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) aligned
  obtain ⟨candidate, accepted, _, fixed⟩ := valid.success_provenance bobBinding answer selected
  have candidateEq : candidate = (bob, .prepared 0) := Option.some.inj
    (accepted.symm.trans associated)
  exact ⟨associated, candidateEq ▸ fixed⟩

end Vegas.Examples.LateOpeningRuntimeBobBindingChronology
