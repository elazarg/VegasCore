/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLateHistories
import Vegas.Examples.LateOpeningRuntimeBobAudit
import Vegas.Examples.LateOpeningRuntimeBobIncentive
import Vegas.Examples.LateOpeningRuntimeCoverage
import Vegas.Pending.ReactiveBinding
import Interaction.ReactiveRawRoundTrace

/-! # A clean binding and delayed final disclosure in the actual service

Bob binds an arbitrary typed answer after Alice's accepted late opening,
remains silent at the optional callback, and reaches the final disclosure
callback while the binding is still immutable and its deadline has not passed.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobSuffix

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol
open LateOpeningRuntimeSource LateOpeningRuntimeService
open LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance
open LateOpeningRuntimeLateHistories LateOpeningRuntimeBobAudit LateOpeningRuntimeReadout

def bindingMaterial (answer : Answer) : app.Submission :=
  ⟨⟨.commitment bobBindEvent (bob, .prepared 0), some ⟨.range 0 5, answer⟩⟩, .none⟩

def binding (answer : Answer) : app.Action :=
  LateOpeningRuntimeService.runtime.reactiveBinding leaks bob bobBindEvent
    (.range 0 5) (.success answer) 0

def bindingMessage : Message Player app.Payload :=
  ⟨(bob, 0), ⟨.commitment bobBindEvent (bob, .prepared 0), none, some ⟨bobBindEvent⟩⟩⟩

def submitted (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) : app.Execution :=
  (answerDecision bit label slot seen).respond app bob (binding answer)

theorem answer_ready (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (answerDecision bit label slot seen).application.config.cut.Ready bobBindEvent := by
  rw [answerDecision_physical]
  change bobBindEvent ∉ ({aliceEvent} : Finset nativeGraph.EventId) ∧
    nativeGraph.order.predecessors bobBindEvent ⊆ {aliceEvent}
  decide

theorem answer_fresh (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (answerDecision bit label slot seen).application.candidates.lookup (bob, .prepared 0) =
      .fresh := by
  rw [answerDecision_physical]
  rfl

theorem binding_canonical (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    LateOpeningRuntimeService.runtime.canonicalServiceDecision leaks bob
      ((answerDecision bit label slot seen).recall bob)
      ((answerDecision bit label slot seen).observe app bob) bobBindEvent (.success answer) =
      binding answer := by
  exact LateOpeningRuntimeService.runtime.canonicalServiceDecision_binding leaks bob
    ((answerDecision bit label slot seen).recall bob)
    ((answerDecision bit label slot seen).observe app bob) bobBindEvent (.range 0 5)
    rfl rfl rfl 0 (by
      have count : (answerDecision bit label slot seen).application.publicView.bindingCount
          bob = 0 := by
        rw [answerDecision_physical]
        rfl
      rw [← count]
      apply canonicalFreshSlot_canonical
      change (answerDecision bit label slot seen).application.candidates.lookup
        (bob, .prepared ((answerDecision bit label slot seen).application.publicView.bindingCount
          bob)) = .fresh
      rw [count]
      exact answer_fresh bit label slot seen) (.success answer)

theorem answer_serial (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (answerDecision bit label slot seen).network.nextSerial bob = 0 := by
  change ((beforeLottery bit label slot seen).includePending app (alice, 0)).network.nextSerial
    bob = 0
  unfold ReactiveApplication.Execution.includePending
  rw [MessageNetwork.includePending, beforeLottery_lookup]
  fin_cases slot <;> cases seen <;> rfl

theorem binding_packet (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    app.packet (submitted bit label slot seen answer).application bob
      ((answerDecision bit label slot seen).network.known bob) (bindingMaterial answer) =
      bindingMessage.payload := by
  change app.packet (app.submit (answerDecision bit label slot seen).application bob
    (bindingMaterial answer)) bob _ (bindingMaterial answer) = _
  dsimp only [bindingMaterial]
  rw [LateOpeningRuntimeService.runtime.reactiveApplication_packet_none]
  change WitnessedPacket.mk _ _
    ((answerDecision bit label slot seen).application.publicView.tokenFor
      (.commitment bobBindEvent (bob, .prepared 0))) = _
  rw [(answerDecision bit label slot seen).application.publicView_tokenFor_of_ready
    (.commitment bobBindEvent (bob, .prepared 0)) bobBindEvent rfl
      (answer_ready bit label slot seen)]
  rfl

theorem submitted_ready (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (submitted bit label slot seen answer).application.config.cut.Ready bobBindEvent := by
  unfold submitted
  rw [(LateOpeningRuntimeService.runtime.reactive_respond_application leaks
    (answerDecision bit label slot seen) bob (binding answer)).1]
  exact answer_ready bit label slot seen

theorem submitted_timely (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (submitted bit label slot seen answer).application.WithinDeadline
      LateOpeningRuntimeService.runtime bobBindEvent := by
  change (answerDecision bit label slot seen).application.WithinDeadline
    LateOpeningRuntimeService.runtime bobBindEvent
  rw [answerDecision_physical]
  change 3 - 2 < 3
  decide

theorem submitted_result (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (submitted bit label slot seen answer).application.bindingResult
      (bob, .prepared 0) (.range 0 5) = .success answer :=
  LateOpeningRuntimeService.runtime.reactiveBinding_result leaks bob bobBindEvent
    (.range 0 5) (.success answer) 0 (answerDecision bit label slot seen)
      (answer_fresh bit label slot seen)

theorem submitted_config (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (submitted bit label slot seen answer).application.config =
      (answerDecision bit label slot seen).application.config :=
  (LateOpeningRuntimeService.runtime.reactive_respond_application leaks
    (answerDecision bit label slot seen) bob (binding answer)).1

theorem submitted_clock (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) : (submitted bit label slot seen answer).application.clock = 3 := by
  unfold submitted
  rw [LateOpeningRuntimeService.runtime.reactive_respond_clock, answerDecision_physical]

theorem submitted_reveal_unactivated (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (submitted bit label slot seen answer).application.activatedAt bobRevealEvent = none := by
  have same := congrArg (fun view : PublicView nativeGraph => view.activatedAt bobRevealEvent)
    (LateOpeningRuntimeService.runtime.reactive_respond_application leaks
      (answerDecision bit label slot seen) bob (binding answer)).2
  change (submitted bit label slot seen answer).application.activatedAt bobRevealEvent =
    (answerDecision bit label slot seen).application.activatedAt bobRevealEvent at same
  rw [same, answerDecision_physical]
  rfl

def boundPhysical (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) : app.State :=
  let state := (submitted bit label slot seen answer).application
  { state.complete bobBindEvent (submitted_ready bit label slot seen answer)
      (.success answer) (.success answer) with
    accepted := Function.update state.accepted (.inr bobBindEvent) (some (bob, .prepared 0))
    candidates := state.candidates.freeze (bob, .prepared 0) }

theorem handle_binding (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    app.handle (submitted bit label slot seen answer).application bindingMessage =
      some (boundPhysical bit label slot seen answer) := by
  rw [LateOpeningRuntimeService.runtime.reactiveApplication_handle_of_tokenValid leaks
    _ _ (by rfl)]
  change handle LateOpeningRuntimeService.runtime (submitted bit label slot seen answer).application
    ⟨(bob, 0), .commitment bobBindEvent (bob, .prepared 0)⟩ = _
  rw [LateOpeningRuntimeService.runtime.handle_commitment_eq
    (submitted bit label slot seen answer).application (bob, 0) bobBindEvent
    (bob, .prepared 0) bob (.range 0 5) rfl rfl rfl
    (submitted_ready bit label slot seen answer) (submitted_timely bit label slot seen answer)
    rfl rfl (by
      change (answerDecision bit label slot seen).application.accepted (.inr bobBindEvent) = none
      rw [answerDecision_physical]
      rfl) (by
      intro field
      change (answerDecision bit label slot seen).application.accepted field ≠ _
      rw [answerDecision_physical]
      cases field with
      | inl input =>
          fin_cases input
          · change some (alice, Slot.initial (⟨0, by decide⟩ : nativeGraph.InputId)) ≠
              some (bob, Slot.prepared 0)
            decide
          · change (none : Option (Handle nativeGraph)) ≠ some (bob, .prepared 0)
            simp
      | inr event =>
          fin_cases event <;>
            change (none : Option (Handle nativeGraph)) ≠ some (bob, .prepared 0)
          all_goals simp)]
  rw [submitted_result]
  rfl

theorem answer_pending (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (answerDecision bit label slot seen).network.pending = [] :=
  acceptedLottery_pending bit label slot seen

theorem answer_inputs (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (answerDecision bit label slot seen).network.inputs =
      [LateOpeningRuntimeLatePrefix.openingMessage bit] := by
  change ((beforeLottery bit label slot seen).includePending app (alice, 0)).network.inputs = _
  unfold ReactiveApplication.Execution.includePending
  rw [MessageNetwork.includePending, beforeLottery_lookup]
  fin_cases slot
  · change (beforeBob bit label 0).network.inputs = _
    rw [beforeBob_first_network]
    rfl
  · change [(⟨(alice, 0), app.packet (secondLateDecision bit label 1 seen).application alice []
      (disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩))⟩ :
        Message Player app.Payload)] = _
    rw [secondLate_opening_packet]
    rfl

theorem submitted_pending (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (submitted bit label slot seen answer).network.pending = [bindingMessage] := by
  change (answerDecision bit label slot seen).network.pending ++
    [⟨(bob, (answerDecision bit label slot seen).network.nextSerial bob),
      app.packet (submitted bit label slot seen answer).application bob
        ((answerDecision bit label slot seen).network.known bob) (bindingMaterial answer)⟩] = _
  rw [answer_pending, answer_serial, binding_packet]
  rfl

theorem submitted_inputs (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (submitted bit label slot seen answer).network.inputs =
      [LateOpeningRuntimeLatePrefix.openingMessage bit, bindingMessage] := by
  change (answerDecision bit label slot seen).network.inputs ++
    [⟨(bob, (answerDecision bit label slot seen).network.nextSerial bob),
      app.packet (submitted bit label slot seen answer).application bob
        ((answerDecision bit label slot seen).network.known bob) (bindingMaterial answer)⟩] = _
  rw [answer_inputs, answer_serial, binding_packet]
  rfl

theorem submitted_ledger (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (submitted bit label slot seen answer).network.ledger =
      [LateOpeningRuntimeLatePrefix.openingMessage bit] :=
  congrArg MessageNetwork.PlayerView.ledger (answerDecision_bobNetwork bit label slot seen)

theorem binding_lookup (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (submitted bit label slot seen answer).network.lookup (bob, 0) = some bindingMessage := by
  rw [MessageNetwork.lookup, submitted_pending]
  rfl

theorem binding_selection (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    latestAuthor bob ((submitted bit label slot seen answer).observeEnvironment app) =
      .include (bob, 0) := by
  unfold latestAuthor
  change (match (submitted bit label slot seen answer).network.pending.reverse.find?
      (fun message => decide (message.sender = bob ∧ message.id ∉
        (submitted bit label slot seen answer).network.ledger.map Message.id)) with
    | none => ReactiveApplication.Command.wait
    | some message => ReactiveApplication.Command.include message.id) = _
  rw [submitted_pending, submitted_ledger]
  rfl

def includedBinding (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) : app.Execution :=
  let execution := submitted bit label slot seen answer
  { execution.includePending app (bob, 0) with
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .include (bob, 0)⟩] }

theorem binding_environment (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (submitted bit label slot seen answer).environmentStep app (.include (bob, 0)) =
      PMF.pure (includedBinding bit label slot seen answer) := by
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rfl

theorem includedBinding_physical (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (includedBinding bit label slot seen answer).application =
      boundPhysical bit label slot seen answer := by
  change ((submitted bit label slot seen answer).includePending app (bob, 0)).application = _
  unfold ReactiveApplication.Execution.includePending
  rw [MessageNetwork.includePending, binding_lookup]
  change (app.handle (submitted bit label slot seen answer).application bindingMessage).getD _ = _
  rw [handle_binding]
  rfl

theorem includedBinding_pending (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (includedBinding bit label slot seen answer).network.pending = [] := by
  change ((submitted bit label slot seen answer).includePending app (bob, 0)).network.pending = _
  unfold ReactiveApplication.Execution.includePending
  rw [MessageNetwork.includePending, binding_lookup]
  change MessagePool.removeFirst (bob, 0)
    (submitted bit label slot seen answer).network.pending = []
  rw [submitted_pending]
  rfl

theorem includedBinding_inputs (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (includedBinding bit label slot seen answer).network.inputs =
      [LateOpeningRuntimeLatePrefix.openingMessage bit, bindingMessage] := by
  change ((submitted bit label slot seen answer).includePending app (bob, 0)).network.inputs = _
  unfold ReactiveApplication.Execution.includePending
  rw [MessageNetwork.includePending, binding_lookup]
  exact submitted_inputs bit label slot seen answer

theorem includedBinding_receipts (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (includedBinding bit label slot seen answer).receipts =
      [((alice, 0), true), ((bob, 0), true)] := by
  change ((submitted bit label slot seen answer).includePending app (bob, 0)).receipts = _
  unfold ReactiveApplication.Execution.includePending
  rw [MessageNetwork.includePending, binding_lookup]
  change (submitted bit label slot seen answer).receipts ++
    [((bob, 0), (app.handle (submitted bit label slot seen answer).application
      bindingMessage).isSome)] = _
  rw [handle_binding]
  change (answerDecision bit label slot seen).receipts ++ [((bob, 0), true)] = _
  change (acceptedLottery bit label slot seen).receipts ++ [((bob, 0), true)] = _
  rw [acceptedLottery_receipts_eq]
  rfl

theorem binding_round (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
      (submitted bit label slot seen answer) =
      PMF.pure (includedBinding bit label slot seen answer) := by
  rw [fixed_round weight nonnegative players _ _ 12 (.include (bob, 0)) rfl
    (by change PMF.pure (latestAuthor bob _) = _; rw [binding_selection])
    (binding_environment bit label slot seen answer)]
  rfl

theorem bound_stored (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (boundPhysical bit label slot seen answer).config.store (.inr bobBindEvent) =
      some (.success answer) := by
  exact EventGraph.Config.complete_output_same _ bobBindEvent _ (.success answer) (.success answer)

theorem bound_completed (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    bobBindEvent ∈ (boundPhysical bit label slot seen answer).config.cut.completed := by
  change bobBindEvent ∈ insert bobBindEvent
    (submitted bit label slot seen answer).application.config.cut.completed
  exact Finset.mem_insert_self _ _

theorem bound_completionOrder (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (boundPhysical bit label slot seen answer).publicView.observation.completionOrder =
      [aliceEvent, bobBindEvent] := by
  change ((submitted bit label slot seen answer).application.config.history ++
    [(⟨bobBindEvent, .success answer⟩ : nativeGraph.Completion)]).map
      EventGraph.Completion.event = _
  rw [submitted_config, answerDecision_physical]
  rfl

theorem bound_reveal_ready (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (boundPhysical bit label slot seen answer).config.cut.Ready bobRevealEvent := by
  change bobRevealEvent ∉ insert bobBindEvent
    (submitted bit label slot seen answer).application.config.cut.completed ∧
    nativeGraph.order.predecessors bobRevealEvent ⊆ insert bobBindEvent
      (submitted bit label slot seen answer).application.config.cut.completed
  rw [submitted_config, answerDecision_physical]
  change bobRevealEvent ∉ ({bobBindEvent, aliceEvent} : Finset nativeGraph.EventId) ∧
    nativeGraph.order.predecessors bobRevealEvent ⊆ {bobBindEvent, aliceEvent}
  decide

theorem bound_reveal_timer (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (boundPhysical bit label slot seen answer).activatedAt bobRevealEvent = some 3 := by
  change State.refreshActivated (boundPhysical bit label slot seen answer).config
    (submitted bit label slot seen answer).application.clock
      (submitted bit label slot seen answer).application.activatedAt bobRevealEvent = _
  unfold State.refreshActivated
  rw [dite_eq_left (bound_reveal_ready bit label slot seen answer)]
  change ((submitted bit label slot seen answer).application.activatedAt bobRevealEvent).orElse
    (fun _ => some (submitted bit label slot seen answer).application.clock) = _
  rw [submitted_reveal_unactivated, submitted_clock]
  rfl

theorem bound_clock (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) : (boundPhysical bit label slot seen answer).clock = 3 :=
  submitted_clock bit label slot seen answer

def optionalDecision (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) : app.Execution :=
  let execution := includedBinding bit label slot seen answer
  recorded execution (.activate bob) execution.application

def afterOptional (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) : app.Execution :=
  let execution := (optionalDecision bit label slot seen answer).respond app bob ⟨none⟩
  recorded execution .wait execution.application

def ticked (execution : app.Execution) : app.Execution :=
  recorded execution (.application .advanceClock)
    { execution.application with clock := execution.application.clock + 1 }

private theorem recorded_application (execution : app.Execution) (command : app.Command)
    (physical : app.State) : (recorded execution command physical).application = physical := rfl

private theorem recorded_cursor (execution : app.Execution) (command : app.Command)
    (physical : app.State) :
    (recorded execution command physical).environmentRecall.length =
      execution.environmentRecall.length + 1 := by
  simp only [recorded, List.length_append, List.length_singleton]

private theorem silent_application (execution : app.Execution) (who : Player) :
    (execution.respond app who ⟨none⟩).application = execution.application := rfl

theorem afterOptional_application (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (afterOptional bit label slot seen answer).application =
      (includedBinding bit label slot seen answer).application := by
  simp only [afterOptional, optionalDecision, recorded_application, silent_application]

private theorem ticked_three_application (execution : app.Execution) :
    (ticked (ticked (ticked execution))).application =
      { execution.application with clock := execution.application.clock + 3 } := rfl

theorem includedBinding_cursor (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (includedBinding bit label slot seen answer).environmentRecall.length = 13 := by
  change ((submitted bit label slot seen answer).environmentRecall ++ [_]).length = 13
  simp only [List.length_append, List.length_singleton]
  change (answerDecision bit label slot seen).environmentRecall.length + 1 = 13
  rfl

theorem optionalDecision_cursor (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (optionalDecision bit label slot seen answer).environmentRecall.length = 14 := by
  simp only [optionalDecision, recorded_cursor, includedBinding_cursor]

theorem afterOptional_cursor (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (afterOptional bit label slot seen answer).environmentRecall.length = 15 := by
  simp only [afterOptional, recorded_cursor, app.respond_environmentRecall, optionalDecision_cursor]

private theorem ticked_cursor (execution : app.Execution) :
    (ticked execution).environmentRecall.length = execution.environmentRecall.length + 1 :=
  recorded_cursor execution _ _

def beforeFinal (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) : app.Execution :=
  let execution := ticked (ticked (ticked (afterOptional bit label slot seen answer)))
  recorded execution (.application (.expire bobBindEvent)) execution.application

def finalDecision (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) : app.Execution :=
  let execution := beforeFinal bit label slot seen answer
  recorded execution (.activate bob) execution.application

theorem optional_activation (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (includedBinding bit label slot seen answer).environmentStep app (.activate bob) =
      PMF.pure (optionalDecision bit label slot seen answer) := by
  apply recorded_activation
  rw [includedBinding_pending]
  rfl

theorem optional_gate (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    bobBindEvent ∈ EventGraph.PublicObservation.completionOrder
      (includedBinding bit label slot seen answer).application.publicView.observation := by
  rw [includedBinding_physical, bound_completionOrder]
  simp

theorem afterOptional_pending (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (afterOptional bit label slot seen answer).network.pending = [] :=
  includedBinding_pending bit label slot seen answer

theorem beforeFinal_physical (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (beforeFinal bit label slot seen answer).application =
      { boundPhysical bit label slot seen answer with clock := 6 } := by
  unfold beforeFinal
  rw [recorded_application, ticked_three_application, afterOptional_application,
    includedBinding_physical, bound_clock]

theorem finalDecision_physical (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (finalDecision bit label slot seen answer).application =
      { boundPhysical bit label slot seen answer with clock := 6 } := by
  unfold finalDecision
  rw [recorded_application]
  exact beforeFinal_physical bit label slot seen answer

theorem beforeFinal_cursor (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) : (beforeFinal bit label slot seen answer).environmentRecall.length = 19 := by
  simp only [beforeFinal, recorded_cursor, ticked_cursor, afterOptional_cursor]

theorem final_activation (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (beforeFinal bit label slot seen answer).environmentStep app (.activate bob) =
      PMF.pure (finalDecision bit label slot seen answer) := by
  apply recorded_activation
  change foreignPending bob (afterOptional bit label slot seen answer).network.pending = ∅
  rw [afterOptional_pending]
  rfl

theorem final_ready (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (finalDecision bit label slot seen answer).application.config.cut.Ready bobRevealEvent := by
  rw [finalDecision_physical]
  exact bound_reveal_ready bit label slot seen answer

theorem final_timely (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (finalDecision bit label slot seen answer).application.WithinDeadline
      LateOpeningRuntimeService.runtime bobRevealEvent := by
  rw [finalDecision_physical]
  unfold State.WithinDeadline
  change (match (boundPhysical bit label slot seen answer).activatedAt bobRevealEvent with
    | none => False
    | some entered => 6 - entered < 4)
  rw [bound_reveal_timer]
  decide

theorem final_bound (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (finalDecision bit label slot seen answer).application.config.store (.inr bobBindEvent) =
      some (.success answer) := by
  rw [finalDecision_physical]
  exact bound_stored bit label slot seen answer

theorem final_inputs (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (finalDecision bit label slot seen answer).network.inputs =
      [LateOpeningRuntimeLatePrefix.openingMessage bit, bindingMessage] :=
  includedBinding_inputs bit label slot seen answer

theorem final_receipts (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) :
    (finalDecision bit label slot seen answer).receipts =
      [((alice, 0), true), ((bob, 0), true)] := by
  have recordedReceipts (execution : app.Execution) (command : app.Command) (physical : app.State) :
      (recorded execution command physical).receipts = execution.receipts := rfl
  simp only [finalDecision, beforeFinal, ticked, afterOptional, optionalDecision, recordedReceipts,
    app.respond_receipts]
  exact includedBinding_receipts bit label slot seen answer

theorem final_clean (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (answer : Answer) : CleanBindings (finalDecision bit label slot seen answer) := by
  intro message member owner
  rw [final_inputs] at member
  rcases List.mem_cons.mp member with rfl | last
  · exact ((by decide : alice ≠ bob) owner).elim
  · have same := List.mem_singleton.mp last
    subst message
    refine ⟨some ⟨bobBindEvent⟩, rfl, ?_⟩
    rw [final_receipts]
    simp [bindingMessage]

theorem binding_in_raw_menu (answer : Answer) (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) : binding answer ∈ rawMenu.actions who past view := by
  change _ ∈ (ReactiveApplication.ResponseMenu.fromSubmissions
    (fun _ past view => bounds.submissions
      (ReactiveApplication.ResponseMenu.knownPackets past view))).actions who past view
  rw [ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  change bindingMaterial answer ∈
    bounds.submissions (ReactiveApplication.ResponseMenu.knownPackets past view)
  rw [MessageBounds.submissions_mem]
  have covered := binding_values_covered bobBindEvent
  change ∀ value : Answer, (⟨.range 0 5, value⟩ : Raw simpleExpr) ∈ bounds.values at covered
  exact ⟨⟨by change 0 < 26; decide, covered answer⟩, trivial⟩

private theorem silence_in_raw_menu (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) : (⟨none⟩ : app.Action) ∈ rawMenu.actions who past view := by
  change _ ∈ (ReactiveApplication.ResponseMenu.fromSubmissions
    (fun _ past view => bounds.submissions
      (ReactiveApplication.ResponseMenu.knownPackets past view))).actions who past view
  rw [ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  trivial

private theorem trace_fixed (weight : ℝ) (nonnegative : 0 ≤ weight)
    (remaining position : Nat) (execution next : app.Execution) (command : app.Command)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (cursor : execution.environmentRecall.length = position)
    (selected : stageChoice weight nonnegative position (execution.observeEnvironment app) =
      PMF.pure command)
    (moved : execution.environmentStep app command = PMF.pure next) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining, command.actor? app, next⟩)) := by
  apply rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) remaining execution next command trace
  · change command ∈ (stageChoice weight nonnegative execution.environmentRecall.length
      (execution.observeEnvironment app)).support
    rw [cursor, selected]
    simp
  · rw [moved]
    simp

theorem includedBinding_trace (weight : ℝ) (nonnegative : 0 ≤ weight) (positive : 0 < weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false) (answer : Answer) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨13, none, includedBinding bit label slot seen answer⟩)) := by
  obtain ⟨prior⟩ :=
    answerDecision_trace weight nonnegative positive bit label slot seen samplePossible
  obtain ⟨sent⟩ := rawMenu.trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 (answerDecision bit label slot seen)
      bob (binding answer) prior (binding_in_raw_menu answer _ _ _)
  exact trace_fixed weight nonnegative 13 12 (submitted bit label slot seen answer)
    (includedBinding bit label slot seen answer) (.include (bob, 0)) sent rfl
    (by change PMF.pure (latestAuthor bob _) = _; rw [binding_selection])
    (binding_environment bit label slot seen answer)

theorem afterOptional_trace (weight : ℝ) (nonnegative : 0 ≤ weight) (positive : 0 < weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false) (answer : Answer) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨11, none, afterOptional bit label slot seen answer⟩)) := by
  obtain ⟨prior⟩ := includedBinding_trace weight nonnegative positive bit label slot seen
    samplePossible answer
  obtain ⟨active⟩ := trace_fixed weight nonnegative 12 13
    (includedBinding bit label slot seen answer) (optionalDecision bit label slot seen answer)
    (.activate bob) prior (includedBinding_cursor bit label slot seen answer) (by
      change PMF.pure (if bobBindEvent ∈ EventGraph.PublicObservation.completionOrder
        (includedBinding bit label slot seen answer).application.publicView.observation
          then (.activate bob : app.Command) else .wait) = _
      rw [ite_eq_left (optional_gate bit label slot seen answer)])
    (optional_activation bit label slot seen answer)
  obtain ⟨silent⟩ := rawMenu.trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 12
      (optionalDecision bit label slot seen answer) bob ⟨none⟩ active (silence_in_raw_menu _ _ _)
  let execution := (optionalDecision bit label slot seen answer).respond app bob ⟨none⟩
  exact trace_fixed weight nonnegative 11 14 execution (afterOptional bit label slot seen answer)
    .wait silent (by
      rw [app.respond_environmentRecall]
      exact optionalDecision_cursor bit label slot seen answer) (by
      have gate : bobBindEvent ∈ execution.application.publicView.observation.completionOrder :=
        optional_gate bit label slot seen answer
      change PMF.pure
        (if bobBindEvent ∈ execution.application.publicView.observation.completionOrder
          then latestAuthor bob _ else .wait) = _
      rw [ite_eq_left gate]
      unfold latestAuthor
      change PMF.pure
        (match (includedBinding bit label slot seen answer).network.pending.reverse.find? _ with
          | none => _ | some message => _) = _
      rw [includedBinding_pending]
      rfl) (recorded_wait execution)

private theorem recorded_completed_expiry (execution : app.Execution)
    (completed : bobBindEvent ∈ execution.application.config.cut.completed) :
    execution.environmentStep app (.application (.expire bobBindEvent)) =
      PMF.pure (recorded execution (.application (.expire bobBindEvent))
        execution.application) := by
  rw [ReactiveApplication.Execution.environmentStep]
  change ((environmentStep LateOpeningRuntimeService.runtime execution.application
    (.expire bobBindEvent)).map _).map _ = _
  rw [environmentStep_expire_of_not_ready LateOpeningRuntimeService.runtime _ bobBindEvent
    (fun ready => ready.1 completed), PMF.pure_map, PMF.pure_map]
  rfl

theorem beforeFinal_trace (weight : ℝ) (nonnegative : 0 ≤ weight) (positive : 0 < weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false) (answer : Answer) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨7, none, beforeFinal bit label slot seen answer⟩)) := by
  obtain ⟨prior⟩ := afterOptional_trace weight nonnegative positive bit label slot seen
    samplePossible answer
  let execution := afterOptional bit label slot seen answer
  obtain ⟨first⟩ := trace_fixed weight nonnegative 10 15 execution (ticked execution)
    (.application .advanceClock) prior (afterOptional_cursor bit label slot seen answer) rfl
      (recorded_clock execution)
  obtain ⟨second⟩ := trace_fixed weight nonnegative 9 16 (ticked execution)
    (ticked (ticked execution)) (.application .advanceClock) first
      (by rw [ticked_cursor, afterOptional_cursor]) rfl
      (recorded_clock (ticked execution))
  obtain ⟨third⟩ := trace_fixed weight nonnegative 8 17 (ticked (ticked execution))
    (ticked (ticked (ticked execution))) (.application .advanceClock) second
      (by rw [ticked_cursor, ticked_cursor, afterOptional_cursor]) rfl
    (recorded_clock (ticked (ticked execution)))
  have completed : bobBindEvent ∈
      (ticked (ticked (ticked execution))).application.config.cut.completed := by
    change bobBindEvent ∈
      (includedBinding bit label slot seen answer).application.config.cut.completed
    rw [includedBinding_physical]
    exact bound_completed bit label slot seen answer
  exact trace_fixed weight nonnegative 7 18 (ticked (ticked (ticked execution)))
    (beforeFinal bit label slot seen answer) (.application (.expire bobBindEvent)) third
      (by rw [ticked_cursor, ticked_cursor, ticked_cursor, afterOptional_cursor]) rfl
    (recorded_completed_expiry _ completed)

/-- The clean delayed disclosure is an actual active history of the full
bounded raw game for every answer, preference label and possible sample. -/
theorem finalDecision_trace (weight : ℝ) (nonnegative : 0 ≤ weight) (positive : 0 < weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false) (answer : Answer) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨6, some bob, finalDecision bit label slot seen answer⟩)) := by
  obtain ⟨prior⟩ :=
    beforeFinal_trace weight nonnegative positive bit label slot seen samplePossible answer
  exact trace_fixed weight nonnegative 6 19 (beforeFinal bit label slot seen answer)
    (finalDecision bit label slot seen answer) (.activate bob) prior
      (beforeFinal_cursor bit label slot seen answer) rfl
    (final_activation bit label slot seen answer)

def decisionHistory (weight : ℝ) (nonnegative : 0 ≤ weight) (positive : 0 < weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false) (answer : Answer) :
    LateOpeningRuntimeBobIncentive.DecisionHistory weight nonnegative where
  execution := finalDecision bit label slot seen answer
  trace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
      (finalDecision_trace weight nonnegative positive bit label slot seen
        samplePossible answer).some
  answer := answer
  bound := final_bound bit label slot seen answer
  ready := final_ready bit label slot seen answer
  timely := final_timely bit label slot seen answer
  clean := final_clean bit label slot seen answer

theorem final_disclosure_class_nonempty (weight : ℝ) (nonnegative : 0 ≤ weight)
    (positive : 0 < weight) :
    Nonempty (LateOpeningRuntimeBobIncentive.DecisionHistory weight nonnegative) :=
  ⟨decisionHistory weight nonnegative positive false 0 0 false (Or.inl rfl) safe⟩

end Vegas.Examples.LateOpeningRuntimeBobSuffix
