/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkNativeInputs
import Vegas.Examples.PrivateResolutionForkCompletionBounds
import Vegas.Pending.ReactiveWithholdingReceipts
import Interaction.ReactiveSubmissionAudit
import Interaction.ReactiveRecordedResponse

/-! # Actual accepting receipt origins in the public resolution fork

A receipt at a legal initialized raw prefix belongs to an actual ledger
envelope and its exact recorded fresh submission. At Bob's turn that submission
is one of Alice's two actual responses; a second response allocated as zero
has a literal earlier WAIT. These facts do not identify an incoming probability
law or exclude acceptance at the first response.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory.Protocol

theorem alice_zero_receipt_origin (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (accepted : ((alice, 0), true) ∈ control.execution.receipts) :
    ∃ (message : Message Player (WitnessedPacket nativeGraph))
      (entry : app.PlayerEntry) (material : app.Submission),
      message ∈ control.execution.network.ledger ∧ message.id = (alice, 0) ∧
      entry ∈ control.execution.recall alice ∧ entry.action.transmission = some material ∧
      entry.emitted = some message ∧
      control.execution.submissionOrigin? app (alice, 0) = some entry ∧
      app.submissionObservation? control.execution.environmentRecall (alice, 0) =
        some entry.beforeView.application.publicView := by
  have rawTrace := trace
  rw [initialLaw_eq_inputs] at rawTrace
  obtain ⟨message, present, identified, _⟩ :=
    (runtime setup).withholdingReceipts_history leaks (setup.initialLaw.map setup.eventInputs)
      horizon scheduler control rawTrace (alice, 0) accepted
  have audited := app.submissionAudit_history (fun view => view.publicView)
    (by intro state who; rfl) (initialLaw setup) horizon scheduler trace
  obtain ⟨entry, origin, emitted, observed⟩ := audited.1.ledger message present
  rw [identified] at origin observed
  have member : entry ∈ control.execution.recall alice := List.mem_of_find?_eq_some origin
  have submitted := List.find?_some origin
  cases chosen : entry.action.transmission with
  | none => simp [ReactiveApplication.PlayerEntry.submitsId, chosen] at submitted
  | some material =>
      exact ⟨message, entry, material, present, identified, member, chosen, emitted,
        origin, observed⟩

/-- The serial-zero envelope has no preceding genuine own transmission. The
recorded response is recovered at its actual earlier raw decision history. -/
theorem zero_recorded_prior_wait (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (before after : List app.PlayerEntry) (entry : app.PlayerEntry)
    (message : Message Player (WitnessedPacket nativeGraph)) (material : app.Submission)
    (recalled : control.execution.recall alice = before ++ entry :: after)
    (submitted : entry.action.transmission = some material)
    (emitted : entry.emitted = some message) (identified : message.id = (alice, 0)) :
    ∀ earlier ∈ before, earlier.action.transmission = none := by
  have atIndex : (control.execution.recall alice)[before.length]? = some entry := by
    rw [recalled]
    simp
  have ownMember := app.recallOwnPlay_getElem (control.execution.recall alice)
    before.length entry atIndex
  have taken : (control.execution.recall alice).take before.length = before := by
    rw [recalled]
    simp
  rw [taken] at ownMember
  have actualMember : (some (before, entry.beforeView), entry.action) ∈
      (app.information (initialLaw setup) horizon scheduler).ownPlay alice trace := by
    change _ ∈ (app.signals (initialLaw setup) horizon scheduler).ownPlay alice trace
    rw [app.trace_ownPlay]
    exact ownMember
  obtain ⟨prior, joint, legal, next, moved, fuel, observed, chosen, path⟩ :=
    (app.information (initialLaw setup) horizon scheduler).ownPlay_prefix alice trace actualMember
  change (app.signals (initialLaw setup) horizon scheduler).infoOf alice prior.trace = _
    at observed
  rw [app.info] at observed
  cases priorState : prior.state with
  | none => simp [priorState, ReactiveApplication.observe] at observed
  | some previous =>
      by_cases active : previous.actor = some alice
      · simp only [priorState, ReactiveApplication.observe, active, ite_true] at observed
        have previousRecall := (Prod.mk.inj (Option.some.inj observed)).1
        have afterState : next = some ⟨previous.remaining, none,
            previous.execution.respond app alice entry.action⟩ := by
          change next ∈
            (app.transition (initialLaw setup) horizon scheduler prior.state joint).support
            at moved
          simpa only [priorState, ReactiveApplication.transition, active, chosen,
            Option.getD_some, PMF.mem_support_pure_iff] using moved
        have retained := app.reaches_recall_prefix (initialLaw setup) horizon scheduler path
          ⟨previous.remaining, none, previous.execution.respond app alice entry.action⟩
          control afterState rfl alice
        obtain ⟨actualEmission, appended, allocated⟩ :=
          respond_recall_self setup leaks previous.execution alice entry.action
        rw [appended, previousRecall, recalled] at retained
        obtain ⟨suffix, same⟩ := retained
        have entryEq : (⟨previous.execution.observe app alice, entry.action,
            actualEmission⟩ : app.PlayerEntry) = entry := by
          have tailEq := List.append_cancel_left (by
            simpa only [List.append_assoc, List.singleton_append] using same)
          exact (List.cons.inj tailEq).1
        have actualEmitted : actualEmission = some message := by
          rw [← emitted, ← entryEq]
        have zero := allocated material submitted message actualEmitted
        have waited := fresh_zero_prior_wait previous (priorState ▸ prior.trace) material (by
          change (alice, previous.execution.network.nextSerial alice) = (alice, 0)
          exact zero.symm.trans identified)
        rw [previousRecall] at waited
        exact waited
      · simp [priorState, ReactiveApplication.observe, active] at observed

theorem bob_zero_receipt_response_cases (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (active : control.actor = some bob)
    (accepted : ((alice, 0), true) ∈ control.execution.receipts) :
    ∃ (first second : app.PlayerEntry) (message : Message Player (WitnessedPacket nativeGraph)),
      control.execution.recall alice = [first, second] ∧
      message ∈ control.execution.network.ledger ∧ message.id = (alice, 0) ∧
      (first.emitted = some message ∨
        (second.emitted = some message ∧ first.action.transmission = none)) := by
  obtain ⟨message, entry, material, present, identified, member, submitted, emitted, _, _⟩ :=
    alice_zero_receipt_origin control trace accepted
  have counted := (bob_raw_decision_resources control trace active).2.2.2.1
  obtain ⟨first, second, recalled⟩ := List.length_eq_two.mp counted
  rw [recalled] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  refine ⟨first, second, message, recalled, present, identified, ?_⟩
  rcases member with rfl | rfl
  · exact Or.inl emitted
  · refine Or.inr ⟨emitted, ?_⟩
    exact zero_recorded_prior_wait control trace [first] [] entry message material
      recalled submitted emitted identified first (by simp)

end Vegas.PrivateResolutionFork
