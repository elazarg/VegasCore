/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveSubmissionRecall
import Interaction.ReactiveSubmissionSerial

/-! # Public serial evidence for a first event submission

A clean phase starts with all earlier fresh envelopes settled. Until its
reserved inclusion, an author's new submissions name only the current event.
The next serial therefore equals the public ledger count precisely before
that event's first submission. The evidence requires no earlier pending packet
in the auditor's sample and never treats a missing sample as an omitted move.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem eventRecorded_append
    (first second : List (runtime.reactiveApplication leaks).PlayerEntry)
    (event : graph.EventId) :
    runtime.eventRecorded leaks (first ++ second) event =
      (runtime.eventRecorded leaks first event || runtime.eventRecorded leaks second event) := by
  simp only [eventRecorded, List.any_append]

/-- Within a single-event response phase, remembering its submission is exactly
remembering at least one freshly allocated envelope. -/
theorem eventRecorded_false_iff_no_submission
    (past : List (runtime.reactiveApplication leaks).PlayerEntry) (event : graph.EventId)
    (onlyCurrent : ∀ entry ∈ past,
      entry.action.isSubmission (runtime.reactiveApplication leaks) = true →
        runtime.submittedEvent? leaks entry.action = some event) :
    runtime.eventRecorded leaks past event = false ↔
      (runtime.reactiveApplication leaks).submissionCount past = 0 := by
  classical
  have flags (entry : (runtime.reactiveApplication leaks).PlayerEntry) (member : entry ∈ past) :
      decide (runtime.submittedEvent? leaks entry.action = some event) =
        entry.action.isSubmission (runtime.reactiveApplication leaks) := by
    rcases entry with ⟨view, ⟨transmission⟩, emitted⟩
    cases transmission with
    | none => rfl
    | some transmission =>
        cases transmission with
        | replay id => rfl
        | submit submission =>
            have selected := onlyCurrent _ member rfl
            simp only [selected, decide_true]
            rfl
  simp only [eventRecorded, List.any_eq_false,
    ReactiveApplication.submissionCount, List.countP_eq_zero]
  constructor
  · intro absent entry member
    rw [← flags entry member]
    exact absent entry member
  · intro absent entry member
    rw [flags entry member]
    exact absent entry member

/-- The public serial check is the private first-submission test at a clean
single-event window. Replays and arbitrary private observation remain legal. -/
theorem first_event_iff_public_serial
    (before after : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (event : graph.EventId)
    (beforeRecall : before.SerialRecall (runtime.reactiveApplication leaks))
    (afterRecall : after.SerialRecall (runtime.reactiveApplication leaks))
    (settled : before.network.nextSerial who =
      before.network.ledger.countP (fun message => message.sender = who))
    (ledger : after.network.ledger = before.network.ledger)
    (unsent : runtime.eventRecorded leaks (before.recall who) event = false)
    (suffix : List (runtime.reactiveApplication leaks).PlayerEntry)
    (recalled : after.recall who = before.recall who ++ suffix)
    (onlyCurrent : ∀ entry ∈ suffix,
      entry.action.isSubmission (runtime.reactiveApplication leaks) = true →
        runtime.submittedEvent? leaks entry.action = some event) :
    runtime.eventRecorded leaks (after.recall who) event = false ↔
      after.network.nextSerial who =
        after.network.ledger.countP (fun message => message.sender = who) := by
  rw [recalled, runtime.eventRecorded_append, unsent, Bool.false_or,
    runtime.eventRecorded_false_iff_no_submission leaks suffix event onlyCurrent]
  exact ((runtime.reactiveApplication leaks).serial_eq_ledger_iff_no_submission
    before after who beforeRecall afterRecall settled ledger suffix recalled).symm

/-- An unchanged public serial at a settled phase proves that no fresh
submission has occurred, regardless of which events new messages could name.
In particular, every previously unsent event remains unsent. -/
theorem eventRecorded_false_of_public_serial
    (before after : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (event : graph.EventId)
    (beforeRecall : before.SerialRecall (runtime.reactiveApplication leaks))
    (afterRecall : after.SerialRecall (runtime.reactiveApplication leaks))
    (settled : before.network.nextSerial who =
      before.network.ledger.countP (fun message => message.sender = who))
    (ledger : after.network.ledger = before.network.ledger)
    (unsent : runtime.eventRecorded leaks (before.recall who) event = false)
    (suffix : List (runtime.reactiveApplication leaks).PlayerEntry)
    (recalled : after.recall who = before.recall who ++ suffix)
    (clean : after.network.nextSerial who =
      after.network.ledger.countP (fun message => message.sender = who)) :
    runtime.eventRecorded leaks (after.recall who) event = false := by
  have zero := ((runtime.reactiveApplication leaks).serial_eq_ledger_iff_no_submission
    before after who beforeRecall afterRecall settled ledger suffix recalled).mp clean
  apply (runtime.first_event_iff_public_serial leaks before after who event beforeRecall
    afterRecall settled ledger unsent suffix recalled ?_).mpr clean
  intro entry member fresh
  have absent := (List.countP_eq_zero.mp zero) entry member
  rw [fresh] at absent
  exact (absent rfl).elim

/-- Waiting and replay preserve the clean serial test. A fresh submission for
the owner and current event makes its unsent premise false. Thus the test
propagates through a complete retained window without assuming an empty pool. -/
theorem event_accounted_response
    (execution : (runtime.reactiveApplication leaks).Execution) (who owner : Player)
    (event : graph.EventId) (response : (runtime.reactiveApplication leaks).Action)
    (counted : runtime.eventRecorded leaks (execution.recall owner) event = false →
      execution.network.nextSerial owner =
        execution.network.ledger.countP (fun message => message.sender = owner))
    (shape : (response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩) ∨
      (who = owner ∧ runtime.submittedEvent? leaks response = some event)) :
    let next := execution.respond (runtime.reactiveApplication leaks) who response
    runtime.eventRecorded leaks (next.recall owner) event = false →
      next.network.nextSerial owner =
        next.network.ledger.countP (fun message => message.sender = owner) := by
  intro next unsent
  rcases shape with (rfl | ⟨id, rfl⟩) | ⟨rfl, submitted⟩
  · have previous := runtime.eventRecorded_respond_other leaks execution who owner ⟨none⟩ event
      (fun _ impossible => by cases impossible)
    have account := counted (previous ▸ unsent)
    exact account
  · have previous := runtime.eventRecorded_respond_other leaks execution who owner
      ⟨some (.replay id)⟩ event (fun _ impossible => by cases impossible)
    have account := counted (previous ▸ unsent)
    cases found : (execution.network.known who).find? (fun message => message.id = id) <;>
      simpa only [next, ReactiveApplication.Execution.respond, MessageNetwork.replay, found]
        using account
  · have sent := runtime.eventRecorded_respond leaks execution who response event submitted
    rw [show runtime.eventRecorded leaks (next.recall who) event = true from sent] at unsent
    cases unsent

end Vegas.EventGraphRuntime
