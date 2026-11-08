/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveNormalization

/-! # A fresh submission is made at most once per event

The test reads only the player's existing response recall and the unique event
identifier. It requires no phase counter, timing oracle, or memory cost.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Only a new submitted event call records an event; certificate representation
and private submission material do not enter the test. -/
def submittedEvent? (response : ((reactiveApplication timeouts) leaks).Action) :
    Option graph.EventId :=
  match response.transmission with
  | some material =>
      material.call.packet.event? graph
  | none => none

open Classical in
def eventRecorded (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (event : graph.EventId) : Bool :=
  past.any fun entry => decide ((submittedEvent? timeouts) leaks entry.action = some event)

/-- The submitted event identities already present in the player's own recall. -/
def submissionRecall (past : List ((reactiveApplication timeouts) leaks).PlayerEntry) :
    List (Option graph.EventId) :=
  past.map fun entry => (submittedEvent? timeouts) leaks entry.action

theorem eventRecorded_congr
    (left right : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (same : (submissionRecall timeouts) leaks left = (submissionRecall timeouts) leaks right)
    (event : graph.EventId) :
    (eventRecorded timeouts) leaks left event = (eventRecorded timeouts) leaks right event := by
  classical
  have observed := congrArg (fun records : List (Option graph.EventId) =>
    records.any fun selected => decide (selected = some event)) same
  simpa only [submissionRecall, eventRecorded, List.any_map, Function.comp_def] using observed

theorem submissionRecall_respond
    (execution : ((reactiveApplication timeouts) leaks).Execution) (who : Player)
    (response : ((reactiveApplication timeouts) leaks).Action) :
    (submissionRecall timeouts) leaks
      ((execution.respond ((reactiveApplication timeouts) leaks) who response).logs who) =
      (submissionRecall timeouts) leaks (execution.logs who) ++
        [(submittedEvent? timeouts) leaks response] := by
  simp only [submissionRecall, ReactiveApplication.Execution.respond, ↓reduceIte, List.map_append,
    List.map_cons, List.map_nil]

/-- A fresh event call is allowed only before the first submitted call naming
the same event. Every other response is unaffected by this discipline. -/
def firstSubmission (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (response : ((reactiveApplication timeouts) leaks).Action) : Bool :=
  match (submittedEvent? timeouts) leaks response with
  | none => true
  | some event => !((eventRecorded timeouts) leaks past event)

/-- Semantic normalization changes no submitted event identity. Private evidence
requests and inert material do not create additional transmission choices. -/
theorem submittedEvent_normalization (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (response : ((reactiveApplication timeouts) leaks).Action) :
    (submittedEvent? timeouts) leaks (((reactiveNormalization timeouts) leaks).action
      who past view response) = (submittedEvent? timeouts) leaks response := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material => rfl

theorem eventRecorded_iff (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (event : graph.EventId) :
    (eventRecorded timeouts) leaks past event = true ↔
      ∃ entry ∈ past, (submittedEvent? timeouts) leaks entry.action = some event := by
  classical
  simp only [eventRecorded, List.any_eq_true, decide_eq_true_eq]

/-- The actual native response records the submitted event immediately,
independently of later inclusion or rejection. -/
theorem eventRecorded_respond
    (execution : ((reactiveApplication timeouts) leaks).Execution) (who : Player)
    (response : ((reactiveApplication timeouts) leaks).Action) (event : graph.EventId)
    (submitted : (submittedEvent? timeouts) leaks response = some event) :
    (eventRecorded timeouts) leaks
      ((execution.respond ((reactiveApplication timeouts) leaks) who response).logs who) event =
        true := by
  apply ((eventRecorded_iff timeouts) leaks _ event).mpr
  simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
  exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), submitted⟩

/-- The discipline persists when any player takes another native response. -/
theorem eventRecorded_respond_of_recorded
    (execution : ((reactiveApplication timeouts) leaks).Execution) (who observer : Player)
    (response : ((reactiveApplication timeouts) leaks).Action) (event : graph.EventId)
    (recorded : (eventRecorded timeouts) leaks (execution.logs observer) event = true) :
    (eventRecorded timeouts) leaks
      ((execution.respond ((reactiveApplication timeouts) leaks) who response).logs observer)
        event = true := by
  obtain ⟨entry, member, submitted⟩ := ((eventRecorded_iff timeouts) leaks _ event).mp recorded
  apply ((eventRecorded_iff timeouts) leaks _ event).mpr
  exact ⟨entry, ((reactiveApplication timeouts) leaks).respond_recall_mono execution who observer
    response member, submitted⟩

end Vegas.EventGraphRuntime
