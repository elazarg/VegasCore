/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveNormalization
import Interaction.ReactiveRecall

/-! # A fresh submission is made at most once per event

The test reads only the player's existing response recall and the unique event
identifier. It requires no phase counter, timing oracle, or memory cost.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Only a new submitted event call records an event; certificate representation
and private submission material do not enter the test. -/
def submittedEvent? (response : (runtime.reactiveApplication leaks).Action) :
    Option graph.EventId :=
  match response.transmission with
  | some material =>
      material.call.packet.event? graph
  | none => none

open Classical in
def eventRecorded (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (event : graph.EventId) : Bool :=
  past.any fun entry => decide (runtime.submittedEvent? leaks entry.action = some event)

/-- The submitted event identities already present in the player's own recall. -/
def submissionRecall (past : List (runtime.reactiveApplication leaks).PlayerEntry) :
    List (Option graph.EventId) :=
  past.map fun entry => runtime.submittedEvent? leaks entry.action

theorem eventRecorded_congr
    (left right : List (runtime.reactiveApplication leaks).PlayerEntry)
    (same : runtime.submissionRecall leaks left = runtime.submissionRecall leaks right)
    (event : graph.EventId) :
    runtime.eventRecorded leaks left event = runtime.eventRecorded leaks right event := by
  classical
  have observed := congrArg (fun records : List (Option graph.EventId) =>
    records.any fun selected => decide (selected = some event)) same
  simpa only [submissionRecall, eventRecorded, List.any_map, Function.comp_def] using observed

theorem submissionRecall_respond
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action) :
    runtime.submissionRecall leaks
      ((execution.respond (runtime.reactiveApplication leaks) who response).recall who) =
      runtime.submissionRecall leaks (execution.recall who) ++
        [runtime.submittedEvent? leaks response] := by
  simp only [submissionRecall, ReactiveApplication.Execution.respond, ↓reduceIte, List.map_append,
    List.map_cons, List.map_nil]

/-- A fresh event call is allowed only before the first submitted call naming
the same event. Every other response is unaffected by this discipline. -/
def firstSubmission (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (response : (runtime.reactiveApplication leaks).Action) : Bool :=
  match runtime.submittedEvent? leaks response with
  | none => true
  | some event => !(runtime.eventRecorded leaks past event)

/-- Semantic normalization changes no submitted event identity. Private evidence
requests and inert material do not create additional transmission choices. -/
theorem submittedEvent_normalization (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action) :
    runtime.submittedEvent? leaks ((runtime.reactiveNormalization leaks).action
      who past view response) = runtime.submittedEvent? leaks response := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material => rfl

theorem firstSubmission_normalization (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action) :
    runtime.firstSubmission leaks past ((runtime.reactiveNormalization leaks).action
      who past view response) = runtime.firstSubmission leaks past response := by
  simp only [firstSubmission, runtime.submittedEvent_normalization]

theorem eventRecorded_iff (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (event : graph.EventId) :
    runtime.eventRecorded leaks past event = true ↔
      ∃ entry ∈ past, runtime.submittedEvent? leaks entry.action = some event := by
  classical
  simp only [eventRecorded, List.any_eq_true, decide_eq_true_eq]

/-- The actual native response records the submitted event immediately,
independently of later inclusion or rejection. -/
theorem eventRecorded_respond
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action) (event : graph.EventId)
    (submitted : runtime.submittedEvent? leaks response = some event) :
    runtime.eventRecorded leaks
      ((execution.respond (runtime.reactiveApplication leaks) who response).recall who) event =
        true := by
  apply (runtime.eventRecorded_iff leaks _ event).mpr
  simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
  exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), submitted⟩

/-- Any later own recall containing the actual previous submission rejects a
second fresh call of the event. -/
theorem firstSubmission_false_of_recorded
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (event : graph.EventId) (recorded : runtime.eventRecorded leaks past event = true)
    (response : (runtime.reactiveApplication leaks).Action)
    (submitted : runtime.submittedEvent? leaks response = some event) :
    runtime.firstSubmission leaks past response = false := by
  simp only [firstSubmission, submitted, recorded, Bool.not_true]

/-- The discipline persists when any player takes another native response. -/
theorem eventRecorded_respond_of_recorded
    (execution : (runtime.reactiveApplication leaks).Execution) (who observer : Player)
    (response : (runtime.reactiveApplication leaks).Action) (event : graph.EventId)
    (recorded : runtime.eventRecorded leaks (execution.recall observer) event = true) :
    runtime.eventRecorded leaks
      ((execution.respond (runtime.reactiveApplication leaks) who response).recall observer)
        event = true := by
  obtain ⟨entry, member, submitted⟩ := (runtime.eventRecorded_iff leaks _ event).mp recorded
  apply (runtime.eventRecorded_iff leaks _ event).mpr
  exact ⟨entry, (runtime.reactiveApplication leaks).respond_recall_mono execution who observer
    response member, submitted⟩

/-- A response which does not submit this event leaves its recorded status
unchanged. Foreign responses also leave the observer's own record unchanged. -/
theorem eventRecorded_respond_other
    (execution : (runtime.reactiveApplication leaks).Execution) (who observer : Player)
    (response : (runtime.reactiveApplication leaks).Action) (event : graph.EventId)
    (other : who = observer → runtime.submittedEvent? leaks response ≠ some event) :
    runtime.eventRecorded leaks
      ((execution.respond (runtime.reactiveApplication leaks) who response).recall observer)
        event = runtime.eventRecorded leaks (execution.recall observer) event := by
  classical
  by_cases same : observer = who
  · subst observer
    simp only [eventRecorded, ReactiveApplication.Execution.respond, ↓reduceIte,
      List.any_append, List.any_cons, List.any_nil, other rfl, decide_false,
      Bool.or_false]
  · simp only [ReactiveApplication.Execution.respond, ite_eq_right same]

end Vegas.EventGraphRuntime
