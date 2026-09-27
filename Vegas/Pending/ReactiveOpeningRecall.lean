/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveNormalization
import Interaction.ReactiveRecall

/-! # A fresh opening is submitted at most once per event

The test reads only the player's existing response recall and the unique event
identifier. It requires no phase counter, timing oracle, or memory cost. Replays
are distinct responses and do not count as a new opening submission.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Only a new submitted opening records an event; certificate representation
and private submission material do not enter the test. -/
def submittedOpening? (response : (runtime.reactiveApplication leaks).Action) :
    Option graph.EventId :=
  match response.transmission with
  | some (.submit material) =>
      match material.call.packet with
      | .opening event _ _ => some event
      | .commitment .. | .withhold .. | .malformed .. => none
  | none | some (.replay _) => none

open Classical in
def openingRecorded (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (event : graph.EventId) : Bool :=
  past.any fun entry => decide (runtime.submittedOpening? leaks entry.action = some event)

/-- The submitted event identities already present in the player's own recall. -/
def openingRecall (past : List (runtime.reactiveApplication leaks).PlayerEntry) :
    List (Option graph.EventId) :=
  past.map fun entry => runtime.submittedOpening? leaks entry.action

theorem openingRecorded_congr
    (left right : List (runtime.reactiveApplication leaks).PlayerEntry)
    (same : runtime.openingRecall leaks left = runtime.openingRecall leaks right)
    (event : graph.EventId) :
    runtime.openingRecorded leaks left event = runtime.openingRecorded leaks right event := by
  classical
  have observed := congrArg (fun records : List (Option graph.EventId) =>
    records.any fun selected => decide (selected = some event)) same
  simpa only [openingRecall, openingRecorded, List.any_map, Function.comp_def] using observed

theorem openingRecall_respond
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action) :
    runtime.openingRecall leaks
      ((execution.respond (runtime.reactiveApplication leaks) who response).recall who) =
      runtime.openingRecall leaks (execution.recall who) ++
        [runtime.submittedOpening? leaks response] := by
  simp only [openingRecall, ReactiveApplication.Execution.respond, ↓reduceIte, List.map_append,
    List.map_cons, List.map_nil]

/-- A fresh opening is allowed only before the first submitted opening naming
the same event. Every other response is unaffected by this discipline. -/
def firstOpening (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (response : (runtime.reactiveApplication leaks).Action) : Bool :=
  match runtime.submittedOpening? leaks response with
  | none => true
  | some event => !(runtime.openingRecorded leaks past event)

/-- Semantic normalization changes no opening event identity. Private evidence
requests and inert material do not create additional transmission choices. -/
theorem submittedOpening_normalization (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action) :
    runtime.submittedOpening? leaks ((runtime.reactiveNormalization leaks).action
      who past view response) = runtime.submittedOpening? leaks response := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit material => rfl
      | replay id =>
          simp only [ReactiveApplication.SubmissionNormalization.action]
          split <;> rfl

theorem firstOpening_normalization (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action) :
    runtime.firstOpening leaks past ((runtime.reactiveNormalization leaks).action
      who past view response) = runtime.firstOpening leaks past response := by
  simp only [firstOpening, runtime.submittedOpening_normalization]

theorem openingRecorded_iff (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (event : graph.EventId) :
    runtime.openingRecorded leaks past event = true ↔
      ∃ entry ∈ past, runtime.submittedOpening? leaks entry.action = some event := by
  classical
  simp only [openingRecorded, List.any_eq_true, decide_eq_true_eq]

/-- The actual native response records the submitted event immediately,
independently of later inclusion or rejection. -/
theorem openingRecorded_respond
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action) (event : graph.EventId)
    (submitted : runtime.submittedOpening? leaks response = some event) :
    runtime.openingRecorded leaks
      ((execution.respond (runtime.reactiveApplication leaks) who response).recall who) event =
        true := by
  apply (runtime.openingRecorded_iff leaks _ event).mpr
  simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
  exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), submitted⟩

/-- Any later own recall containing the actual previous submission rejects a
second fresh opening of the event. Publicly observable retransmission by replay
is not silently identified with another fresh signed envelope. -/
theorem firstOpening_false_of_recorded
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (event : graph.EventId) (recorded : runtime.openingRecorded leaks past event = true)
    (response : (runtime.reactiveApplication leaks).Action)
    (submitted : runtime.submittedOpening? leaks response = some event) :
    runtime.firstOpening leaks past response = false := by
  simp only [firstOpening, submitted, recorded, Bool.not_true]

/-- The discipline persists when any player takes another native response. -/
theorem openingRecorded_respond_of_recorded
    (execution : (runtime.reactiveApplication leaks).Execution) (who observer : Player)
    (response : (runtime.reactiveApplication leaks).Action) (event : graph.EventId)
    (recorded : runtime.openingRecorded leaks (execution.recall observer) event = true) :
    runtime.openingRecorded leaks
      ((execution.respond (runtime.reactiveApplication leaks) who response).recall observer)
        event = true := by
  obtain ⟨entry, member, submitted⟩ := (runtime.openingRecorded_iff leaks _ event).mp recorded
  apply (runtime.openingRecorded_iff leaks _ event).mpr
  exact ⟨entry, (runtime.reactiveApplication leaks).respond_recall_mono execution who observer
    response member, submitted⟩

end Vegas.EventGraphRuntime
