/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventApplication
import Interaction.MessageApplicationPolicies

/-! # Event-addressed reserved submission selection

The native event service selects the newest still-pending packet that is both
authored by the event owner and addressed to the requested event. Later
traffic for another event or author is ignored rather than consuming the
reserved inclusion opportunity.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

namespace Payload

/-- The public author and stable event address expected at one reserved
inclusion opportunity. -/
def Matches (event : graph.EventId) (owner : Player)
    (message : Message Player (Payload graph)) : Prop :=
  message.sender = owner ∧ message.payload.event? graph = some event

instance (event : graph.EventId) (owner : Player)
    (message : Message Player (Payload graph)) :
    Decidable (Matches event owner message) := by
  unfold Matches
  infer_instance

end Payload

/-- Select the rightmost element satisfying a decidable public predicate. -/
private def latestWhere? {α : Type} (predicate : α → Bool) : List α → Option α
  | [] => none
  | item :: rest =>
      match latestWhere? predicate rest with
      | some latest => some latest
      | none => if predicate item then some item else none

private theorem latestWhere?_some {α : Type} (predicate : α → Bool) :
    ∀ {items : List α} {selected : α},
      latestWhere? predicate items = some selected →
        selected ∈ items ∧ predicate selected = true := by
  intro items
  induction items with
  | nil => simp [latestWhere?]
  | cons item rest ih =>
      intro selected found
      simp only [latestWhere?] at found
      cases tail : latestWhere? predicate rest with
      | some latest =>
          simp only [tail] at found
          cases found
          obtain ⟨member, matching⟩ := ih tail
          exact ⟨List.mem_cons_of_mem item member, matching⟩
      | none =>
          simp only [tail] at found
          by_cases matching : predicate item = true
          · simp only [matching, ↓reduceIte, Option.some.injEq] at found
            subst selected
            exact ⟨List.mem_cons_self, matching⟩
          · have falseEq : predicate item = false := Bool.eq_false_of_not_eq_true matching
            simp [falseEq] at found

private theorem latestWhere?_append_matching {α : Type} (predicate : α → Bool)
    (items : List α) (item : α) (matching : predicate item = true) :
    latestWhere? predicate (items ++ [item]) = some item := by
  induction items with
  | nil => simp [latestWhere?, matching]
  | cons head tail ih => simp [latestWhere?, ih]

private theorem latestWhere?_exists_of_mem {α : Type} (predicate : α → Bool)
    (items : List α) (item : α) (member : item ∈ items) (matching : predicate item = true) :
    ∃ selected, latestWhere? predicate items = some selected := by
  induction items with
  | nil => contradiction
  | cons head tail ih =>
      cases found : latestWhere? predicate tail with
      | some selected => exact ⟨selected, by simp [latestWhere?, found]⟩
      | none =>
          rcases List.mem_cons.mp member with rfl | inTail
          · exact ⟨item, by simp [latestWhere?, found, matching]⟩
          · obtain ⟨selected, present⟩ := ih inTail
            rw [found] at present
            contradiction

private theorem latestWhere?_append_nonmatching {α : Type} (predicate : α → Bool)
    (items : List α) (item : α) (nonmatching : predicate item = false) :
    latestWhere? predicate (items ++ [item]) = latestWhere? predicate items := by
  induction items with
  | nil => simp [latestWhere?, nonmatching]
  | cons head tail ih => simp [latestWhere?, ih]

/-- The newest matching pending packet for one owner and stable event
address. -/
def latestEventSubmission? (pool : MessagePool Player (Payload graph))
    (event : graph.EventId) (owner : Player) :
    Option (Message Player (Payload graph)) :=
  latestWhere? (fun message => decide (Payload.Matches event owner message)) pool.pending

/-- A reserved event opportunity either includes the selected matching packet
or waits when no such packet is pending. -/
def latestEventSubmissionCommand (runtime : EventGraphRuntime graph)
    (event : graph.EventId) (owner : Player)
    (view : runtime.application.EnvironmentObservation) :
    runtime.application.EnvironmentPolicyCommand :=
  match latestEventSubmission? view.pool event owner with
  | some message => .include message.id
  | none => .wait

/-- Any matching pending envelope ensures that the reserved selector returns
a packet, even in the presence of unrelated or replayed traffic. -/
theorem latestEventSubmission?_exists (pool : MessagePool Player (Payload graph))
    (event : graph.EventId) (owner : Player)
    (message : Message Player (Payload graph)) (pending : message ∈ pool.pending)
    (matching : Payload.Matches event owner message) :
    ∃ selected, latestEventSubmission? pool event owner = some selected :=
  latestWhere?_exists_of_mem _ pool.pending message pending (decide_eq_true matching)

/-- Every selected envelope is pending and has the requested author and event
address. -/
theorem latestEventSubmission?_spec
    (pool : MessagePool Player (Payload graph))
    (event : graph.EventId) (owner : Player)
    (message : Message Player (Payload graph))
    (selected : latestEventSubmission? pool event owner = some message) :
    message ∈ pool.pending ∧ message.sender = owner ∧
      message.payload.event? graph = some event := by
  have found := latestWhere?_some
    (fun candidate => decide (Payload.Matches event owner candidate)) selected
  have matching : Payload.Matches event owner message := of_decide_eq_true found.2
  exact ⟨found.1, matching.1, matching.2⟩

/-- Appending a matching packet makes it the newest selected
submission. -/
theorem latestEventSubmission?_append_matching
    (pool : MessagePool Player (Payload graph))
    (event : graph.EventId) (owner : Player)
    (message : Message Player (Payload graph))
    (matching : Payload.Matches event owner message) :
    latestEventSubmission? { pool with pending := pool.pending ++ [message] }
      event owner = some message := by
  apply latestWhere?_append_matching
  exact decide_eq_true matching

/-- An unrelated later packet cannot consume or change the reserved event
selection. -/
theorem latestEventSubmission?_append_nonmatching
    (pool : MessagePool Player (Payload graph))
    (event : graph.EventId) (owner : Player)
    (message : Message Player (Payload graph))
    (unrelated : ¬ Payload.Matches event owner message) :
    latestEventSubmission? { pool with pending := pool.pending ++ [message] }
        event owner =
      latestEventSubmission? pool event owner := by
  apply latestWhere?_append_nonmatching
  exact decide_eq_false unrelated

/-- An inclusion command names an actually pending envelope with exactly the
requested public author and event address. -/
theorem latestEventSubmissionCommand_include
    (runtime : EventGraphRuntime graph) (event : graph.EventId) (owner : Player)
    (view : runtime.application.EnvironmentObservation)
    (id : MessageId Player)
    (command : runtime.latestEventSubmissionCommand event owner view = .include id) :
    ∃ message, message.id = id ∧ message ∈ view.pool.pending ∧
      message.sender = owner ∧ message.payload.event? graph = some event := by
  unfold latestEventSubmissionCommand at command
  cases selected : latestEventSubmission? view.pool event owner with
  | none => simp [selected] at command
  | some message =>
      simp only [selected, MessageInterface.EnvironmentPolicyCommand.include.injEq] at command
      subst id
      have spec := latestEventSubmission?_spec view.pool event owner message selected
      exact ⟨message, rfl, spec.1, spec.2.1, spec.2.2⟩

end Vegas.EventGraphRuntime
