/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePolicyFacts

/-! # Original resolution intentions in complete response recall

A matching silent sampled intention can be recovered from an arbitrary recall,
not only a singleton response. Event-unique private memories prevent a competing
intention from changing which original action is recovered. This is a local
observation adapter; service-wide memory alignment is a separate invariant.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private theorem filterMap_head_of_unique {α β : Type} (select : α → Option β)
    (entries : List α) (value : β)
    (present : ∃ entry ∈ entries, select entry = some value)
    (unique : ∀ entry ∈ entries, ∀ selected, select entry = some selected → selected = value) :
    (entries.filterMap select).head? = some value := by
  induction entries with
  | nil => simp at present
  | cons entry rest ih =>
      cases selected : select entry with
      | some head =>
          have same := unique entry (by simp) head selected
          simp [selected, same]
      | none =>
          simp only [List.filterMap_cons, selected]
          apply ih
          · obtain ⟨witness, member, chosen⟩ := present
            rcases List.mem_cons.mp member with same | later
            · subst witness
              rw [selected] at chosen
              cases chosen
            · exact ⟨witness, later, chosen⟩
          · intro witness member head chosen
            exact unique witness (List.mem_cons_of_mem _ member) head chosen

/-- Original-action recall preserves every physical completion's event identity,
independently of service success or supported internal memory. -/
theorem reactiveOriginal_event {graph : EventGraph Player L}
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion)) (receipts : List (MessageId Player × Bool))
    (completion : graph.Completion) :
    (runtime.reactiveOriginal leaks who history intentions receipts completion).event =
      completion.event := by
  classical
  cases node : nodeView graph completion.event with
  | sample => simp only [reactiveOriginal, node]
  | bind => simp only [reactiveOriginal, node]
  | resolve =>
      let select := fun (pair : (runtime.reactiveApplication leaks).PlayerEntry ×
          Option graph.Completion) => do
        let remembered ← pair.2
        if remembered.event = completion.event ∧
            runtime.ReactiveSilentDecision leaks who pair.1 remembered then some remembered
        else do
          let message ← pair.1.emitted
          if remembered.event = completion.event ∧
              message.payload.call.event? graph = some completion.event ∧
              (message.id, true) ∈ receipts ∧
              pair.1.action = runtime.reactiveDecision leaks who remembered.event
                remembered.action pair.1.beforeView.application then some remembered
          else none
      let candidates := (history.zip intentions).filterMap select
      have sameEvent : ∀ remembered ∈ candidates, remembered.event = completion.event := by
        intro remembered member
        obtain ⟨⟨entry, saved⟩, _, selected⟩ := List.mem_filterMap.mp member
        cases saved with
        | none => simp [select] at selected
        | some intention =>
            simp only [select, Option.bind_eq_bind, Option.bind_some] at selected
            split at selected
            · rename_i authentic
              cases Option.some.inj selected
              exact authentic.1
            · cases emitted : entry.emitted with
              | none => simp [emitted] at selected
              | some message =>
                  simp only [emitted, Option.bind_some] at selected
                  split at selected
                  · rename_i accepted
                    cases Option.some.inj selected
                    exact accepted.1
                  · cases selected
      simp only [reactiveOriginal, node]
      change (candidates.head?.getD completion).event = completion.event
      cases selected : candidates.head? with
      | none => rfl
      | some remembered =>
          exact sameEvent remembered (List.mem_of_mem_head? (by simp [selected]))

/-- Complete response recall restores a genuine silent resolution intention.
Uniqueness is about the event-labelled private memory, rather than a desired
observation or continuation-law equality. -/
theorem reactiveOriginal_silent_of_unique_memory (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion)) (receipts : List (MessageId Player × Bool))
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (remembered completion : graph.Completion)
    (retained : (entry, some remembered) ∈ history.zip intentions)
    (matching : runtime.ReactiveSilentDecision leaks who entry remembered)
    (sameEvent : remembered.event = completion.event)
    (unique : ∀ other ∈ intentions, ∀ saved, other = some saved →
      saved.event = completion.event → saved = remembered)
    (resolution : (match nodeView graph completion.event with
      | .resolve .. => true | .sample .. | .bind .. => false) = true) :
    runtime.reactiveOriginal leaks who history intentions receipts completion = remembered := by
  classical
  cases node : nodeView graph completion.event with
  | sample => simp [node] at resolution
  | bind => simp [node] at resolution
  | resolve =>
      let select := fun (pair : (runtime.reactiveApplication leaks).PlayerEntry ×
          Option graph.Completion) => do
        let saved ← pair.2
        if saved.event = completion.event ∧
            runtime.ReactiveSilentDecision leaks who pair.1 saved then some saved
        else do
          let message ← pair.1.emitted
          if saved.event = completion.event ∧
              message.payload.call.event? graph = some completion.event ∧
              (message.id, true) ∈ receipts ∧
              pair.1.action = runtime.reactiveDecision leaks who saved.event
                saved.action pair.1.beforeView.application then some saved
          else none
      have found : ((history.zip intentions).filterMap select).head? = some remembered := by
        apply filterMap_head_of_unique
        · exact ⟨(entry, some remembered), retained, by simp [select, sameEvent, matching]⟩
        · rintro ⟨record, saved⟩ member selected chosen
          have inMemory := (List.of_mem_zip member).2
          cases saved with
          | none => simp [select] at chosen
          | some intention =>
              simp only [select, Option.bind_eq_bind, Option.bind_some] at chosen
              split at chosen
              · rename_i validated
                have same := Option.some.inj chosen
                subst selected
                exact unique (some intention) inMemory intention rfl validated.1
              · cases emitted : record.emitted with
                | none => simp [emitted] at chosen
                | some message =>
                    simp only [emitted, Option.bind_some] at chosen
                    split at chosen
                    · rename_i accepted
                      have same := Option.some.inj chosen
                      subst selected
                      exact unique (some intention) inMemory intention rfl accepted.1
                    · cases chosen
      simp only [reactiveOriginal, node]
      change (((history.zip intentions).filterMap select).head?).getD completion = remembered
      rw [found]
      rfl

/-- The same arbitrary-history restoration is grounded in an actual supported
prescribed response, rather than assuming that an internal intention is genuine. -/
theorem reactiveOriginal_silent_of_prescribed_support (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (beforeHistory history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (beforeIntentions intentions : List (Option graph.Completion))
    (receipts : List (MessageId Player × Bool))
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (action : (runtime.reactiveApplication leaks).Action)
    (remembered completion : graph.Completion)
    (supported : (action, some remembered) ∈
      (runtime.prescribedReactiveResponse leaks who policy beforeHistory beforeIntentions
        view).support)
    (silent : action.transmission = none)
    (retained : (⟨view, action, none⟩, some remembered) ∈ history.zip intentions)
    (sameEvent : remembered.event = completion.event)
    (unique : ∀ other ∈ intentions, ∀ saved, other = some saved →
      saved.event = completion.event → saved = remembered)
    (resolution : (match nodeView graph completion.event with
      | .resolve .. => true | .sample .. | .bind .. => false) = true) :
    runtime.reactiveOriginal leaks who history intentions receipts completion = remembered := by
  apply runtime.reactiveOriginal_silent_of_unique_memory leaks who history intentions receipts
    ⟨view, action, none⟩ remembered completion retained _ sameEvent unique resolution
  exact runtime.reactiveSilentDecision_of_prescribed_support leaks who policy beforeHistory
    beforeIntentions view action remembered supported silent _ rfl

end Vegas.EventGraphRuntime
