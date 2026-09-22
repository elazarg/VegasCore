/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventSubmissionOrigin
import Vegas.Pending.EventOpponentFrame

/-! # Protection of prescribed candidate slots

An accepted packet cannot consume the canonical candidate of another still
unfinished prescribed event. The packet may have been replayed by any player;
the proof uses its authenticated sender and canonical submission provenance.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

private theorem handled_event_completed (runtime : EventGraphRuntime graph)
    (before after : State graph) (message : Message Player (Payload graph))
    (accepted : handle runtime before message = some after)
    (event : graph.EventId) (address : message.payload.event? graph = some event) :
    event ∈ after.config.cut.completed := by
  obtain ⟨actual, actualAddress, ready, action, member⟩ :=
    handle_config_mem_step runtime before after message accepted
  have same := Option.some.inj (actualAddress.symm.trans address)
  subst actual
  rw [before.config.step_cut event ready action after.config member]
  exact Finset.mem_insert_self _ _

/-- An accepted packet leaves a still-unfinished prescribed event's canonical
candidate, acceptance cell, and non-aliasing property intact. -/
theorem handle_unfinished_canonical_resources (runtime : EventGraphRuntime graph)
    (before after : State graph) (message : Message Player (Payload graph))
    (owner : Player) (event : graph.EventId)
    (canonical : CanonicalCommitments owner message)
    (accepted : handle runtime before message = some after)
    (unfinished : event ∉ after.config.cut.completed) :
    after.candidates.lookup (owner, eventSlot event) =
        before.candidates.lookup (owner, eventSlot event) ∧
      after.accepted (.inr event) = before.accepted (.inr event) ∧
      (before.HandleUnused (owner, eventSlot event) →
        after.HandleUnused (owner, eventSlot event)) := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | opening target candidate raw =>
      have tables := handle_resolution_tables runtime before after
        ⟨id, .opening target candidate raw⟩ (by intros; simp) accepted
      rw [tables.1, tables.2]
      refine ⟨rfl, rfl, ?_⟩
      intro unused field retained
      apply unused field
      rwa [tables.1] at retained
  | withhold target =>
      have tables := handle_resolution_tables runtime before after
        ⟨id, .withhold target⟩ (by intros; simp) accepted
      rw [tables.1, tables.2]
      refine ⟨rfl, rfl, ?_⟩
      intro unused field retained
      apply unused field
      rwa [tables.1] at retained
  | commitment target candidate =>
      have completed := handled_event_completed runtime before after
        ⟨id, .commitment target candidate⟩ accepted target rfl
      have different : event ≠ target := fun same => unfinished (same ▸ completed)
      obtain ⟨candidates, handles, authored⟩ :=
        handle_commitment_tables runtime before after id target candidate accepted
      have distinct : (owner, eventSlot event) ≠ candidate := by
        intro same
        have sender : id.1 = owner := by
          exact authored.symm.trans (congrArg Prod.fst same).symm
        have canonicalHandle := (canonical sender target candidate rfl).1
        have slots : eventSlot event = eventSlot target :=
          congrArg Prod.snd (same.trans canonicalHandle)
        exact different (Fin.ext (Slot.prepared.inj slots))
      refine ⟨?_, ?_, ?_⟩
      · rw [candidates]
        exact before.candidates.lookup_freeze_other candidate (owner, eventSlot event) distinct
      · rw [handles]
        exact Function.update_of_ne (by simpa using different) _ _
      · intro unused field retained
        by_cases current : field = .inr target
        · subst field
          simp only [handles, Function.update_self] at retained
          exact distinct (Option.some.inj retained).symm
        · apply unused field
          simpa [handles, Function.update_of_ne current] using retained

end Vegas.EventGraphRuntime
