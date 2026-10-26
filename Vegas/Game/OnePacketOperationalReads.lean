/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketBindingSilence

/-! # Reading own submissions from emitted envelopes

Along every history of the supplied runtime, a recall entry emitted a packet
exactly when it transmitted (`Vegas.history_emitted_isSome`). So a player's own
emitted envelopes determine its number of submissions
(`Vegas.history_outputs_length`), the events it has submitted for
(`Vegas.history_eventRecorded_iff`), the prepared slots it has committed to
(`Vegas.history_slotCommitted_iff`), and, with its number of completed
bindings, its canonical slot (`Vegas.history_canonicalFreshSlot`). These are
operational data: none of them reads a stored value or a candidate.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}
  {control : (application setup runtime leaks).Control}

omit [DecidableEq Player] in
/-- The public canonical slot depends on the traffic only through its committed
slots. -/
theorem publicFreshSlot_congr {graph : EventGraph Player L}
    {left right : List (Message Player (WitnessedPacket graph))} {who : Player}
    (same : ∀ serial, SlotCommitted left who serial ↔ SlotCommitted right who serial)
    (count : Nat) : publicFreshSlot left who count = publicFreshSlot right who count := by
  have committed : SlotCommitted left who = SlotCommitted right who :=
    funext fun serial => propext (same serial)
  unfold publicFreshSlot
  rw [committed]

/-- **Emission is transmission.** Along every history of the supplied runtime, a
recall entry emitted a packet exactly when it transmitted. -/
theorem history_emitted_isSome
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) (entry : (application setup runtime leaks).PlayerEntry)
    (member : entry ∈ control.execution.recall who) :
    entry.emitted.isSome = entry.action.transmission.isSome := by
  have emitted := (transmissionsEmitted_serviceInvariant (runtime := runtime) scheduler).history
    (initialLaw setup)
    horizon (fun _ _ _ _ member => (List.not_mem_nil member).elim) trace
  have signed := signedCommitments_history runtime leaks (initialLaw setup)
    (serviceInitialLaw_initialized setup) horizon scheduler trace
  cases transmits : entry.action.transmission with
  | none =>
      cases emits : entry.emitted with
      | none => rfl
      | some message =>
          obtain ⟨_, material, sends, _⟩ := signed.emissions who entry member message emits
          rw [transmits] at sends
          cases sends
  | some material =>
      obtain ⟨message, emits, _⟩ := emitted who entry member material transmits
      rw [emits]
      rfl

/-- Along every history of the supplied runtime, a player's emitted envelopes
number its submissions. -/
theorem history_outputs_length
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) :
    ((application setup runtime leaks).outputs (control.execution.recall who)).length =
      (application setup runtime leaks).submissionCount (control.execution.recall who) := by
  unfold ReactiveApplication.outputs ReactiveApplication.submissionCount
  rw [List.length_filterMap_eq_countP]
  apply List.countP_congr
  intro entry member
  rw [history_emitted_isSome (runtime := runtime) trace who entry member]
  unfold ReactiveApplication.Action.isSubmission
  cases entry.action.transmission <;> simp

/-- Along every history of the supplied runtime, a player's recall has submitted
for an event exactly when one of its emitted envelopes names it. -/
theorem history_eventRecorded_iff
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) (event : (graph setup).EventId) :
    runtime.eventRecorded leaks (control.execution.recall who) event = true ↔
      ∃ message ∈ (application setup runtime leaks).outputs (control.execution.recall who),
        message.payload.call.event? (graph setup) = some event := by
  have emitted := (transmissionsEmitted_serviceInvariant (runtime := runtime) scheduler).history
    (initialLaw setup)
    horizon (fun _ _ _ _ member => (List.not_mem_nil member).elim) trace
  have signed := signedCommitments_history runtime leaks (initialLaw setup)
    (serviceInitialLaw_initialized setup) horizon scheduler trace
  constructor
  · intro recorded
    obtain ⟨entry, entryMember, submitted⟩ := List.any_eq_true.mp recorded
    have submittedEq := of_decide_eq_true submitted
    unfold EventGraphRuntime.submittedEvent? at submittedEq
    cases transmits : entry.action.transmission with
    | none =>
        rw [transmits] at submittedEq
        cases submittedEq
    | some material =>
        rw [transmits] at submittedEq
        dsimp only at submittedEq
        obtain ⟨message, emits, call⟩ := emitted who entry entryMember material transmits
        refine ⟨message, List.mem_filterMap.mpr ⟨entry, entryMember, emits⟩, ?_⟩
        rw [call]
        exact submittedEq
  · rintro ⟨message, output, named⟩
    obtain ⟨entry, entryMember, emits⟩ := List.mem_filterMap.mp output
    obtain ⟨_, material, sends, call⟩ := signed.emissions who entry entryMember message emits
    refine List.any_eq_true.mpr ⟨entry, entryMember, decide_eq_true ?_⟩
    unfold EventGraphRuntime.submittedEvent?
    rw [sends]
    change material.call.packet.event? (graph setup) = some event
    rw [← call]
    exact named

/-- Along every history of the supplied runtime, a player has committed to a
prepared slot exactly when one of its emitted envelopes commits to it. -/
theorem history_slotCommitted_iff
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) (serial : Nat) :
    SlotCommitted control.execution.network.inputs who serial ↔
      SlotCommitted ((application setup runtime leaks).outputs (control.execution.recall who)) who
        serial := by
  have recalled := runtime.countRecall_history leaks trace
  rw [← recalled.1 who]
  constructor
  · rintro ⟨message, input, sender, committed⟩
    exact ⟨message, List.mem_filter.mpr ⟨input, by simp [sender]⟩, sender, committed⟩
  · rintro ⟨message, output, sender, committed⟩
    exact ⟨message, (List.mem_filter.mp output).1, sender, committed⟩

/-- **The canonical slot is operational.** Along every history of the default
runtime, a player's canonical slot is read from its emitted envelopes and its
number of completed bindings. -/
theorem history_canonicalFreshSlot
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) :
    canonicalFreshSlot who (control.execution.observe (application setup runtime leaks)
      who).application =
      publicFreshSlot ((application setup runtime leaks).outputs (control.execution.recall who)) who
        (control.execution.application.publicView.bindingCount who) := by
  change canonicalFreshSlot who (control.execution.application.playerView who) = _
  rw [canonicalFreshSlot_eq_publicFreshSlot (preparedFresh_history (runtime := runtime) horizon
    scheduler trace)]
  exact publicFreshSlot_congr (history_slotCommitted_iff (runtime := runtime) trace who) _

end Vegas
