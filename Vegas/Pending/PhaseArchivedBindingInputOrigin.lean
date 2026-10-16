/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingStampHistory
import Vegas.Pending.PhaseBindingFreshness
import Vegas.Pending.PhaseAttemptCheckpoint
import Vegas.Pending.PhaseArchivedBindings
import Vegas.Pending.PhaseRetiredCompletion
import Vegas.Pending.PhaseCountUniqueness

/-! # Original recorded commitment handles in actual archived attempts -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

/-- A surviving owner's completed archived binding accepts the exact handle of
its original remembered SEND in that attempt. Actual archive stamps and FIRST
identify the envelope; no clear endpoint, accepting receipt or source-origin
interpretation is assumed. -/
theorem archived_recorded_binding_accepted
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (record : RetiredCommitAttempt graph) (retired : record ∈ control.execution.application.retired)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (lower : record.attempt.phase ≤ event.val)
    (completed : event ∈ record.state.config.cut.completed)
    (surviving : owner ∉ control.execution.application.current.excluded)
    (entry : (app).PlayerEntry) (recorded : entry ∈ control.execution.recall owner)
    (material : WitnessedSubmission graph) (sent : entry.action.transmission = some material)
    (candidate : Handle graph) (named : material.call.packet = .commitment event candidate)
    (sameAttempt : entry.beforeView.application.2.attempt = record.attempt) :
    record.state.accepted (.inr event) = some candidate := by
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have archive := phaseRetiredCompletion_history runtime leaks plan inputs horizon scheduler raw
  obtain ⟨_phase, _installed, _address, _kind, _finished, _receipts, covered⟩ :=
    archive.archives record retired
  have present : record.state.accepted (.inr event) ≠ none := by
    intro missing
    have missed := (record.state.publicView_missedBinding event owner payload binding).mpr
      ⟨completed, missing⟩
    exact surviving (covered event owner (actor?_of_outputLayout_binding graph binding)
      (Or.inl missed))
  obtain ⟨accepted, associated⟩ := Option.ne_none_iff_exists'.mp present
  obtain ⟨valid, _native, _fixed⟩ :=
    phaseRetiredBindings_history runtime leaks plan inputs horizon scheduler raw record retired
  have owned : accepted.1 = owner := by
    obtain ⟨otherPayload, typed⟩ := valid.accepted_typed (.inr event) accepted associated
    exact (EventField.binding.inj (typed.symm.trans binding)).1
  have stamp := phaseArchivedBindingStamp_history runtime leaks plan inputs horizon scheduler
    raw
    record retired
  rcases stamp event accepted associated with earlier |
      ⟨original, originalOutput, originalSender, originalCall, originalAttempt⟩
  · omega
  · change original ∈ (app).outputs (control.execution.recall accepted.1) at originalOutput
    rw [owned] at originalOutput
    have sender : original.sender = owner := originalSender.trans owned
    obtain ⟨message, emitted, messageOwner, messageCall⟩ :=
      recalled_submission_emitted runtime leaks
      initial horizon scheduler raw owner entry recorded material sent
    have messageOutput : message ∈ (app).outputs (control.execution.recall owner) :=
      List.mem_filterMap.mpr ⟨entry, recorded, emitted⟩
    have attempt := phase_recalled_emission_attempt runtime leaks initial horizon scheduler raw
      owner entry recorded message emitted
    have clean : CountClean runtime leaks control.execution :=
      (onePacketMenu_countClean runtime leaks bounds scheduler).history initial horizon
      (fun state _supported => countClean_initial runtime leaks state) trace
    have originalInput : original ∈ control.execution.network.inputs := by
      rw [← clean.1.1 owner] at originalOutput
      exact (List.mem_filter.mp originalOutput).1
    have messageInput : message ∈ control.execution.network.inputs := by
      rw [← clean.1.1 owner] at messageOutput
      exact (List.mem_filter.mp messageOutput).1
    have sameEvent : event? original.payload = event? message.payload := by
      simp only [event?, originalCall, messageCall, named, Payload.event?, Option.map_some,
        originalAttempt, attempt, sameAttempt]
    have same := Permits.eq_of_same_event
      ((permits_eq_true_iff _ _).mp (clean.2 original originalInput))
      ((permits_eq_true_iff _ _).mp (clean.2 message messageInput)) originalInput messageInput
      (fun first firstInput second secondInput ids =>
        (app).input_identifier_injective_history initial horizon scheduler control raw first second
          firstInput secondInput ids) (sender.trans messageOwner.symm) sameEvent
    have candidates : accepted = candidate := by
      have call := congrArg (fun value : Message Player (CommitAttemptPacket graph) =>
        value.payload.packet.call) same
      rw [originalCall, messageCall, named] at call
      exact (Payload.commitment.inj call).2
    simpa only [candidates] using associated

end Vegas.EventGraphRuntime.PhaseCount
