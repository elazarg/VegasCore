/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingStampHistory
import Vegas.Pending.PhaseAttemptCheckpoint
import Vegas.Pending.PhaseRecordedBindingMeaning
import Vegas.Pending.PhaseCountUniqueness
import Interaction.ReactiveRecordedResponse

/-! # Typed declarations of surviving owners in completed live attempts -/

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

/-- A surviving owner's completed live binding accepts its recalled packet
in the current physical attempt. Other owners may already be excluded. -/
theorem completed_recorded_binding_accepted
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (lower : control.execution.application.attempt.phase ≤ event.val)
    (completed : event ∈ control.execution.application.current.native.config.cut.completed)
    (surviving : owner ∉ control.execution.application.current.excluded)
    (entry : (app).PlayerEntry) (recorded : entry ∈ control.execution.recall owner)
    (material : WitnessedSubmission graph) (sent : entry.action.transmission = some material)
    (candidate : Handle graph) (named : material.call.packet = .commitment event candidate)
    (sameAttempt : entry.beforeView.application.2.attempt =
      control.execution.application.attempt) :
    control.execution.application.current.native.accepted (.inr event) = some candidate := by
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have coverage :=
    (phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler raw).active
  have present : control.execution.application.current.native.accepted (.inr event) ≠ none := by
    intro missing
    have missed := (control.execution.application.current.native.publicView_missedBinding
      event owner payload binding).mpr ⟨completed, missing⟩
    exact surviving (coverage.covered event owner (actor?_of_outputLayout_binding graph binding)
      (Or.inl missed))
  obtain ⟨accepted, associated⟩ := Option.ne_none_iff_exists'.mp present
  have valid := (phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw).active
  have owned : accepted.1 = owner := by
    obtain ⟨otherPayload, typed⟩ := valid.accepted_typed (.inr event) accepted associated
    exact (EventField.binding.inj (typed.symm.trans binding)).1
  have stamp := phaseLiveBindingStamp_history runtime leaks plan inputs horizon scheduler raw
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

/-- The completed live graph action is the exact typed result declared at the
original legal callback, without a clear-state, receipt or freshness premise. -/
theorem completed_recorded_binding_action
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (lower : control.execution.application.attempt.phase ≤ event.val)
    (completed : event ∈ control.execution.application.current.native.config.cut.completed)
    (surviving : owner ∉ control.execution.application.current.excluded)
    (result : PublicationResult (L.Val payload)) (serial : Nat) (entry : (app).PlayerEntry)
    (recorded : entry ∈ control.execution.recall owner)
    (declared : entry.action = phaseBindingResponse runtime leaks owner event payload result serial)
    (sameAttempt : entry.beforeView.application.2.attempt =
      control.execution.application.attempt) :
    ∃ original : graph.Action event,
      ⟨event, original⟩ ∈ control.execution.application.current.native.config.history ∧
      cast (congrArg EventField.Action binding) original = result := by
  obtain ⟨before, prior, _prefix, _acting, viewed, offered, _recalled⟩ :=
    (menu).recorded_response_prefix initial horizon scheduler control trace owner entry recorded
  rw [declared] at offered
  have fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh := by
    cases result with
    | failure =>
        exact viewed ▸ onePacket_binding_fresh runtime leaks bounds plan inputs horizon scheduler
          prior owner event serial none .none offered
    | success value =>
        exact viewed ▸ onePacket_binding_fresh runtime leaks bounds plan inputs horizon scheduler
          prior owner event serial (some ⟨payload, value⟩) .none offered
  obtain ⟨material, sent⟩ : ∃ material, entry.action.transmission = some material := by
    rw [declared]
    exact ⟨_, rfl⟩
  have exactMaterial : (phaseBindingResponse runtime leaks owner event payload result
      serial).transmission = some material := declared ▸ sent
  have named : material.call.packet = .commitment event (owner, .prepared serial) :=
    (congrArg (fun material : WitnessedSubmission graph => material.call.packet)
      (Option.some.inj exactMaterial)).symm
  have accepted := completed_recorded_binding_accepted runtime leaks bounds plan inputs horizon
    scheduler trace owner event payload binding lower completed surviving entry recorded material
      sent (owner, .prepared serial) named sameAttempt
  have raw := (menu).toRawTrace initial horizon scheduler trace
  obtain ⟨_draw, valid⟩ :=
    phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler raw
  have bindings :=
    (phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw).active
  obtain ⟨original, retained, meaning⟩ := bindings.completed_binding_action valid.active.reachable
    event owner payload binding completed
  rw [accepted, Option.elim_some] at meaning
  exact ⟨original, retained, meaning.trans (phase_recorded_binding_result runtime leaks initial
    horizon scheduler raw owner event payload result serial entry recorded declared fresh)⟩

end Vegas.EventGraphRuntime.PhaseCount
