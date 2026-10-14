/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCountUniqueness
import Vegas.Pending.ReactiveOnePacketMenu
import Vegas.Pending.ReactiveSignedCommitments
import Vegas.Pending.ReactiveAssociationEvidence
import Interaction.ReactiveTrafficIdentity

/-! # Count-admitted bindings remain includable while ready and timely

A permitted commitment's prepared handle cannot have been accepted elsewhere:
accepted handles have signed provenance, and the count verdict forbids reusing
that handle. This applies to unusable private bindings as well as valid values.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem counted_binding_handle_unused
    (execution : (runtime.reactiveApplication leaks).Execution)
    (clean : runtime.CountClean leaks execution)
    (signed : runtime.SignedCommitments leaks execution)
    (unique : execution.network.UniqueIds)
    (association : execution.application.AssociationInvariant)
    (message : Message Player (WitnessedPacket graph))
    (member : message ∈ execution.network.inputs)
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.call = .commitment event candidate)
    (ready : execution.application.config.cut.Ready event) :
    execution.application.HandleUnused candidate := by
  have allowed := (countPermits_eq_true_iff _ _).mp (clean.2 message member)
  have correct := allowed.2.1
  rw [CountCallCorrect, call] at correct
  obtain ⟨_, _, _owner, ⟨serial, prepared⟩, _⟩ := correct
  intro field accepted
  cases field with
  | inl input =>
      have initial := signed.inputHandles input candidate accepted
      rw [prepared] at initial
      cases initial
  | inr other =>
      obtain ⟨previous, output, previousCall⟩ := signed.acceptedSigned other candidate accepted
      have previousInput : previous ∈ execution.network.inputs := by
        rw [← clean.1.1 candidate.1] at output
        exact (List.mem_filter.mp output).1
      have previousAllowed := (countPermits_eq_true_iff _ _).mp (clean.2 previous previousInput)
      have same := allowed.commitment_eq_of_handle previousAllowed member previousInput
        (fun left leftInput right rightInput identified =>
          (unique.inputs right rightInput).inputs left leftInput identified) call previousCall
      have eventEq : event = other := by
        rw [← same, call] at previousCall
        exact (Payload.commitment.inj previousCall).1
      subst other
      exact ready.1 (association.accepted_complete event candidate accepted)

theorem counted_binding_resolves
    (execution : (runtime.reactiveApplication leaks).Execution)
    (clean : runtime.CountClean leaks execution)
    (signed : runtime.SignedCommitments leaks execution)
    (unique : execution.network.UniqueIds)
    (association : execution.application.AssociationInvariant)
    (message : Message Player (WitnessedPacket graph))
    (member : message ∈ execution.network.inputs)
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.call = .commitment event candidate)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event) :
    ∃ next, (runtime.reactiveApplication leaks).handle execution.application message = some next ∧
      event ∈ next.config.cut.completed := by
  have allowed := (countPermits_eq_true_iff _ _).mp (clean.2 message member)
  have correct := allowed.2.1
  rw [CountCallCorrect, call] at correct
  obtain ⟨owned, _, candidateOwner, _, _⟩ := correct
  have unused := runtime.counted_binding_handle_unused leaks execution clean signed unique
    association message member event candidate call ready
  have vacant : execution.application.accepted (.inr event) = none := by
    cases accepted : execution.application.accepted (.inr event) with
    | none => rfl
    | some handle => exact (ready.1 (association.accepted_complete event handle accepted)).elim
  cases node : nodeView graph event with
  | sample payload law outputEq codeEq =>
      simp only [bindingOwnedBy, outputEq] at owned
      cases owned
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [bindingOwnedBy, outputEq] at owned
      cases owned
  | bind owner payload outputEq codeEq =>
      have sender : message.sender = owner := by
        have same : owner = message.sender := by
          simpa only [bindingOwnedBy, outputEq, decide_eq_true_eq] using owned
        exact same.symm
      have candidateOwner' : candidate.1 = owner := candidateOwner.trans sender
      have raw := handle_commitment_eq runtime execution.application message.id event candidate
        owner payload outputEq codeEq node ready timely sender candidateOwner' vacant unused
      obtain ⟨next, accepted⟩ : ∃ next,
          (runtime.reactiveApplication leaks).handle execution.application message = some next := by
        rw [runtime.reactiveApplication_handle_of_tokenValid leaks _ _ allowed.1]
        change ∃ next, handle runtime execution.application
          ⟨message.id, message.payload.call⟩ = some next
        rw [call]
        exact ⟨_, raw⟩
      refine ⟨next, accepted, ?_⟩
      obtain ⟨named, addressed, _, completed⟩ := handle_completes runtime _ _ _
        (reactiveHandle_call accepted)
      rw [call] at addressed
      change some event = some named at addressed
      rwa [Option.some.inj addressed]

theorem counted_binding_resolves_of_history
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (clean : runtime.CountClean leaks control.execution)
    (message : Message Player (WitnessedPacket graph))
    (member : message ∈ control.execution.network.inputs)
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.call = .commitment event candidate)
    (ready : control.execution.application.config.cut.Ready event)
    (timely : control.execution.application.WithinDeadline runtime event) :
    ∃ next, (runtime.reactiveApplication leaks).handle control.execution.application message =
      some next ∧ event ∈ next.config.cut.completed := by
  have signed := runtime.signedCommitments_history leaks (inputs.map State.initial)
    (fun state supported => by
      obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨input, rfl⟩) horizon scheduler trace
  have binding : control.execution.application.BindingInvariant :=
    runtime.reactiveBindingInvariant_history leaks inputs horizon scheduler trace
  exact runtime.counted_binding_resolves leaks control.execution clean signed
    ((runtime.reactiveApplication leaks).uniqueIds_history scheduler _ horizon control trace)
    binding.toAssociationInvariant
    message member event candidate call ready timely

end Vegas.EventGraphRuntime
