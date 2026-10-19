/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhasePacketEvidence
import Vegas.Pending.PhaseBindingInvariant
import Vegas.Pending.PhaseCountMenu

/-! # Timely truthful opening acceptance from its actual native certificate -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The candidate association is a factual current native field. Authentic
opening evidence and the genuine raw history supply its openable meaning.
Deferred guards may resolve either way; transport acceptance is unchanged. -/
theorem opening_accepted_of_certificate
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control))
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ control.execution.network.inputs) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L)
    (opening : message.payload.packet.call = .opening event candidate raw)
    (request : control.execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, event⟩)
    (timely : control.execution.application.current.native.WithinDeadline runtime event)
    (allowed : permits control.execution.network.inputs message = true)
    (owner : Player) (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (associated : control.execution.application.current.native.accepted binding.field =
      some candidate) :
    ∃ native next,
      handle runtime control.execution.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native ∧
      event ∈ native.config.cut.completed ∧
      next = ({control.execution.application with current :=
        control.execution.application.current.inclusionResult message.payload.packet.call native} :
          PhaseRuntimeState graph).normalize ∧
      (app).handle control.execution.application message = some next := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have invariant := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler trace
  have permitted := (permits_eq_true_iff _ _).mp allowed
  have correct := permitted.2.1
  unfold CountCallCorrect at correct
  dsimp only [nativeMessage] at correct
  rw [opening] at correct
  obtain ⟨certified, resolves⟩ := correct
  simp only [node] at resolves
  obtain ⟨sender, typed, _signed⟩ := resolves
  have sender' : message.sender = owner := sender
  have ready := request.2.2.1
  have owned : candidate.1 = owner := by
    obtain ⟨ty, kind⟩ := invariant.active.accepted_typed binding.field candidate associated
    exact (EventField.binding.inj (binding.layout_eq.symm.trans kind)).1.symm
  have certificate : message.payload.packet.evidence = some ⟨candidate, raw⟩ := by
    unfold certifiedOpening at certified
    rw [opening] at certified
    cases evidence : message.payload.packet.evidence with
    | none => simp only [evidence, Bool.false_eq_true] at certified
    | some fact =>
        simp only [evidence, decide_eq_true_eq] at certified
        exact congrArg some certified
  have sound := (phasePacketEvidence runtime leaks).history_sound initial horizon scheduler
    trace
  have verified := sound.inputs message member ⟨candidate, raw⟩ (by
    simp only [phasePacketEvidence, certificate, Option.toList_some, List.mem_singleton])
  change control.execution.application.current.native.candidates.lookup candidate =
    .openable raw at verified
  rcases raw with ⟨rawType, value⟩
  change rawType = payload at typed
  subst rawType
  have stored := invariant.active.opening_stored binding candidate value associated verified
  have defined := EventCode.resolveOutput?_isSome binding checks true
    control.execution.application.current.native.config.store (by
      intro field read
      apply control.execution.application.current.native.config.read_available ready
      rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
      exact read)
  obtain ⟨result, resolved⟩ := Option.isSome_iff_exists.mp defined
  have rawAccepted := handle_opening_eq runtime control.execution.application.current.native
    message.id event candidate owner payload binding checks outputEq codeEq node ready timely
    sender' owned associated value verified stored result resolved
  obtain ⟨native, accepted⟩ : ∃ native,
      handle runtime control.execution.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native := by
    rw [opening]
    exact ⟨_, rawAccepted⟩
  obtain ⟨named, addressed, unfinished, completed⟩ :=
    handle_completes runtime _ native _ accepted
  have same : named = event := Option.some.inj (addressed.symm.trans (by
    simp only [opening, Payload.event?]))
  let next := ({control.execution.application with current :=
    control.execution.application.current.inclusionResult message.payload.packet.call native} :
      PhaseRuntimeState graph).normalize
  refine ⟨native, next, accepted, by rwa [same] at completed, rfl, ?_⟩
  change control.execution.application.handle runtime message = some next
  have current : message.payload.attempt = control.execution.application.attempt := request.1
  have token : message.payload.tokenValid control.execution.application.attempt = true :=
    Bool.and_eq_true_iff.mpr ⟨decide_eq_true_eq.mpr current, permitted.1⟩
  have allowed : control.execution.application.allows message.payload.packet.call = true := by
    obtain ⟨phase, member, inside⟩ := request.2.1
    have head : control.execution.application.phases.head? = some phase := member
    simp only [PhaseRuntimeState.allows, head, opening, Payload.event?, decide_eq_true_eq]
    exact inside
  have active : control.execution.application.current.excludedCall
      message.payload.packet.call = false := by
    rw [opening]
    change (graph.actor? event).any
      (fun owner => decide (owner ∈ control.execution.application.current.excluded)) = false
    have acting : graph.actor? event = some message.sender := request.2.2.2.1
    rw [acting, Option.any_some]
    exact decide_eq_false (request.2.2.2.2 :
      message.sender ∉ control.execution.application.current.excluded)
  simp only [PhaseRuntimeState.handle, token, allowed, active, Bool.not_false,
    Bool.and_self, ↓reduceIte, accepted, Option.map_some, next]

end Vegas.EventGraphRuntime.PhaseCount
