/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingAdmission
import Vegas.Pending.ReactivePacketService

/-! # Binding packets throughout the actual reactive wire block

The service may include a prescribed binding during an intervening wire turn.
If it has not done so, the original unspent envelope remains eligible for the
reserved inclusion. These facts concern the actual response/inclusion protocol;
no dependency monitor or replacement scheduler is introduced.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Once the prescribed binding envelope has been submitted at a usable
opportunity, arbitrary intervening wire turns and the actual reserved inclusion
store its fixed selected result. The premises are post-response invariants;
opponent policies and the passive leak rule are unrestricted. -/
theorem reactive_binding_wire_block (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (result : PublicationResult (L.Val payload)) (serial nonce : Nat)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (prescribed : players owner = runtime.prescribedReactivePolicy leaks owner policy)
    (network : runtime.NetworkPolicy leaks) (rounds : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.Invariant inputs)
    (associated : execution.application.BindingInvariant)
    (integrity : runtime.ReactivePacketIntegrity leaks owner execution)
    (protection : runtime.ReactiveCandidateProtection leaks owner event
      (owner, .prepared serial) execution)
    (meaning : execution.application.bindingResult (owner, .prepared serial) payload = result)
    (audit : execution.SubmissionAudit (runtime.reactiveApplication leaks)
      ReactivePlayerView.publicView)
    (recall : execution.InputRecall (runtime.reactiveApplication leaks))
    (serials : execution.network.SerialsBeforeNext)
    (emitted : (⟨(owner, nonce), ⟨.commitment event (owner, .prepared serial), none⟩⟩ :
      Message Player (WitnessedPacket graph)) ∈
        (runtime.reactiveApplication leaks).outputs (execution.recall owner))
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (pending : (⟨(owner, nonce), ⟨.commitment event (owner, .prepared serial), none⟩⟩ :
      Message Player (WitnessedPacket graph)) ∈ execution.network.pending)
    (unpublished : (execution.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
      (runtime.reactiveApplication leaks) (owner, nonce))
    (reached : next ∈ (runtime.runInteractionPlan leaks players network
      (List.replicate rounds .wire ++ [.includeLatest event owner]) execution).support) :
    next.application.config.outputs event =
      some (cast (congrArg EventField.Value outputEq.symm) result) := by
  let app := runtime.reactiveApplication leaks
  let candidate : Handle graph := (owner, .prepared serial)
  let message : Message Player (WitnessedPacket graph) :=
    ⟨(owner, nonce), ⟨.commitment event candidate, none⟩⟩
  let resources (current : app.Execution) := current.application.BindingInvariant ∧
    runtime.ReactiveCandidateProtection leaks owner event candidate current ∧
    current.application.candidates.lookup candidate =
      execution.application.candidates.lookup candidate
  have bindingInvariant := runtime.reactiveBindingInvariant leaks
  have protectedInvariant := runtime.reactiveCandidateProtection_policy leaks owner event
    candidate rfl policy players prescribed
  have preserved : app.PolicyInvariant players resources := {
    respond := by
      intro current who action good supported
      exact ⟨bindingInvariant.respond current who action good.1,
        protectedInvariant.respond current who action good.2.1 supported,
        (runtime.reactive_respond_candidate_fixed leaks current who action candidate
          good.2.1.fixed).trans good.2.2⟩
    environment := by
      intro current after command good moved
      exact ⟨bindingInvariant.environmentStep current after command good.1 moved,
        protectedInvariant.environment current after command good.2.1 moved,
        (runtime.reactive_environment_candidate_fixed leaks current after command candidate
          good.2.1.fixed moved).trans good.2.2⟩ }
  have actor : graph.actor? event = some owner := by
    have equal := congrArg EventCode.actor codeEq
    rw [EventCode.actor_cast outputEq (graph.nodes event)] at equal
    exact equal
  apply runtime.reactive_packet_wire_block leaks inputs owner event actor
    (cast (congrArg EventField.Value outputEq.symm) result) message rfl rfl players resources
    preserved (runtime.reactivePacketIntegrity_policy leaks owner policy players prescribed) ?_
    network rounds execution next ⟨associated, protection, rfl⟩ valid integrity audit recall serials
    emitted ready timely pending unpublished reached
  intro current good currentReady currentTimely
  have vacant : current.application.accepted (.inr event) = none := by
    cases cell : current.application.accepted (.inr event) with
    | none => rfl
    | some chosen => exact False.elim (currentReady.1
        (good.1.toAssociationInvariant.accepted_complete event chosen cell))
  have fixedMeaning : current.application.bindingResult candidate payload = result := by
    rw [State.bindingResult, good.2.2]
    exact meaning
  have handled := runtime.handle_commitment_eq current.application message.id event candidate owner
    payload outputEq codeEq node currentReady currentTimely rfl rfl vacant
    (good.2.1.unused currentReady.1)
  refine ⟨_, handled, ?_⟩
  simp only [State.complete, fixedMeaning, Config.complete_output_same]

/-- The actual compiled binding response survives every wire reaction and is
realized by the ensuing reserved inclusion. Fresh allocation and the activation
stamp are explicit prefix obligations, not assumptions about later traffic. -/
theorem reactiveDecision_binding_service (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (action : graph.Action event) (serial : Nat)
    (policy : graph.BehavioralPolicy owner)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (prescribed : players owner = runtime.prescribedReactivePolicy leaks owner policy)
    (network : runtime.NetworkPolicy leaks) (rounds : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.Invariant inputs)
    (associated : execution.application.BindingInvariant)
    (integrity : runtime.ReactivePacketIntegrity leaks owner execution)
    (fixed : runtime.ReactiveCommitmentsFixed leaks execution)
    (audit : execution.SubmissionAudit (runtime.reactiveApplication leaks)
      ReactivePlayerView.publicView)
    (recall : execution.InputRecall (runtime.reactiveApplication leaks))
    (serials : execution.network.SerialsBeforeNext)
    (activated : (runtime.reactiveApplication leaks).submissionObservation?
        execution.environmentRecall (owner, execution.network.nextSerial owner) =
      some execution.application.publicView)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (allocated : reactiveFreshSlot
      ((runtime.reactiveApplication leaks).observePlayer execution.application owner) = some serial)
    (supported : runtime.reactiveDecision leaks owner event action
        ((runtime.reactiveApplication leaks).observePlayer execution.application owner) ∈
      (runtime.prescribedReactivePolicy leaks owner policy (execution.recall owner)
        (execution.observe (runtime.reactiveApplication leaks) owner)).support)
    (reached : next ∈ (runtime.runInteractionPlan leaks players network
      (List.replicate rounds .wire ++ [.includeLatest event owner])
        (execution.respond (runtime.reactiveApplication leaks) owner
          (runtime.reactiveDecision leaks owner event action
            ((runtime.reactiveApplication leaks).observePlayer
              execution.application owner)))).support) :
    next.application.config.outputs event = some
      (cast (congrArg EventField.Value outputEq.symm)
        (cast (congrArg EventField.Action outputEq) action)) := by
  let app := runtime.reactiveApplication leaks
  let result : PublicationResult (L.Val payload) :=
    cast (congrArg EventField.Action outputEq) action
  let response := runtime.reactiveBinding leaks owner event payload result serial
  let submitted := execution.respond app owner response
  let message : Message Player (WitnessedPacket graph) :=
    ⟨(owner, execution.network.nextSerial owner),
      ⟨.commitment event (owner, .prepared serial), none⟩⟩
  have responseEq := runtime.reactiveDecision_binding_eq leaks owner owner event payload outputEq
    codeEq node action _ serial allocated
  rw [responseEq] at reached supported
  have fresh := reactiveFreshSlot_spec
    ((runtime.reactiveApplication leaks).observePlayer execution.application owner) serial allocated
  have unused : execution.application.HandleUnused (owner, .prepared serial) :=
    fun field cell => associated.accepted_fixed field _ cell fresh
  have same := runtime.reactive_respond_application leaks execution owner response
  have newlyIssued : message.id ∉ execution.network.ledger.map Message.id := by
    rintro member
    obtain ⟨previous, prior, equal⟩ := List.mem_map.mp member
    have earlier := serials.ledger previous prior
    change previous.id.2 < execution.network.nextSerial previous.id.1 at earlier
    rw [equal] at earlier
    exact Nat.lt_irrefl _ earlier
  have output : message ∈ app.outputs (submitted.recall owner) := by
    change message ∈ app.outputs ((execution.respond app owner response).recall owner)
    simp only [response, reactiveBinding, ReactiveApplication.Execution.respond,
      MessageNetwork.submit, ↓reduceIte, ReactiveApplication.outputs, List.filterMap_append,
      List.filterMap_cons, List.filterMap_nil]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have retained : message ∈ submitted.network.pending :=
    List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have afterReady : submitted.application.config.cut.Ready event := by
    change (execution.respond app owner response).application.config.cut.Ready event
    rwa [same.1]
  have afterTimely : submitted.application.WithinDeadline runtime event := by
    have progress := runtime.reactive_respond_progress leaks inputs execution owner response valid
    exact ((progress.ready_timely_or_completed runtime event ready timely).resolve_left
      afterReady.1).2
  apply runtime.reactive_binding_wire_block leaks inputs owner event payload outputEq codeEq node
    result serial (execution.network.nextSerial owner) policy players prescribed network rounds
    submitted next
    ((runtime.reactiveStateInvariant leaks inputs).respond execution owner response valid)
    ((runtime.reactiveBindingInvariant leaks).respond execution owner response associated)
    ((runtime.reactivePacketIntegrity_policy leaks owner policy players prescribed).respond
      execution owner response integrity (by rw [prescribed]; exact supported))
    (runtime.reactiveBinding_protection leaks owner event payload result serial execution fixed
      fresh unused)
    (runtime.reactiveBinding_result leaks owner event payload result serial execution fresh)
    (app.submissionAudit_respond ReactivePlayerView.publicView (by intros; rfl)
      execution owner response audit (app.submissionOrigin_next_none execution owner recall serials)
        activated)
    (app.respond_inputRecall execution owner response recall)
    ((app.serialsBeforeNextInvariant (fun _ _ => FinDist.pure .wait)).respond
      execution owner response serials) output afterReady afterTimely retained newlyIssued reached

end Vegas.EventGraphRuntime
