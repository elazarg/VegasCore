/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDisclosureAdmission
import Vegas.Pending.ReactivePacketService

/-! # Compiled disclosures through arbitrary wire reactions

The actual response retains its selected call and opening evidence while other
players react. Completed reads and their accepted associations are stable, so
the shared service theorem applies to successful and failed disclosure alike.
The result concerns prescribed owner behavior; prior conflicting own packets
and sequential-equilibrium continuation recovery remain separate obligations.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The actual compiled disclosure response realizes its source result after
arbitrary wire reactions and the reserved inclusion. Guard rejection does not
remove the opening evidence from a true disclosure of a successful binding. -/
theorem reactiveDecision_disclosure_service (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : graph.Inputs) (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (action : graph.Action event) (result : PublicationResult (L.Val payload))
    (policy : graph.BehavioralPolicy owner)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (prescribed : players owner = runtime.prescribedReactivePolicy leaks owner policy)
    (network : runtime.NetworkPolicy leaks) (rounds : Nat)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (valid : execution.application.Invariant inputs)
    (associated : execution.application.BindingInvariant)
    (unremembered : execution.application.remembered event = none)
    (integrity : runtime.ReactivePacketIntegrity leaks owner execution)
    (audit : execution.SubmissionAudit (runtime.reactiveApplication leaks)
      ReactivePlayerView.publicView)
    (recall : execution.InputRecall (runtime.reactiveApplication leaks))
    (serials : execution.network.SerialsBeforeNext)
    (activated : (runtime.reactiveApplication leaks).submissionObservation?
        execution.environmentRecall (owner, execution.network.nextSerial owner) =
      some execution.application.publicView)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline runtime event)
    (resolved : EventCode.resolveOutput? binding checks
      (cast (congrArg EventField.Action outputEq) action) execution.application.config.store =
        some result)
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
    next.application.config.outputs event =
      some (cast (congrArg EventField.Value outputEq.symm) result) := by
  let app := runtime.reactiveApplication leaks
  let response := runtime.reactiveDecision leaks owner event action
    (app.observePlayer execution.application owner)
  let packet := reactiveResolutionPacket owner event payload binding checks outputEq action
    (app.observePlayer execution.application owner)
  let material := disclosureSubmission packet
  let submitted := execution.respond app owner response
  let message : Message Player (WitnessedPacket graph) :=
    ⟨(owner, execution.network.nextSerial owner),
      app.packet (app.submit execution.application owner material) owner
        (execution.network.known owner) material⟩
  have sent : response.transmission = some (.submit material) := by
    simp only [response, reactiveDecision, node, material, packet, app]
  let fields := insert binding.field (GuardCheck.listReadFields checks)
  have available : ∀ field ∈ fields,
      (execution.application.config.store field).isSome = true := by
    intro field member
    apply execution.application.config.read_available ready
    rw [resolution_readFields event owner payload binding checks outputEq codeEq]
    exact member
  let resources (state : State graph) := state.BindingInvariant ∧ state.remembered event = none ∧
    ∀ field ∈ fields, state.config.store field = execution.application.config.store field ∧
      state.accepted field = execution.application.accepted field
  have bindingInvariant := runtime.reactiveBindingInvariant leaks
  have memoryInvariant := runtime.reactiveRememberedInvariant leaks
    (fun table => table event = none)
  have frameInvariant := runtime.reactiveReadFrameInvariant leaks execution.application fields
    available
  have stable : app.Invariant resources := {
    submit := fun state who submission good =>
      ⟨bindingInvariant.submit state who submission good.1,
        memoryInvariant.submit state who submission good.2.1,
        frameInvariant.submit state who submission good.2.2⟩
    handle := fun state envelope after good handled =>
      ⟨bindingInvariant.handle state envelope after good.1 handled,
        memoryInvariant.handle state envelope after good.2.1 handled,
        frameInvariant.handle state envelope after good.2.2 handled⟩
    environment := fun state command after good moved =>
      ⟨bindingInvariant.environment state command after good.1 moved,
        memoryInvariant.environment state command after good.2.1 moved,
        frameInvariant.environment state command after good.2.2 moved⟩ }
  have initialResources : resources execution.application :=
    ⟨associated, unremembered, fun _ _ => ⟨rfl, rfl⟩⟩
  have actor : graph.actor? event = some owner := by
    have equal := congrArg EventCode.actor codeEq
    rw [EventCode.actor_cast outputEq (graph.nodes event)] at equal
    exact equal
  have addressed : message.payload.call.event? graph = some event :=
    reactiveResolutionPacket_event owner event payload binding checks outputEq action _
  have emitted : message ∈ app.outputs (submitted.recall owner) := by
    simp only [submitted, ReactiveApplication.Execution.respond, sent, MessageNetwork.submit,
      ↓reduceIte, ReactiveApplication.outputs, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have retained : message ∈ submitted.network.pending := by
    simp only [submitted, ReactiveApplication.Execution.respond, sent, MessageNetwork.submit]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have newlyIssued : message.id ∉ execution.network.ledger.map Message.id := by
    rintro member
    obtain ⟨previous, prior, equal⟩ := List.mem_map.mp member
    have earlier := serials.ledger previous prior
    change previous.id.2 < execution.network.nextSerial previous.id.1 at earlier
    rw [equal] at earlier
    exact Nat.lt_irrefl _ earlier
  have unpublished : (submitted.observeEnvironment app).Unpublished app message.id := by
    simpa only [ReactiveApplication.EnvironmentView.Unpublished,
      ReactiveApplication.Execution.observeEnvironment, MessageNetwork.publicView, submitted,
      ReactiveApplication.Execution.respond, sent, MessageNetwork.submit] using newlyIssued
  have same := runtime.reactive_respond_application leaks execution owner response
  have afterReady : submitted.application.config.cut.Ready event := by
    change (execution.respond app owner response).application.config.cut.Ready event
    rwa [same.1]
  have afterTimely : submitted.application.WithinDeadline runtime event := by
    have progress := runtime.reactive_respond_progress leaks inputs execution owner response valid
    exact ((progress.ready_timely_or_completed runtime event ready timely).resolve_left
      afterReady.1).2
  apply runtime.reactive_packet_wire_block leaks inputs owner event actor
    (cast (congrArg EventField.Value outputEq.symm) result) message rfl addressed players
    (fun current => resources current.application)
    (ReactiveApplication.Invariant.policyInvariant app stable players)
    (runtime.reactivePacketIntegrity_policy leaks owner policy players prescribed) ?_ network rounds
    submitted next (stable.respond execution owner response initialResources)
    ((runtime.reactiveStateInvariant leaks inputs).respond execution owner response valid)
    ((runtime.reactivePacketIntegrity_policy leaks owner policy players prescribed).respond
      execution owner response integrity (by rw [prescribed]; exact supported))
    (app.submissionAudit_respond ReactivePlayerView.publicView (by intros; rfl)
      execution owner response audit (app.submissionOrigin_next_none execution owner recall serials)
        activated)
    (app.respond_inputRecall execution owner response recall)
    ((app.serialsBeforeNextInvariant (fun _ _ => FinDist.pure .wait)).respond execution owner
      response serials) emitted afterReady afterTimely retained unpublished reached
  intro current good currentReady currentTimely
  have bindingFrame := good.2.2 binding.field (Finset.mem_insert_self ..)
  have packetEq : reactiveResolutionPacket owner event payload binding checks outputEq action
      (app.observePlayer current.application owner) = packet := by
    apply reactiveResolutionPacket_eq_of_resolution owner event payload binding checks
      outputEq action
    · change EventCode.resolveOutput? binding checks true
          (graph.playerStore owner current.application.config.store) =
        EventCode.resolveOutput? binding checks true
          (graph.playerStore owner execution.application.config.store)
      rw [EventCode.resolveOutput?_playerStore, EventCode.resolveOutput?_playerStore]
      exact EventCode.resolveOutput?_congr binding checks true _ _
        (fun field member => (good.2.2 field member).1)
    · exact bindingFrame.2
  have resultEq := EventCode.resolveOutput?_congr binding checks
    (cast (congrArg EventField.Action outputEq) action) current.application.config.store
    execution.application.config.store (fun field member => (good.2.2 field member).1)
  obtain ⟨currentResult, selected, after, evaluates, transmission, handled, stored, _⟩ :=
    runtime.reactiveDecision_disclosure_public_law leaks current.application good.1 message.id
      owner event payload binding checks outputEq codeEq node currentReady currentTimely rfl
      good.2.1 action
  have sameResult : currentResult = result := Option.some.inj
    (evaluates.symm.trans (resultEq.trans resolved))
  subst currentResult
  have samePacket : packet = selected := by
    simp only [reactiveDecision, node] at transmission
    have equal := ReactiveApplication.Transmission.submit.inj (Option.some.inj transmission)
    exact packetEq.symm.trans
      (congrArg (fun submission : WitnessedSubmission graph => submission.call.packet) equal)
  subst selected
  refine ⟨after, handled, ?_⟩
  have output := congrFun stored (.inr event)
  simpa only [State.complete, Config.store, Config.complete_output_same] using output

end Vegas.EventGraphRuntime
