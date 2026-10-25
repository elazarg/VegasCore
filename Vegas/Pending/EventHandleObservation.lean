/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.EventCompletionObservation

/-! # Focal observation of focal-authored packet handling -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

private theorem handle_playerView_transport_of_sender (runtime : EventGraphRuntime graph)
    (left right after : State graph) (focal : Player) (message : Message Player (Payload graph))
    (views : left.playerView focal = right.playerView focal) (sender : message.sender = focal)
    (accepted : handle runtime left message = some after) :
    ∃ next, handle runtime right message = some next ∧
      after.playerView focal = next.playerView focal := by
  have publicEq : left.publicView = right.publicView :=
    congrArg PlayerView.publicView views
  have observationEq : graph.playerObserve focal left.config =
      graph.playerObserve focal right.config := by
    have observed := congrArg
      (fun view : PlayerView graph =>
        (view.observation.completionOrder, view.observation.store,
          view.observation.ownActions)) views
    apply PlayerObservation.ext graph
    · exact congrArg Prod.fst observed
    · exact congrArg (fun value => value.2.1) observed
    · exact congrArg (fun value => value.2.2) observed
  have candidatesEq : (fun slot => left.candidates.lookup (focal, slot)) =
      fun slot => right.candidates.lookup (focal, slot) :=
    congrArg PlayerView.candidates views
  have acceptedEq : left.accepted = right.accepted :=
    congrArg PublicView.accepted publicEq
  have clockEq : left.clock = right.clock := congrArg PublicView.clock publicEq
  have activatedEq : left.activatedAt = right.activatedAt :=
    congrArg PublicView.activatedAt publicEq
  have orderEq : left.config.history.map Completion.event =
      right.config.history.map Completion.event :=
    congrArg PlayerObservation.completionOrder observationEq
  have cutEq : left.config.cut = right.config.cut :=
    cut_eq_of_completionOrder_eq left.config right.config orderEq
  have playerStoreEq : graph.playerStore focal left.config.store =
      graph.playerStore focal right.config.store :=
    congrArg PlayerObservation.store observationEq
  have readyTransport {event : graph.EventId} (ready : left.config.cut.Ready event) :
      right.config.cut.Ready event := by
    simpa only [← cutEq] using ready
  have timelyTransport {event : graph.EventId} (timely : left.WithinDeadline runtime event) :
      right.WithinDeadline runtime event := by
    unfold State.WithinDeadline at timely ⊢
    rw [← activatedEq, ← clockEq]
    exact timely
  rcases message with ⟨id, packet⟩
  change id.1 = focal at sender
  cases packet with
  | malformed raw => cases accepted
  | commitment event candidate =>
      obtain ⟨ready, timely, owner, payload, outputEq, codeEq, view, senderOwner, handleOwner,
        vacant, unused, afterEq⟩ :=
        (handle_commitment_iff runtime left after id event candidate).mp accepted
      have ownerEq : owner = focal := senderOwner.symm.trans sender
      cases ownerEq
      rcases candidate with ⟨candidateOwner, slot⟩
      change candidateOwner = focal at handleOwner
      subst candidateOwner
      have rightVacant : right.accepted (.inr event) = none := by
        rw [← acceptedEq]
        exact vacant
      have rightUnused : right.HandleUnused (focal, slot) := by
        intro field
        rw [← acceptedEq]
        exact unused field
      have resultEq : left.bindingResult (focal, slot) payload =
          right.bindingResult (focal, slot) payload := by
        unfold State.bindingResult
        rw [congrFun candidatesEq slot]
      have rightAccepted := handle_commitment_eq runtime right id event (focal, slot) focal
        payload outputEq codeEq view (readyTransport ready) (timelyTransport timely)
        senderOwner rfl rightVacant rightUnused
      refine ⟨_, rightAccepted, ?_⟩
      rw [afterEq]
      apply State.acceptHandle_playerView_congr
      apply State.complete_playerView_congr left right focal publicEq observationEq candidatesEq
        event ready (readyTransport ready)
      · intro _
        rw [resultEq]
      · intro _
        rw [resultEq]
  | opening event candidate raw =>
      obtain ⟨ready, timely, owner, payload, binding, checks, outputEq, codeEq, value, result,
        view, senderOwner, handleOwner, associated, rawEq, verified, stored, resolved, afterEq⟩ :=
        (handle_opening_iff runtime left after id event candidate raw).mp accepted
      have ownerEq : owner = focal := senderOwner.symm.trans sender
      cases ownerEq
      rcases candidate with ⟨candidateOwner, slot⟩
      change candidateOwner = focal at handleOwner
      subst candidateOwner
      have rightAssociated : right.accepted binding.field = some (focal, slot) := by
        rw [← acceptedEq]
        exact associated
      have rightVerified : right.candidates.lookup (focal, slot) =
          .openable ⟨payload, value⟩ := by
        rw [← congrFun candidatesEq slot]
        exact verified
      have rightStored : binding.get? right.config.store = some (.success value) := by
        rw [← binding.get?_playerStore focal right.config.store rfl, ← playerStoreEq,
          binding.get?_playerStore focal left.config.store rfl]
        exact stored
      have rightResolved : EventCode.resolveOutput? binding checks true right.config.store =
          some result := by
        rw [← EventCode.resolveOutput?_playerStore binding checks right.config.store true,
          ← playerStoreEq,
          EventCode.resolveOutput?_playerStore binding checks left.config.store true]
        exact resolved
      have rightAccepted := handle_opening_eq runtime right id event (focal, slot) focal
        payload binding checks outputEq codeEq view (readyTransport ready)
        (timelyTransport timely) senderOwner rfl rightAssociated value rightVerified rightStored
        result rightResolved
      rw [rawEq]
      refine ⟨_, rightAccepted, ?_⟩
      rw [afterEq]
      apply State.complete_playerView_congr left right focal publicEq observationEq candidatesEq
        event ready (readyTransport ready) <;> exact fun _ => rfl

/-- Handling the same focal-authored packet has the same focal observation in
two states with equal focal views. Foreign candidate meanings, binding values,
and supplied graph actions need not agree. -/
theorem handle_playerView_congr_of_sender
    (runtime : EventGraphRuntime graph) (left right : State graph) (focal : Player)
    (message : Message Player (Payload graph))
    (views : left.playerView focal = right.playerView focal)
    (sender : message.sender = focal) :
    Option.map (fun state => state.playerView focal) (handle runtime left message) =
      Option.map (fun state => state.playerView focal) (handle runtime right message) := by
  cases leftEq : handle runtime left message with
  | none =>
      cases rightEq : handle runtime right message with
      | none => rfl
      | some after =>
          obtain ⟨next, impossible, _⟩ :=
            handle_playerView_transport_of_sender runtime right left after
              focal message views.symm sender rightEq
          rw [leftEq] at impossible
          cases impossible
  | some after =>
      obtain ⟨next, rightEq, equal⟩ :=
        handle_playerView_transport_of_sender runtime left right after
          focal message views sender leftEq
      rw [rightEq]
      exact congrArg some equal

private theorem handle_commitment_playerView_transport (runtime : EventGraphRuntime graph)
    (left right after : State graph) (focal : Player) (id : MessageId Player)
    (event : graph.EventId) (candidate : Handle graph)
    (views : left.playerView focal = right.playerView focal)
    (accepted : handle runtime left ⟨id, .commitment event candidate⟩ = some after) :
    ∃ next, handle runtime right ⟨id, .commitment event candidate⟩ = some next ∧
      after.playerView focal = next.playerView focal := by
  have publicEq : left.publicView = right.publicView :=
    congrArg PlayerView.publicView views
  have observationEq : graph.playerObserve focal left.config =
      graph.playerObserve focal right.config := by
    have observed := congrArg
      (fun view : PlayerView graph =>
        (view.observation.completionOrder, view.observation.store,
          view.observation.ownActions)) views
    apply PlayerObservation.ext graph
    · exact congrArg Prod.fst observed
    · exact congrArg (fun value => value.2.1) observed
    · exact congrArg (fun value => value.2.2) observed
  have candidatesEq := congrArg PlayerView.candidates views
  have acceptedEq : left.accepted = right.accepted :=
    congrArg PublicView.accepted publicEq
  have clockEq : left.clock = right.clock := congrArg PublicView.clock publicEq
  have activatedEq : left.activatedAt = right.activatedAt :=
    congrArg PublicView.activatedAt publicEq
  have cutEq : left.config.cut = right.config.cut :=
    cut_eq_of_completionOrder_eq left.config right.config
      (congrArg PlayerObservation.completionOrder observationEq)
  change (fun slot => left.candidates.lookup (focal, slot)) =
    (fun slot => right.candidates.lookup (focal, slot)) at candidatesEq
  obtain ⟨ready, timely, owner, payload, outputEq, codeEq, view, sender, handleOwner,
    vacant, unused, afterEq⟩ :=
    (handle_commitment_iff runtime left after id event candidate).mp accepted
  have rightReady : right.config.cut.Ready event := by simpa only [← cutEq] using ready
  have rightTimely : right.WithinDeadline runtime event := by
    unfold State.WithinDeadline at timely ⊢
    rw [← activatedEq, ← clockEq]
    exact timely
  have rightVacant : right.accepted (.inr event) = none := by
    rw [← acceptedEq]
    exact vacant
  have rightUnused : right.HandleUnused candidate := by
    intro field
    rw [← acceptedEq]
    exact unused field
  have resultEq (ownerFocal : owner = focal) :
      left.bindingResult candidate payload = right.bindingResult candidate payload := by
    rcases candidate with ⟨candidateOwner, slot⟩
    change candidateOwner = owner at handleOwner
    have actualOwner : candidateOwner = focal := handleOwner.trans ownerFocal
    cases actualOwner
    unfold State.bindingResult
    rw [congrFun candidatesEq slot]
  have rightAccepted := handle_commitment_eq runtime right id event candidate owner payload
    outputEq codeEq view rightReady rightTimely sender handleOwner rightVacant rightUnused
  refine ⟨_, rightAccepted, ?_⟩
  rw [afterEq]
  apply State.acceptHandle_playerView_congr
  apply State.complete_playerView_congr left right focal publicEq observationEq candidatesEq
    event ready rightReady
  · intro visible
    unfold EventGraph.fieldVisibleTo at visible
    change (graph.outputLayout event).VisibleTo focal at visible
    rw [outputEq] at visible
    change owner = focal at visible
    rw [resultEq visible]
  · intro focalActor
    have ownerActor : graph.actor? event = some owner := by
      change (graph.nodes event).actor = some owner
      rw [← EventCode.actor_cast outputEq (graph.nodes event), codeEq]
      rfl
    rw [resultEq (Option.some.inj (ownerActor.symm.trans focalActor))]

/-- Commitment packets have the same acceptance status and focal result under
equal focal views, regardless of their sender.  A foreign binding result may
differ semantically, but both its value and its action are hidden from the
focal observer. -/
theorem handle_commitment_playerView_congr
    (runtime : EventGraphRuntime graph) (left right : State graph) (focal : Player)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (views : left.playerView focal = right.playerView focal) :
    Option.map (fun state => state.playerView focal)
        (handle runtime left ⟨id, .commitment event candidate⟩) =
      Option.map (fun state => state.playerView focal)
        (handle runtime right ⟨id, .commitment event candidate⟩) := by
  cases leftEq : handle runtime left ⟨id, .commitment event candidate⟩ with
  | none =>
      cases rightEq : handle runtime right ⟨id, .commitment event candidate⟩ with
      | none => rfl
      | some after =>
          obtain ⟨next, impossible, _⟩ :=
            handle_commitment_playerView_transport runtime right left after
              focal id event candidate views.symm rightEq
          rw [leftEq] at impossible
          cases impossible
  | some after =>
      obtain ⟨next, rightEq, equal⟩ :=
        handle_commitment_playerView_transport runtime left right after
          focal id event candidate views leftEq
      rw [rightEq]
      exact congrArg some equal

end Vegas.EventGraphRuntime
