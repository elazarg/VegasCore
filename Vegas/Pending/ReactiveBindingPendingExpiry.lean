/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrameStep
import Vegas.Pending.ReactiveBindingRestoration

/-! # Expiry of a pending unusable binding under private repair

An unusable binding's locally remembered original result is failure. Due expiry
uses that same result on both actual executions, so this pending shadow does not
require an invented completed boundary. The joint law preserves actual public
miss markers, traffic, receipts, foreign inputs and reconstructed owner recall.
This operational component does not prove whole-policy settlement dominance.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

/-- Private repair records the actual unusable choice's failure locally, even
while the opaque packet remains pending. No completion is presumed. -/
theorem repairResponse_unusable_shadow_failure
    (who : Player) (memory : BindingMemory runtime leaks)
    (actual : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (originalFresh : (memory.shadow.inputView runtime leaks actual).application.candidates
      (.prepared serial) = .fresh)
    (actualFresh : actual.application.candidates (.prepared serial) = .fresh)
    (unusable : opening.bind (fun raw => raw.as? payload) = none) :
    let change := memory.repairResponse runtime leaks who actual
      ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩
    change.2.actions event = some
        (cast (congrArg EventField.Action outputEq.symm) PublicationResult.failure) ∧
      change.2.values (.inr event) = some
        (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure) := by
  simp only [repairResponse, node, originalFresh, actualFresh, unusable, and_self,
    ↓reduceIte, Option.elim_none, BindingShadow.rememberCompletion, Function.update_self]

namespace Frame

variable {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- An owned completion agreeing with the locally remembered original action
and value preserves the full frame, even if its shadow was installed while pending. -/
theorem complete_matching_override
    (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId) (leftReady : original.application.config.cut.Ready event)
    (rightReady : repaired.application.config.cut.Ready event)
    (owned : graph.actor? event = some owner)
    (visible : graph.fieldVisibleTo owner (.inr event))
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (rememberedAction : memory.shadow.actions event = some action)
    (rememberedValue : memory.shadow.values (.inr event) = some value) :
    Frame runtime leaks memory owner
      { original with application := original.application.complete event leftReady action value }
      { repaired with
        application := repaired.application.complete event rightReady action value } := by
  let app := runtime.reactiveApplication leaks
  have application := congrArg ReactiveApplication.PlayerView.application frame.observed
  have reconstructed := memory.shadow.rememberCompletion_observation owner
    original.application.config repaired.application.config
    (congrArg (fun view : ReactivePlayerView graph => view.observation.store) application)
    (congrArg (fun view : ReactivePlayerView graph => view.observation.ownActions) application)
    event leftReady rightReady owned visible action action value value
  rw [memory.shadow.rememberCompletion_eq_self event action value rememberedAction
    rememberedValue] at reconstructed
  have nextPublic := State.complete_publicView_congr original.application repaired.application
    frame.publicView
    event leftReady rightReady action value
  have nextObservation :
      (memory.shadow.view (app.observePlayer
        (repaired.application.complete event rightReady action value) owner)).observation =
      (app.observePlayer
        (original.application.complete event leftReady action value) owner).observation := by
    apply PlayerObservation.ext graph
    · exact (congrArg (fun view : PublicView graph => view.observation.completionOrder)
        nextPublic).symm
    · exact reconstructed.1
    · exact reconstructed.2
  have nextApplication : memory.shadow.view (app.observePlayer
      (repaired.application.complete event rightReady action value) owner) =
        app.observePlayer (original.application.complete event leftReady action value) owner := by
    exact congr (congr (congrArg (ReactivePlayerView.mk owner) nextPublic.symm) nextObservation)
      (congrArg ReactivePlayerView.candidates application)
  refine ⟨frame.past, ?_, frame.lengths, frame.network, frame.service, ?_,
    frame.recall, frame.slots, ?_, frame.submissions⟩
  · change (⟨repaired.network.observe owner, memory.shadow.view (app.observePlayer
      (repaired.application.complete event rightReady action value) owner),
        repaired.receipts⟩ : app.PlayerView) =
      ⟨original.network.observe owner, app.observePlayer
        (original.application.complete event leftReady action value) owner, original.receipts⟩
    exact congr (congr (congrArg (ReactiveApplication.PlayerView.mk (app := app))
      (congrArg (fun network => network.observe owner) frame.network.symm)) nextApplication)
        frame.receipts.symm
  · intro who different
    exact State.complete_playerView_congr original.application repaired.application who
      frame.publicView
      (original.application.playerView_observation_eq repaired.application who
        (frame.views who different))
      (congrArg PlayerView.remembered (frame.views who different))
      (congrArg PlayerView.candidates (frame.views who different)) event leftReady rightReady
      action action value value (fun _ => rfl) (fun _ => rfl)
  · exact Config.bindingRefines_complete frame.successful event leftReady rightReady action action
      value value (EventField.BindingRefines.refl _ _)

/-- Due binding expiry has one exact deterministic joint law when the pending
shadow remembers the original failure. Actual public miss markers are installed
on both sides; no completed-shadow or timely-inclusion premise is needed. -/
theorem expire_pending_failure
    (frame : Frame runtime leaks memory owner original repaired)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (ready : original.application.config.cut.Ready event)
    (rememberedAction : memory.shadow.actions event = some
      (cast (congrArg EventField.Action outputEq.symm) PublicationResult.failure))
    (rememberedValue : memory.shadow.values (.inr event) = some
      (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure))
    (entered : Nat) (activated : original.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ original.application.clock - entered) :
    let app := runtime.reactiveApplication leaks
    ∃ left right,
      original.environmentStep app (.application (.expire event)) = PMF.pure left ∧
      repaired.environmentStep app (.application (.expire event)) = PMF.pure right ∧
      Frame runtime leaks memory owner left right := by
  let app := runtime.reactiveApplication leaks
  have rightReady : repaired.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← frame.publicView, State.publicView_eventReady]
    exact ready
  have clocks : original.application.clock = repaired.application.clock :=
    congrArg PublicView.clock frame.publicView
  have enteredEq : original.application.activatedAt = repaired.application.activatedAt :=
    congrArg PublicView.activatedAt frame.publicView
  have rightActivated : repaired.application.activatedAt event = some entered := by
    rw [← enteredEq]
    exact activated
  have rightDue : runtime.deadline event ≤ repaired.application.clock - entered := by
    rwa [← clocks]
  let action : graph.Action event :=
    cast (congrArg EventField.Action outputEq.symm) PublicationResult.failure
  let value : (graph.outputLayout event).Value :=
    cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure
  let left : app.Execution :=
    { original with
      application := (original.application.complete event ready action value).markMissed event
      environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .application (.expire event)⟩] }
  let right : app.Execution :=
    { repaired with
      application := (repaired.application.complete event rightReady action value).markMissed event
      environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .application (.expire event)⟩] }
  have first : original.environmentStep app (.application (.expire event)) = PMF.pure left := by
    change ((environmentStep runtime original.application (.expire event)).map _).map _ = _
    rw [environmentStep_expire_bind_eq runtime original.application event ready entered
      activated due owner payload outputEq codeEq node, PMF.pure_map, PMF.pure_map]
  have second : repaired.environmentStep app (.application (.expire event)) = PMF.pure right := by
    change ((environmentStep runtime repaired.application (.expire event)).map _).map _ = _
    rw [environmentStep_expire_bind_eq runtime repaired.application event rightReady entered
      rightActivated rightDue owner payload outputEq codeEq node, PMF.pure_map, PMF.pure_map]
  have owned : graph.actor? event = some owner := by
    change (graph.nodes event).actor = some owner
    rw [← EventCode.actor_cast outputEq (graph.nodes event), codeEq]
    rfl
  have visible : graph.fieldVisibleTo owner (.inr event) := by
    change (graph.outputLayout event).VisibleTo owner
    rw [outputEq]
    rfl
  have paired := (frame.complete_matching_override event ready rightReady owned visible action value
    rememberedAction rememberedValue).markMissed event
  exact ⟨left, right, first, second, { paired with
    service := by
      change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
      rw [frame.service, frame.environment] }⟩

end Frame

end Vegas.EventGraphRuntime.BindingMemory
