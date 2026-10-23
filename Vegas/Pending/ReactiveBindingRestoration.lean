/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveBindingShadowStep

/-! # Owner reconstruction through commitment inclusion

The private reconstruction recorded when a commitment is submitted becomes
observable only when that same commitment is included. This lemma uses the
actual pending envelope and handler; it covers arbitrary earlier repairs.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

namespace BindingShadow

omit [DecidableEq Player] in
theorem rememberCompletion_eq_self (memory : BindingShadow graph)
    (event : graph.EventId) (action : graph.Action event)
    (value : (graph.outputLayout event).Value)
    (rememberedAction : memory.actions event = some action)
    (rememberedValue : memory.values (.inr event) = some value) :
    memory.rememberCompletion event action value = memory := by
  classical
  cases memory with
  | mk values actions candidates =>
      simp only [rememberCompletion, BindingShadow.mk.injEq]
      change values (.inr event) = some value at rememberedValue
      change actions event = some action at rememberedAction
      rw [← rememberedValue, ← rememberedAction]
      simp only [Function.update_eq_self, and_self]

/-- The owner sees its original typed binding result and action after actual
inclusion. The same public receipt and network observation remain visible. -/
theorem include_binding_input (memory : BindingShadow graph)
    (left right : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (observed : memory.inputView runtime leaks
      (right.observe (runtime.reactiveApplication leaks) who) =
        left.observe (runtime.reactiveApplication leaks) who)
    (network : left.network = right.network)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (id : MessageId Player) (candidate : Handle graph)
    (sender : id.1 = who) (owned : candidate.1 = who)
    (found : left.network.lookup id = some ⟨id, ⟨.commitment event candidate, none, some ⟨event⟩⟩⟩)
    (ready : left.application.config.cut.Ready event)
    (timely : left.application.WithinDeadline runtime event)
    (vacant : left.application.accepted (.inr event) = none)
    (unused : left.application.HandleUnused candidate)
    (leftFixed : left.application.candidates.lookup candidate ≠ .fresh)
    (rightFixed : right.application.candidates.lookup candidate ≠ .fresh)
    (rememberedAction : memory.actions event = some
      (cast (congrArg EventField.Action outputEq.symm)
        (left.application.bindingResult candidate payload)))
    (rememberedValue : memory.values (.inr event) = some
      (cast (congrArg EventField.Value outputEq.symm)
        (left.application.bindingResult candidate payload))) :
    memory.inputView runtime leaks
      ((right.includePending (runtime.reactiveApplication leaks) id).observe
        (runtime.reactiveApplication leaks) who) =
      (left.includePending (runtime.reactiveApplication leaks) id).observe
        (runtime.reactiveApplication leaks) who := by
  let app := runtime.reactiveApplication leaks
  have application := congrArg ReactiveApplication.PlayerView.application observed
  have visible : left.application.publicView = right.application.publicView :=
    (congrArg PlayerView.publicView application).symm
  have receipts : left.receipts = right.receipts :=
    (congrArg ReactiveApplication.PlayerView.receipts observed).symm
  have accepted := congrArg PublicView.accepted visible
  have ready' : right.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← visible, State.publicView_eventReady]
    exact ready
  have timely' : right.application.WithinDeadline runtime event := by
    unfold State.WithinDeadline at timely ⊢
    rw [← show left.application.clock = right.application.clock from
      congrArg PublicView.clock visible,
      ← show left.application.activatedAt = right.application.activatedAt from
        congrArg PublicView.activatedAt visible]
    exact timely
  have vacant' : right.application.accepted (.inr event) = none :=
    (congrFun accepted (.inr event)).symm.trans vacant
  have unused' : right.application.HandleUnused candidate := by
    intro field associated
    exact unused field ((congrFun accepted field).trans associated)
  have found' : right.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, none, some ⟨event⟩⟩⟩ := network ▸ found
  have handled := runtime.handle_commitment_eq left.application id event candidate who payload
    outputEq codeEq node ready timely sender owned vacant unused
  have handled' := runtime.handle_commitment_eq right.application id event candidate who payload
    outputEq codeEq node ready' timely' sender owned vacant' unused'
  have nextPublic := runtime.reactive_include_binding_public_congr leaks left right network
    visible who event payload outputEq codeEq node id candidate none sender owned found ready
      timely vacant unused
  have leftCandidates := runtime.reactive_include_fixed_binding_candidates leaks left id
    event candidate none found leftFixed
  have rightCandidates := runtime.reactive_include_fixed_binding_candidates leaks right id
    event candidate none found' rightFixed
  have restores := memory.rememberCompletion_observation who left.application.config
    right.application.config
    (congrArg (fun view : PlayerView graph => view.observation.store) application)
    (congrArg (fun view : PlayerView graph => view.observation.ownActions) application)
    event ready ready' (by
      change (graph.nodes event).actor = some who
      rw [← EventCode.actor_cast outputEq (graph.nodes event), codeEq]
      rfl) (by
      change (graph.outputLayout event).VisibleTo who
      rw [outputEq]
      rfl)
    (cast (congrArg EventField.Action outputEq.symm)
      (left.application.bindingResult candidate payload))
    (cast (congrArg EventField.Action outputEq.symm)
      (right.application.bindingResult candidate payload))
    (cast (congrArg EventField.Value outputEq.symm)
      (left.application.bindingResult candidate payload))
    (cast (congrArg EventField.Value outputEq.symm)
      (right.application.bindingResult candidate payload))
  rw [memory.rememberCompletion_eq_self event _ _ rememberedAction rememberedValue] at restores
  have leftConfig : (left.includePending app id).application.config =
      left.application.config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm)
          (left.application.bindingResult candidate payload))
        (cast (congrArg EventField.Value outputEq.symm)
          (left.application.bindingResult candidate payload)) := by
    simp only [app, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, reactiveApplication_handle, WitnessedPacket.tokenValid_commitment, ite_true,
      handled, Option.getD_some, State.complete]
  have rightConfig : (right.includePending app id).application.config =
      right.application.config.complete event ready'
        (cast (congrArg EventField.Action outputEq.symm)
          (right.application.bindingResult candidate payload))
        (cast (congrArg EventField.Value outputEq.symm)
          (right.application.bindingResult candidate payload)) := by
    simp only [app, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found', reactiveApplication_handle, WitnessedPacket.tokenValid_commitment, ite_true,
      handled', Option.getD_some, State.complete]
  have nextObservation :
      (memory.view (app.observePlayer (right.includePending app id).application who)).observation =
        (app.observePlayer (left.includePending app id).application who).observation := by
    apply EventGraph.PlayerObservation.ext
    · exact (congrArg (fun view : PublicView graph => view.observation.completionOrder)
        nextPublic).symm
    · change memory.store (graph.playerObserve who
        (right.includePending app id).application.config).store =
          (graph.playerObserve who (left.includePending app id).application.config).store
      rw [leftConfig, rightConfig]
      exact restores.1
    · change (graph.playerObserve who
        (right.includePending app id).application.config).ownActions.map memory.completion =
          (graph.playerObserve who (left.includePending app id).application.config).ownActions
      rw [leftConfig, rightConfig]
      exact restores.2
  have nextApplication : memory.view (app.observePlayer
      (right.includePending app id).application who) =
        app.observePlayer (left.includePending app id).application who := by
    have catalog : (fun slot => (memory.candidates slot).getD
        ((right.includePending app id).application.candidates.lookup (who, slot))) =
        (fun slot => (left.includePending app id).application.candidates.lookup (who, slot)) := by
      rw [leftCandidates, rightCandidates]
      exact congrArg PlayerView.candidates application
    exact congr (congr (congrArg (PlayerView.mk who) nextPublic.symm)
      nextObservation) catalog
  change (⟨(right.includePending app id).network.observe who,
    memory.view (app.observePlayer (right.includePending app id).application who),
      (right.includePending app id).receipts⟩ : app.PlayerView) = _
  rw [nextApplication]
  have nextNetwork : (left.includePending app id).network =
      (right.includePending app id).network := by
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found', network]
  have nextReceipts : (left.includePending app id).receipts =
      (right.includePending app id).receipts := by
    simp only [app, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, found', reactiveApplication_handle, WitnessedPacket.tokenValid_commitment, ite_true,
      handled, handled', Option.isSome_some, receipts]
  rw [← nextNetwork, ← nextReceipts]
  rfl

end BindingShadow

end Vegas.EventGraphRuntime
