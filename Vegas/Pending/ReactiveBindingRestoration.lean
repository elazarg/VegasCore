/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingShadowStep
import Vegas.Pending.ReactiveUnusableBinding

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

namespace BindingMemory

/-- The complete private repair step: choose the original raw binding using
reconstructed input, submit a valid replacement under the same opaque handle,
then include that envelope. The stored memory reconstructs the original next
own input and response history. -/
theorem repairResponse_include_input (who : Player) (memory : BindingMemory runtime leaks)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (lengths : (right.recall who).length = memory.responses.length)
    (past : memory.restoreRecall runtime leaks (right.recall who) = left.recall who)
    (observed : memory.shadow.inputView runtime leaks
      (right.observe (runtime.reactiveApplication leaks) who) =
        left.observe (runtime.reactiveApplication leaks) who)
    (network : left.network = right.network)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (originalFresh : left.application.candidates.lookup (who, .prepared serial) = .fresh)
    (actualFresh : right.application.candidates.lookup (who, .prepared serial) = .fresh)
    (ready : left.application.config.cut.Ready event)
    (timely : left.application.WithinDeadline runtime event)
    (vacant : left.application.accepted (.inr event) = none)
    (unused : left.application.HandleUnused (who, .prepared serial))
    (serials : left.network.SerialsBeforeNext) :
    let app := runtime.reactiveApplication leaks
    let view := right.observe app who
    let original : app.Action :=
      ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩
    let repaired := memory.repairResponse runtime leaks who view original
    let remembered : BindingMemory runtime leaks :=
      ⟨repaired.2, memory.responses ++ [(memory.shadow.inputView runtime leaks view, original)]⟩
    let id := (who, left.network.nextSerial who)
    let before := (left.respond app who original).includePending app id
    let after := (right.respond app who repaired.1).includePending app id
    remembered.restoreRecall runtime leaks (after.recall who) = before.recall who ∧
      remembered.shadow.inputView runtime leaks (after.observe app who) =
        before.observe app who ∧
      (after.recall who).length = remembered.responses.length := by
  let app := runtime.reactiveApplication leaks
  let view := right.observe app who
  let originalCall : Submission graph := ⟨.commitment event (who, .prepared serial), opening⟩
  let replacementOpening := match opening.bind (fun raw => raw.as? payload) with
    | none => some (⟨payload, L.someValue payload⟩ : Raw L)
    | some _ => opening
  let repairedCall : Submission graph :=
    ⟨.commitment event (who, .prepared serial), replacementOpening⟩
  let original : app.Action := ⟨some ⟨originalCall, .none⟩⟩
  let repaired := memory.repairResponse runtime leaks who view original
  let remembered : BindingMemory runtime leaks :=
    ⟨repaired.2, memory.responses ++ [(memory.shadow.inputView runtime leaks view, original)]⟩
  let before := left.respond app who original
  let after := right.respond app who repaired.1
  let id := (who, left.network.nextSerial who)
  have visible : left.application.publicView = right.application.publicView :=
    (congrArg (fun view : app.PlayerView => view.application.publicView) observed).symm
  have ready' : right.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← visible, State.publicView_eventReady]
    exact ready
  have input := memory.repairResponse_submit_input runtime leaks who left right lengths past
    observed network event payload outputEq codeEq node serial opening originalFresh actualFresh
      ready'
  change remembered.restoreRecall runtime leaks (after.recall who) = before.recall who ∧
    remembered.shadow.inputView runtime leaks (after.observe app who) = before.observe app who ∧
      (after.recall who).length = remembered.responses.length at input
  have ownFresh : (memory.shadow.inputView runtime leaks view).application.candidates
      (.prepared serial) = .fresh := by
    rw [observed]
    exact originalFresh
  have localFresh : view.application.candidates (.prepared serial) = .fresh := actualFresh
  have afterAction : repaired.1 = ⟨some ⟨repairedCall, .none⟩⟩ := by
    cases decoded : opening.bind (fun raw => raw.as? payload) with
    | none =>
        rw [memory.repairResponse_unusable runtime leaks who view event payload outputEq codeEq
          node serial opening ownFresh actualFresh decoded]
        simp only [repairedCall, replacementOpening, decoded]
        rfl
    | some value =>
        rw [memory.repairResponse_usable runtime leaks who view event payload outputEq codeEq
          node serial opening ownFresh actualFresh value decoded]
        simp only [repairedCall, replacementOpening, decoded]
  have networkEq : before.network = after.network := by
    dsimp only [before, after]
    rw [afterAction]
    simp only [app, original, ReactiveApplication.Execution.respond,
      reactiveApplication_packet_none, network, visible]
    rfl
  have found : before.network.lookup id =
      some ⟨id, ⟨.commitment event (who, .prepared serial), none, some ⟨event⟩⟩⟩ :=
    respond_submit_lookup_of_ready runtime leaks left who originalCall serials event rfl ready
  have configEq : before.application.config = left.application.config := by
    change (submitStep (originalCall.register left.application who) who
      originalCall.packet).config = _
    rw [submitStep_config, (originalCall.register_facts who left.application).1]
  have publicEq : before.application.publicView = left.application.publicView := by
    change (submitStep (originalCall.register left.application who) who
      originalCall.packet).publicView = _
    rw [submitStep_publicView, (originalCall.register_facts who left.application).2]
  have beforeReady : before.application.config.cut.Ready event := by rwa [configEq]
  have beforeTimely : before.application.WithinDeadline runtime event := by
    unfold State.WithinDeadline
    rw [show before.application.clock = left.application.clock from
      congrArg PublicView.clock publicEq,
      show before.application.activatedAt = left.application.activatedAt from
        congrArg PublicView.activatedAt publicEq]
    exact timely
  have accepted := congrArg PublicView.accepted publicEq
  have beforeVacant : before.application.accepted (.inr event) = none :=
    (congrFun accepted (.inr event)).trans vacant
  have beforeUnused : before.application.HandleUnused (who, .prepared serial) := by
    intro field associated
    exact unused field ((congrFun accepted field).symm.trans associated)
  have beforeFixed : before.application.candidates.lookup (who, .prepared serial) ≠ .fresh :=
    submitStep_commitment_fixed _ who event (.prepared serial)
  have afterFixed : after.application.candidates.lookup (who, .prepared serial) ≠ .fresh := by
    dsimp only [after]
    rw [afterAction]
    exact submitStep_commitment_fixed _ who event (.prepared serial)
  have result : before.application.bindingResult (who, .prepared serial) payload =
      (opening.bind fun raw => raw.as? payload).elim .failure PublicationResult.success :=
    runtime.submitted_bindingResult leaks left who event payload serial opening originalFresh
  have actionMemory : remembered.shadow.actions event = some
      (cast (congrArg EventField.Action outputEq.symm)
        (before.application.bindingResult (who, .prepared serial) payload)) := by
    simp only [remembered, repaired, repairResponse, original, originalCall, node, ownFresh,
      localFresh, and_self, ↓reduceIte, result, BindingShadow.rememberCompletion,
      Function.update_self]
  have valueMemory : remembered.shadow.values (.inr event) = some
      (cast (congrArg EventField.Value outputEq.symm)
        (before.application.bindingResult (who, .prepared serial) payload)) := by
    simp only [remembered, repaired, repairResponse, original, originalCall, node, ownFresh,
      localFresh, and_self, ↓reduceIte, result, BindingShadow.rememberCompletion,
      Function.update_self]
  have included := remembered.shadow.include_binding_input runtime leaks before after who
    input.2.1 networkEq event payload outputEq codeEq node id (who, .prepared serial) rfl rfl
      found beforeReady beforeTimely beforeVacant beforeUnused beforeFixed afterFixed
        actionMemory valueMemory
  change remembered.restoreRecall runtime leaks ((after.includePending app id).recall who) =
      (before.includePending app id).recall who ∧
    remembered.shadow.inputView runtime leaks ((after.includePending app id).observe app who) =
      (before.includePending app id).observe app who ∧
    ((after.includePending app id).recall who).length = remembered.responses.length
  have leftRecall : (before.includePending app id).recall = before.recall := by
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending, found]
  have rightRecall : (after.includePending app id).recall = after.recall := by
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      networkEq ▸ found]
  rw [leftRecall, rightRecall]
  exact ⟨input.1, included, input.2.2⟩

end BindingMemory

end Vegas.EventGraphRuntime
