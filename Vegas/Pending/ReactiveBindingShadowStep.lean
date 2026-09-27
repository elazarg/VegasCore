/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingShadow

/-! # The actual owner response under hidden binding repair

The update is computed by the private implementation from its current own
input and original response. The theorem couples the actual atomic responses,
including the complete original own recall and arbitrary mistyped raw material.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

namespace BindingMemory

theorem repairResponse_submit_input (who : Player) (memory : BindingMemory runtime leaks)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (lengths : (right.recall who).length = memory.responses.length)
    (past : memory.restoreRecall runtime leaks (right.recall who) = left.recall who)
    (observed : memory.shadow.inputView runtime leaks
      (right.observe (runtime.reactiveApplication leaks) who) =
        left.observe (runtime.reactiveApplication leaks) who)
    (network : left.network = right.network)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (originalFresh : left.application.candidates.lookup (who, .prepared serial) = .fresh)
    (actualFresh : right.application.candidates.lookup (who, .prepared serial) = .fresh)
    (ready : right.application.config.cut.Ready event) :
    let app := runtime.reactiveApplication leaks
    let view := right.observe app who
    let original : app.Action :=
      ⟨some (.submit ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩)⟩
    let repaired := memory.repairResponse runtime leaks who view original
    let remembered : BindingMemory runtime leaks :=
      ⟨repaired.2, memory.responses ++ [(memory.shadow.inputView runtime leaks view, original)]⟩
    let before := left.respond app who original
    let after := right.respond app who repaired.1
    remembered.restoreRecall runtime leaks (after.recall who) = before.recall who ∧
      remembered.shadow.inputView runtime leaks (after.observe app who) =
        before.observe app who ∧
      (after.recall who).length = remembered.responses.length := by
  let app := runtime.reactiveApplication leaks
  let beforeView := right.observe app who
  let originalCall : Submission graph := ⟨.commitment event (who, .prepared serial), opening⟩
  let decoded := opening.bind (fun raw => raw.as? payload)
  let replacementOpening := match decoded with
    | none => some (⟨payload, L.someValue payload⟩ : Raw L)
    | some _ => opening
  let repairedCall : Submission graph :=
    ⟨.commitment event (who, .prepared serial), replacementOpening⟩
  let original : app.Action := ⟨some (.submit ⟨originalCall, .none⟩)⟩
  let repaired : app.Action := ⟨some (.submit ⟨repairedCall, .none⟩)⟩
  let catalog := memory.shadow.rememberCandidate (.prepared serial)
    (originalCall.candidateAfter who
      (memory.shadow.inputView runtime leaks beforeView).application.candidates (.prepared serial))
  let result : PublicationResult (L.Val payload) :=
    decoded.elim PublicationResult.failure PublicationResult.success
  let shadow := catalog.rememberCompletion event
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) result)
    (cast (congrArg EventGraph.EventField.Value outputEq.symm) result)
  have ownFresh : (memory.shadow.inputView runtime leaks beforeView).application.candidates
      (.prepared serial) = .fresh := by
    rw [observed]
    exact originalFresh
  have actualLocalFresh : beforeView.application.candidates (.prepared serial) = .fresh :=
    actualFresh
  have repairedEq : memory.repairResponse runtime leaks who beforeView original =
      (repaired, shadow) := by
    simp only [repairResponse, original, originalCall, node, ownFresh, actualLocalFresh,
      and_self, ↓reduceIte]
    change ((match decoded with
      | none => runtime.reactiveBinding leaks who event payload
          (.success (L.someValue payload)) serial
      | some _ => original), shadow) = (repaired, shadow)
    apply Prod.ext
    · dsimp only [repaired, repairedCall, replacementOpening]
      cases decoded <;> rfl
    · rfl
  let before := left.respond app who original
  let after := right.respond app who repaired
  let remembered : BindingMemory runtime leaks :=
    ⟨shadow, memory.responses ++ [(memory.shadow.inputView runtime leaks beforeView, original)]⟩
  change _ ∧ _ ∧ _
  change (let repaired := memory.repairResponse runtime leaks who beforeView original
    let remembered : BindingMemory runtime leaks :=
      ⟨repaired.2, memory.responses ++
        [(memory.shadow.inputView runtime leaks beforeView, original)]⟩
    remembered.restoreRecall runtime leaks ((right.respond app who repaired.1).recall who) =
      before.recall who ∧
    remembered.shadow.inputView runtime leaks ((right.respond app who repaired.1).observe app who) =
      before.observe app who ∧
    ((right.respond app who repaired.1).recall who).length = remembered.responses.length)
  rw [repairedEq]
  change remembered.restoreRecall runtime leaks (after.recall who) = before.recall who ∧
    remembered.shadow.inputView runtime leaks (after.observe app who) = before.observe app who ∧ _
  have submittedConfig : after.application.config = right.application.config := by
    change (submitStep (repairedCall.register right.application who) who
      repairedCall.packet).config = _
    rw [submitStep_config, (repairedCall.register_facts who right.application).1]
  have catalogEq := memory.shadow.rememberCandidate_submit_view runtime leaks
    left.application right.application who
      (congrArg ReactiveApplication.PlayerView.application observed) event serial opening
        replacementOpening
  change catalog.view (app.observePlayer after.application who) =
    app.observePlayer before.application who at catalogEq
  have shadowEq : shadow.view (app.observePlayer after.application who) =
      app.observePlayer before.application who := by
    rw [show shadow.view (app.observePlayer after.application who) =
      catalog.view (app.observePlayer after.application who) from
        catalog.rememberCompletion_pending runtime leaks after.application who event
          (submittedConfig ▸ ready) _ _]
    exact catalogEq
  have recallEq := memory.restoreRecall_submit runtime leaks left right who
    ⟨originalCall, .none⟩ ⟨repairedCall, .none⟩ lengths past observed network rfl
  refine ⟨recallEq, ?_, ?_⟩
  · change (⟨after.network.observe who, shadow.view (app.observePlayer after.application who),
      after.receipts⟩ : app.PlayerView) =
      ⟨before.network.observe who, app.observePlayer before.application who, before.receipts⟩
    have networkEq : before.network = after.network := by
      change (left.network.submit who ⟨originalCall.packet, none⟩).2 =
        (right.network.submit who ⟨repairedCall.packet, none⟩).2
      rw [network]
    rw [← networkEq, shadowEq]
    exact congrArg (fun receipts => (⟨before.network.observe who,
      app.observePlayer before.application who, receipts⟩ : app.PlayerView))
        (congrArg ReactiveApplication.PlayerView.receipts observed)
  · change (after.recall who).length = remembered.responses.length
    simp only [after, repaired, remembered, ReactiveApplication.Execution.respond,
      ↓reduceIte, List.length_append, List.length_singleton, lengths]

end BindingMemory

end Vegas.EventGraphRuntime
