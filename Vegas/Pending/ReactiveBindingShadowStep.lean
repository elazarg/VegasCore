/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingShadow

/-! # The actual owner response under hidden binding repair

The update is computed by the private implementation from its current own
input and original response. The theorem couples the actual atomic responses,
including the complete original own recall and arbitrary mistyped raw material.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type}
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

namespace BindingShadow

/-- At a completed boundary, completion overrides name completed events.
A pending unusable failure override satisfies this invariant once actual
inclusion or expiry completes its event. -/
def CompletedAt (memory : BindingShadow graph) (config : graph.Config) : Prop :=
  ∀ event, (memory.actions event).isSome ∨ (memory.values (.inr event)).isSome →
    event ∈ config.cut.completed

theorem completedAt_empty (config : graph.Config) :
    (empty : BindingShadow graph).CompletedAt config := by
  intro event present
  rcases present with present | present <;> cases present

/-- A completed-boundary shadow remains valid as the completed cut grows. -/
theorem CompletedAt.mono {memory : BindingShadow graph} {before after : graph.Config}
    (past : memory.CompletedAt before)
    (completed : before.cut.completed ⊆ after.cut.completed) :
    memory.CompletedAt after := by
  intro event present
  exact completed (past event present)

theorem CompletedAt.rememberCandidate {memory : BindingShadow graph} {config : graph.Config}
    (past : memory.CompletedAt config) (slot : CandidateSlot graph)
    (value : CommitmentCandidate (Raw L)) :
    (memory.rememberCandidate slot value).CompletedAt config := past

theorem CompletedAt.complete {memory : BindingShadow graph} {config : graph.Config}
    (past : memory.CompletedAt config) (event : graph.EventId) (ready : config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    memory.CompletedAt (config.complete event ready action value) := by
  intro query present
  rw [Config.complete_cut, EventOrder.Cut.mem_complete]
  exact Or.inr (past query present)

theorem CompletedAt.rememberCompletion_of_completed
    {memory : BindingShadow graph} {config : graph.Config}
    (past : memory.CompletedAt config) (event : graph.EventId)
    (completed : event ∈ config.cut.completed)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    (memory.rememberCompletion event action value).CompletedAt config := by
  classical
  intro query present
  by_cases same : query = event
  · exact same ▸ completed
  · apply past query
    simpa only [BindingShadow.rememberCompletion, Function.update_of_ne same,
      Function.update_of_ne (Sum.inr_injective.ne same)] using present

theorem CompletedAt.rememberCompletion {memory : BindingShadow graph} {config : graph.Config}
    (past : memory.CompletedAt config) (event : graph.EventId) (ready : config.cut.Ready event)
    (originalAction actualAction : graph.Action event)
    (originalValue actualValue : (graph.outputLayout event).Value) :
    (memory.rememberCompletion event originalAction originalValue).CompletedAt
      (config.complete event ready actualAction actualValue) := by
  classical
  intro query present
  rw [Config.complete_cut, EventOrder.Cut.mem_complete]
  by_cases same : query = event
  · exact Or.inl same
  · apply Or.inr
    apply past query
    simpa only [BindingShadow.rememberCompletion, Function.update_of_ne same,
      Function.update_of_ne (Sum.inr_injective.ne same)] using present

theorem CompletedAt.ready_none {memory : BindingShadow graph} {config : graph.Config}
    (past : memory.CompletedAt config) (event : graph.EventId) (ready : config.cut.Ready event) :
    memory.actions event = none ∧ memory.values (.inr event) = none := by
  constructor
  · cases stored : memory.actions event with
    | none => rfl
    | some action =>
        exact False.elim (ready.1 (past event (Or.inl (by simp only [stored]; rfl))))
  · cases stored : memory.values (.inr event) with
    | none => rfl
    | some value =>
        exact False.elim (ready.1 (past event (Or.inr (by simp only [stored]; rfl))))


end BindingShadow

variable [DecidableEq Player]

namespace BindingMemory

/-- The actual fresh-binding repair memory is valid at every later completed
boundary containing the addressed event. Usable responses add no completion
override; unusable responses add only that event's failure override. -/
theorem repairResponse_completedAt (who : Player) (memory : BindingMemory runtime leaks)
    (actual : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (originalFresh : (memory.shadow.inputView runtime leaks actual).application.candidates
      (.prepared serial) = .fresh)
    (actualFresh : actual.application.candidates (.prepared serial) = .fresh)
    (before after : graph.Config) (past : memory.shadow.CompletedAt before)
    (advanced : before.cut.completed ⊆ after.cut.completed)
    (completed : event ∈ after.cut.completed) :
    (memory.repairResponse runtime leaks who actual
      ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩).2.CompletedAt
        after := by
  cases decoded : opening.bind (fun raw => raw.as? payload) with
  | none =>
      simp only [repairResponse, node, originalFresh, actualFresh, decoded, and_self, ↓reduceIte]
      exact ((past.mono advanced).rememberCandidate _ _).rememberCompletion_of_completed
        event completed _ _
  | some value =>
      simp only [repairResponse, node, originalFresh, actualFresh, decoded, and_self, ↓reduceIte]
      exact (past.mono advanced).rememberCandidate _ _

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
      ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩
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
  let original : app.Action := ⟨some ⟨originalCall, .none⟩⟩
  let repaired : app.Action := ⟨some ⟨repairedCall, .none⟩⟩
  let catalog := memory.shadow.rememberCandidate (.prepared serial)
    (originalCall.candidateAfter who
      (memory.shadow.inputView runtime leaks beforeView).application.candidates (.prepared serial))
  let shadow := match decoded with
    | none => catalog.rememberCompletion event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) PublicationResult.failure)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm) PublicationResult.failure)
    | some _ => catalog
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
    change (match decoded with
      | none => (runtime.reactiveBinding leaks who event payload
          (.success (L.someValue payload)) serial,
          catalog.rememberCompletion event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) PublicationResult.failure)
            (cast (congrArg EventGraph.EventField.Value outputEq.symm) PublicationResult.failure))
      | some _ => (original, catalog)) = (repaired, shadow)
    cases decodedEq : decoded <;>
      simp only [repaired, repairedCall, replacementOpening, shadow, decodedEq] <;> rfl
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
    cases decodedEq : decoded with
    | none =>
        rw [show shadow.view (app.observePlayer after.application who) =
          catalog.view (app.observePlayer after.application who) from
            by simpa only [shadow, decodedEq] using
              catalog.rememberCompletion_pending runtime leaks after.application who event
                (submittedConfig ▸ ready)
                (cast (congrArg EventGraph.EventField.Action outputEq.symm)
                  PublicationResult.failure)
                (cast (congrArg EventGraph.EventField.Value outputEq.symm)
                  PublicationResult.failure)]
        exact catalogEq
    | some value =>
        simpa only [shadow, decodedEq] using catalogEq
  have publicEq : right.application.publicView = left.application.publicView :=
    congrArg (fun view : app.PlayerView => view.application.publicView) observed
  have packetEq : (⟨originalCall, .none⟩ : WitnessedSubmission graph).emit
        (app.submit left.application who ⟨originalCall, .none⟩) who (left.network.known who) =
      (⟨repairedCall, .none⟩ : WitnessedSubmission graph).emit
        (app.submit right.application who ⟨repairedCall, .none⟩) who
          (right.network.known who) := by
    change WitnessedPacket.mk originalCall.packet none
        ((app.submit left.application who ⟨originalCall, .none⟩).publicView.tokenFor
          originalCall.packet) =
      WitnessedPacket.mk repairedCall.packet none
        ((app.submit right.application who ⟨repairedCall, .none⟩).publicView.tokenFor
          repairedCall.packet)
    rw [reactiveApplication_submit_publicView, reactiveApplication_submit_publicView, publicEq]
  have recallEq := memory.restoreRecall_submit runtime leaks left right who
    ⟨originalCall, .none⟩ ⟨repairedCall, .none⟩ lengths past observed network packetEq
  refine ⟨recallEq, ?_, ?_⟩
  · change (⟨after.network.observe who, shadow.view (app.observePlayer after.application who),
      after.receipts⟩ : app.PlayerView) =
      ⟨before.network.observe who, app.observePlayer before.application who, before.receipts⟩
    have networkEq : before.network = after.network := by
      exact congrArg₂ (fun current packet => (current.submit who packet).2) network packetEq
    rw [← networkEq, shadowEq]
    exact congrArg (fun receipts => (⟨before.network.observe who,
      app.observePlayer before.application who, receipts⟩ : app.PlayerView))
        (congrArg ReactiveApplication.PlayerView.receipts observed)
  · change (after.recall who).length = remembered.responses.length
    simp only [after, repaired, remembered, ReactiveApplication.Execution.respond,
      ↓reduceIte, List.length_append, List.length_singleton, lengths]

end BindingMemory

end Vegas.EventGraphRuntime
