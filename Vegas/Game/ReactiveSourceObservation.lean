/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReactiveSourceDecision
import Vegas.Compile.EventGraphPolicyBacktranslation

/-! # Source decision observations at chronological reactive prefixes -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem reactiveOriginal_event {graph : EventGraph Player L}
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion)) (receipts : List (MessageId Player × Bool))
    (completion : graph.Completion) :
    (runtime.reactiveOriginal leaks who history intentions receipts completion).event =
      completion.event := by
  classical
  cases node : nodeView graph completion.event with
  | sample => simp only [reactiveOriginal, node]
  | bind => simp only [reactiveOriginal, node]
  | resolve =>
      let select := fun (pair : (runtime.reactiveApplication leaks).PlayerEntry ×
          Option graph.Completion) => do
        let remembered ← pair.2
        if remembered.event = completion.event ∧
            runtime.ReactiveSilentDecision leaks who pair.1 remembered then some remembered
        else do
          let message ← pair.1.emitted
          if remembered.event = completion.event ∧
              message.payload.call.event? graph = some completion.event ∧
              (message.id, true) ∈ receipts ∧
              pair.1.action = runtime.reactiveDecision leaks who remembered.event
                remembered.action pair.1.beforeView.application then some remembered
          else none
      let candidates := (history.zip intentions).filterMap select
      have sameEvent : ∀ remembered ∈ candidates, remembered.event = completion.event := by
        intro remembered member
        obtain ⟨⟨entry, saved⟩, _, selected⟩ := List.mem_filterMap.mp member
        cases saved with
        | none => simp [select] at selected
        | some intention =>
            simp only [select, Option.bind_eq_bind, Option.bind_some] at selected
            split at selected
            · rename_i authentic
              cases Option.some.inj selected
              exact authentic.1
            · cases emitted : entry.emitted with
              | none => simp [emitted] at selected
              | some message =>
                  simp only [emitted, Option.bind_some] at selected
                  split at selected
                  · rename_i accepted
                    cases Option.some.inj selected
                    exact accepted.1
                  · cases selected
      simp only [reactiveOriginal, node]
      change (candidates.head?.getD completion).event = completion.event
      cases selected : candidates.head? with
      | none => rfl
      | some remembered =>
          exact sameEvent remembered (List.mem_of_mem_head? (by simp [selected]))

/-- The full normalized reactive decision observation is the constructive
encoding of its source observation and original own-action recall. Prefix and
store agreement are operational invariants; no observation equality is assumed. -/
theorem encodeDecisionView?_originalReactiveSourceRecall
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (runtime : EventGraphRuntime (toEventGraph whole))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (toEventGraph whole)))
    {Γ : SourceCtx Player L} (refs : ContextRefs (graphLayout whole) Γ)
    (offset : Nat) (covered : refs.CoversPrefix whole offset)
    (inputs : (toEventGraph whole).Inputs)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (reachable : execution.application.config.Reachable inputs)
    (ordered : execution.application.config.cut.IsPrefix offset)
    (source : State L Γ) (agree : refs.Agrees source execution.application.config.store)
    (intentions : List (Option (toEventGraph whole).Completion))
    (event : Fin (eventCount whole)) (ready : execution.application.config.cut.Ready event)
    (who : Player) (actor : (toEventGraph whole).actor? event = some who) :
    encodeDecisionView? whole refs who event
        (sourceObserve who source,
          originalReactiveSourceRecall whole runtime leaks who execution intentions) =
      some ((toEventGraph whole).normalizeObservation event who
        { (toEventGraph whole).playerObserve who execution.application.config with
          ownActions := ((toEventGraph whole).ownCompletions who
            execution.application.config.history).map
              (runtime.reactiveOriginal leaks who (execution.recall who) intentions
                execution.receipts) }) := by
  let graph := toEventGraph whole
  let physical := graph.ownCompletions who execution.application.config.history
  let original := physical.map
    (runtime.reactiveOriginal leaks who (execution.recall who) intentions execution.receipts)
  have originalIds : original.map EventGraph.Completion.event =
      graph.prefixSchema.ownHistory event := by
    have same : original.map EventGraph.Completion.event =
        physical.map EventGraph.Completion.event := by
      simp only [original, List.map_map]
      apply List.map_congr_left
      intro completion _
      exact reactiveOriginal_event runtime leaks who (execution.recall who) intentions
        execution.receipts completion
    rw [same]
    exact (toEventGraph_barrierOrdered whole).informationDiscipline.ready_ownEventIds
      reachable ready actor
  have strategic : ∀ completion ∈ original,
      ∃ sourceAction,
        decodeEventAction whole completion.event completion.action = some sourceAction := by
    intro completion member
    obtain ⟨physicalCompletion, retained, rfl⟩ := List.mem_map.mp member
    have filtered := List.mem_filter.mp retained
    have originalEvent := reactiveOriginal_event runtime leaks who (execution.recall who)
      intentions execution.receipts physicalCompletion
    have ownerLaw := decodeEventAction_owner whole _
      (runtime.reactiveOriginal leaks who (execution.recall who) intentions execution.receipts
        physicalCompletion).action
    have actualOwner : graph.actor? physicalCompletion.event = some who :=
      of_decide_eq_true filtered.2
    have sourceOwner : eventOwner? whole
        (runtime.reactiveOriginal leaks who (execution.recall who) intentions execution.receipts
          physicalCompletion).event = some who := by
      calc
        _ = (toEventGraph whole).actor? _ := eventOwner?_eq_actor whole _
        _ = some who := (congrArg graph.actor? originalEvent).trans actualOwner
    rw [sourceOwner] at ownerLaw
    obtain ⟨sourceAction, decoded, _⟩ := Option.map_eq_some_iff.mp ownerLaw
    exact ⟨sourceAction, decoded⟩
  have historyEncoded : encodeCompletions? whole (graph.prefixSchema.ownHistory event)
      (decodeCompletions whole original) = some original := by
    have inverse := encodeCompletions?_decodeCompletions_eq_some whole original strategic
    have transport := congrArg
      (fun ids : List (Fin (eventCount whole)) =>
        encodeCompletions? whole ids (decodeCompletions whole original)) originalIds
    exact transport.symm.trans inverse
  have storeEncoded := encodeObservationStore_eq_playerStore_of_prefix whole refs offset covered
    execution.application.config ordered source agree who
  change encodeDecisionView? whole refs who event
    (sourceObserve who source, decodeCompletions whole original) =
    some (graph.normalizeObservation event who
      { graph.playerObserve who execution.application.config with ownActions := original })
  unfold encodeDecisionView?
  change (encodeCompletions? whole (graph.prefixSchema.ownHistory event)
    (decodeCompletions whole original) >>= fun ownActions =>
      some ({ completionOrder := graph.rankPrefix event,
              store := encodeObservationStore who refs (sourceObserve who source),
              ownActions := ownActions } : graph.PlayerObservation who)) = _
  rw [historyEncoded]
  simp only [Option.bind_eq_bind, Option.bind_some]
  apply congrArg some
  apply EventGraph.PlayerObservation.ext graph
  · rfl
  · exact storeEncoded
  · rfl

end Vegas
