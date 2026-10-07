/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceInformation
import Vegas.Compile.EventGraphPolicyBacktranslation
import Vegas.Pending.EventInitialObservation

/-! # Reconstructing native checkpoint observations

Source observation equality determines the masked semantic store and the owner's
original completion actions. Sequential reachability determines completion order.
The remaining service and network fields are stated separately as operational
equalities; no information-fiber or posterior correspondence is assumed.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}

/-- Every reachable sequential graph history follows source rank. -/
theorem reachable_rankPrefix {inputs : (graph setup).Inputs}
    {config : (graph setup).Config} (reachable : config.Reachable inputs) :
    EventGraph.RankPrefix config := by
  induction reachable with
  | initial => exact EventGraph.rankPrefix_initial _
  | step _ event ready action next supported ih =>
      exact EventGraph.rankPrefix_step ih event ready action
        (fun _ unfinished => setup.eventGraph.sequentialize_ready_le_unfinished _
          ready unfinished) supported

/-- At a prefix checkpoint the chronological identities contain exactly the
completed source ranks, independently of private inputs and strategic actions. -/
theorem checkpoint_completionOrder {inputs : (graph setup).Inputs}
    (config : (graph setup).Config) (reachable : config.Reachable inputs)
    (offset : Nat) (ordered : config.cut.IsPrefix offset) :
    config.history.map EventGraph.Completion.event =
      (List.finRange (graph setup).order.eventCount).filter (fun event => event.val < offset) := by
  apply (reachable_rankPrefix setup reachable).2.eq_of_mem_iff
    ((List.sortedLT_finRange (graph setup).order.eventCount).pairwise.filter _)
  intro event
  rw [config.history_exact, ordered.2]
  simp

/-- Reference coverage is unaffected by replacing the dependency order with
the sequential order used by the service. -/
theorem checkpoint_visible_coverage {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ) (offset : Nat)
    (covered : refs.CoversPrefix setup.program offset)
    (config : (serviceGraph setup mode).Config) (ordered : config.cut.IsPrefix offset)
    (who : Player) (field : (serviceGraph setup mode).Field)
    (absent : ¬ refs.CoversVisible who field) :
    (serviceGraph setup mode).playerStore who config.store field = none := by
  by_cases visible : (serviceGraph setup mode).fieldVisibleTo who field
  · rw [(serviceGraph setup mode).playerStore_of_visible who config.store field visible]
    cases field with
    | inl input =>
        obtain ⟨name, cell, source, found⟩ := covered.1 input
        exfalso
        apply absent
        refine ⟨name, cell, source, ?_, found⟩
        rw [cellVisibleTo_iff_fieldVisibleTo]
        change ((graphLayout setup.program) (.inl input)).VisibleTo who at visible
        rw [← found, (refs.get source).layout_eq] at visible
        exact visible
    | inr event =>
        by_cases earlier : event.val < offset
        · obtain ⟨name, cell, source, found⟩ := covered.2 event earlier
          exfalso
          apply absent
          refine ⟨name, cell, source, ?_, found⟩
          rw [cellVisibleTo_iff_fieldVisibleTo]
          change ((graphLayout setup.program) (.inr event)).VisibleTo who at visible
          rw [← found, (refs.get source).layout_eq] at visible
          exact visible
        · rw [EventGraph.Config.store_output]
          have unavailable : (config.outputs event).isSome = false := by
            rw [Bool.eq_false_iff]
            intro available
            exact earlier ((ordered.2 event).mp ((config.output_available event).mp available))
          cases output : config.outputs event with
          | none => rfl
          | some value => simp [output] at unavailable
  · exact (serviceGraph setup mode).playerStore_of_hidden who config.store field visible

theorem checkpoint_playerStore {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ) (offset : Nat)
    (covered : refs.CoversPrefix setup.program offset)
    (config : (serviceGraph setup mode).Config) (ordered : config.cut.IsPrefix offset)
    (source : State L Γ) (agree : refs.Agrees source config.store) (who : Player) :
    (serviceGraph setup mode).playerStore who config.store =
      encodeObservationStore who refs (sourceObserve who source) := by
  symm
  exact encodeObservationStore_eq_playerStore (graph := serviceGraph setup mode) who refs source
    config.store agree (checkpoint_visible_coverage setup refs offset covered config ordered who)

/-- Filtering chronological identities commutes with selecting one owner's
original completion actions. -/
theorem ownCompletions_eventIds (who : Player)
    (history : List (serviceGraph setup mode).Completion) :
    ((serviceGraph setup mode).ownCompletions who history).map EventGraph.Completion.event =
      (history.map EventGraph.Completion.event).filter
        (fun event => (serviceGraph setup mode).actor? event = some who) := by
  simp only [EventGraph.ownCompletions, List.filter_map]
  rfl

/-- Original strategic actions are recoverable from the source own-action
history and the public event identities; execution-mode conversion loses none
of those actions. -/
theorem ownCompletions_eq_of_decoded_eq (who : Player)
    (left right : List (serviceGraph setup mode).Completion)
    (order : left.map EventGraph.Completion.event = right.map EventGraph.Completion.event)
    (decoded : decodeHistory setup.program
        (left.map (setup.eventGraph.fromModeCompletion mode)) who =
      decodeHistory setup.program
        (right.map (setup.eventGraph.fromModeCompletion mode)) who) :
    (serviceGraph setup mode).ownCompletions who left = (serviceGraph setup mode).ownCompletions who
    right := by
  let fromMode := setup.eventGraph.fromModeCompletion mode
  have encoding (history : List (serviceGraph setup mode).Completion) :
      encodeCompletions? setup.program
          (((serviceGraph setup mode).ownCompletions who history).map EventGraph.Completion.event)
          (decodeHistory setup.program (history.map fromMode) who) =
        some (((serviceGraph setup mode).ownCompletions who history).map fromMode) := by
    rw [ownCompletions_fromModeCompletion setup]
    let own := setup.eventGraph.ownCompletions who (history.map fromMode)
    have strategic : ∀ completion ∈ own, ∃ sourceAction,
        decodeEventAction setup.program completion.event completion.action = some sourceAction := by
      intro completion member
      have filtered := List.mem_filter.mp member
      have ownerLaw := decodeEventAction_owner setup.program completion.event completion.action
      have actorLaw : setup.eventGraph.actor? completion.event = some who :=
        of_decide_eq_true filtered.2
      change (toEventGraph setup.program).actor? completion.event = some who at actorLaw
      rw [eventOwner?_eq_actor setup.program completion.event, actorLaw] at ownerLaw
      cases action : decodeEventAction setup.program completion.event completion.action with
      | none => simp [action] at ownerLaw
      | some sourceAction => exact ⟨sourceAction, rfl⟩
    have restored := encodeCompletions?_decodeCompletions_eq_some setup.program own strategic
    change encodeCompletions? setup.program (own.map EventGraph.Completion.event)
      (decodeCompletions setup.program own) = some own at restored
    have ids : own.map EventGraph.Completion.event =
        ((serviceGraph setup mode).ownCompletions who history).map EventGraph.Completion.event := by
      change (setup.eventGraph.ownCompletions who (history.map fromMode)).map _ = _
      rw [← ownCompletions_fromModeCompletion setup]
      rw [List.map_map]
      rfl
    rw [ids] at restored
    exact restored
  have ids : ((serviceGraph setup mode).ownCompletions who left).map EventGraph.Completion.event =
      ((serviceGraph setup mode).ownCompletions who right).map EventGraph.Completion.event := by
    rw [ownCompletions_eventIds, ownCompletions_eventIds, order]
  have first := encoding left
  rw [ids, decoded] at first
  have mapped := Option.some.inj (first.symm.trans (encoding right))
  have restored := congrArg (List.map (setup.eventGraph.toModeCompletion mode)) mapped
  simpa [fromMode, List.map_map, Function.comp_def] using restored

/-- At source checkpoints with the same completion order, equal source views
determine the entire native semantic observation, including original owner
actions. No independence between players' initialized secrets is required. -/
theorem checkpoint_playerObservation_eq_of_order {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ) (offset : Nat)
    (covered : refs.CoversPrefix setup.program offset) (who : Player)
    (left right : Config Player L Γ)
    (nativeLeft nativeRight : (serviceGraph setup mode).Config)
    (order : nativeLeft.history.map EventGraph.Completion.event =
      nativeRight.history.map EventGraph.Completion.event)
    (leftPrefix : nativeLeft.cut.IsPrefix offset)
    (rightPrefix : nativeRight.cut.IsPrefix offset)
    (leftStore : refs.Agrees left.state nativeLeft.store)
    (rightStore : refs.Agrees right.state nativeRight.store)
    (leftHistory : decodeHistory setup.program
        (nativeLeft.history.map (setup.eventGraph.fromModeCompletion mode)) = left.history)
    (rightHistory : decodeHistory setup.program
        (nativeRight.history.map (setup.eventGraph.fromModeCompletion mode)) = right.history)
    (same : left.view who = right.view who) :
    (serviceGraph setup mode).playerObserve who nativeLeft =
      (serviceGraph setup mode).playerObserve who nativeRight := by
  apply EventGraph.PlayerObservation.ext (serviceGraph setup mode)
  · exact order
  · change (serviceGraph setup mode).playerStore who nativeLeft.store =
      (serviceGraph setup mode).playerStore who nativeRight.store
    rw [checkpoint_playerStore setup refs offset covered nativeLeft leftPrefix left.state
      leftStore who, checkpoint_playerStore setup refs offset covered nativeRight rightPrefix
      right.state rightStore who]
    exact congrArg (encodeObservationStore who refs) (congrArg Prod.fst same)
  · apply ownCompletions_eq_of_decoded_eq setup who _ _ order
    rw [leftHistory, rightHistory]
    exact congrArg Prod.snd same

/-- At genuine source-ranked checkpoints of the sequential graph, equal source
views determine the entire native semantic observation: there the completion
order is the source rank order. -/
theorem checkpoint_playerObservation_eq {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ) (offset : Nat)
    (covered : refs.CoversPrefix setup.program offset) (who : Player)
    (left right : Config Player L Γ)
    (nativeLeft nativeRight : (graph setup).Config)
    {leftInputs rightInputs : (graph setup).Inputs}
    (leftReachable : nativeLeft.Reachable leftInputs)
    (rightReachable : nativeRight.Reachable rightInputs)
    (leftPrefix : nativeLeft.cut.IsPrefix offset)
    (rightPrefix : nativeRight.cut.IsPrefix offset)
    (leftStore : refs.Agrees left.state nativeLeft.store)
    (rightStore : refs.Agrees right.state nativeRight.store)
    (leftHistory : decodeHistory setup.program
        (nativeLeft.history.map (setup.eventGraph.fromModeCompletion .sequential)) = left.history)
    (rightHistory : decodeHistory setup.program
        (nativeRight.history.map (setup.eventGraph.fromModeCompletion .sequential)) = right.history)
    (same : left.view who = right.view who) :
    (graph setup).playerObserve who nativeLeft =
      (graph setup).playerObserve who nativeRight :=
  checkpoint_playerObservation_eq_of_order setup refs offset covered who left right nativeLeft
    nativeRight ((checkpoint_completionOrder setup nativeLeft leftReachable offset
      leftPrefix).trans (checkpoint_completionOrder setup nativeRight rightReachable offset
        rightPrefix).symm) leftPrefix rightPrefix leftStore rightStore leftHistory rightHistory
    same

/-- Initial candidate catalogues expose no additional distinctions once the
current semantic observation and preservation of the catalogue are known. -/
theorem checkpoint_candidates_eq (who : Player)
    (left right : EventGraphRuntime.State (serviceGraph setup mode))
    (leftCandidates : left.candidates =
      (EventGraphRuntime.State.initial left.config.inputs).candidates)
    (rightCandidates : right.candidates =
      (EventGraphRuntime.State.initial right.config.inputs).candidates)
    (same : (serviceGraph setup mode).playerObserve who left.config =
      (serviceGraph setup mode).playerObserve who right.config) :
    (fun slot => left.candidates.lookup (who, slot)) =
      fun slot => right.candidates.lookup (who, slot) := by
  rw [leftCandidates, rightCandidates]
  apply EventGraphRuntime.State.initial_candidates_eq_of_observation
  apply EventGraph.PlayerObservation.ext (serviceGraph setup mode)
  · rfl
  · apply (serviceGraph setup mode).playerStore_congr
    intro field visible
    cases field with
    | inl input =>
        exact EventGraph.store_eq_of_playerObserve_eq who left.config right.config
          same (.inl input) visible
    | inr event => rfl
  · rfl

/-- Assemble the actual native before-view from its semantic observation and
the service's public fields. The source execution induction must establish
the stated clock, activation, ledger, leak, and receipt equalities.
Own response recall is deliberately absent. -/
theorem checkpoint_observe_eq
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (who : Player) (left right : (serviceApplication setup mode deadline leaks).Execution)
    (same : (serviceGraph setup mode).playerObserve who left.application.config =
      (serviceGraph setup mode).playerObserve who right.application.config)
    (leftCandidates : left.application.candidates =
      (EventGraphRuntime.State.initial left.application.config.inputs).candidates)
    (rightCandidates : right.application.candidates =
      (EventGraphRuntime.State.initial right.application.config.inputs).candidates)
    (accepted : left.application.accepted = right.application.accepted)
    (clock : left.application.clock = right.application.clock)
    (activated : left.application.activatedAt = right.application.activatedAt)
    (ledger : left.network.ledger = right.network.ledger)
    (leaked : left.network.leaked who = right.network.leaked who)
    (receipts : left.receipts = right.receipts) :
    left.observe (serviceApplication setup mode deadline leaks) who = right.observe
        (serviceApplication setup mode deadline leaks) who := by
  have candidates := checkpoint_candidates_eq setup who left.application right.application
    leftCandidates rightCandidates same
  have publicObservation := EventGraph.publicObserve_eq_of_playerObserve_eq who
    left.application.config right.application.config same
  have publicView : left.application.publicView = right.application.publicView := by
    unfold EventGraphRuntime.State.publicView
    rw [publicObservation, accepted, clock, activated]
  change ReactiveApplication.PlayerView.mk
      ⟨left.network.leaked who, left.network.ledger⟩
      ⟨who, left.application.publicView,
        (serviceGraph setup mode).playerObserve who left.application.config,
        fun slot => left.application.candidates.lookup (who, slot)⟩ left.receipts =
    ReactiveApplication.PlayerView.mk
      ⟨right.network.leaked who, right.network.ledger⟩
      ⟨who, right.application.publicView,
        (serviceGraph setup mode).playerObserve who right.application.config,
        fun slot => right.application.candidates.lookup (who, slot)⟩ right.receipts
  rw [leaked, ledger, publicView, same, candidates, receipts]

end Vegas
