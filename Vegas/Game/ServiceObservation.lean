/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ServiceInformation
import Vegas.Compile.EventGraphPolicyBacktranslation

/-! # Reconstructing native checkpoint observations

At active-player checkpoints, source observation equality determines the masked
semantic store, public default record and owner's original completion actions.
Sequential reachability determines completion order.
The remaining service and network fields are stated separately as operational
equalities; no information-fiber or posterior correspondence is assumed.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}

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

/-- Filtering chronological identities selects one owner's actual decisions
when all of its completed events contain decisions. -/
theorem ownCompletions_eventIds (who : Player)
    (history : List (serviceGraph setup mode).Completion)
    (decisions : ∀ completion ∈ history,
      (serviceGraph setup mode).actor? completion.event = some who →
        completion.decision.isSome) :
    ((serviceGraph setup mode).ownCompletions who history).map EventGraph.Completion.event =
      (history.map EventGraph.Completion.event).filter
        (fun event => (serviceGraph setup mode).actor? event = some who) := by
  have filters : history.filter (fun completion =>
        (serviceGraph setup mode).actor? completion.event = some who ∧
          completion.decision.isSome) =
      history.filter (fun completion =>
        (serviceGraph setup mode).actor? completion.event = some who) := by
    apply List.filter_congr
    intro completion member
    by_cases owned : (serviceGraph setup mode).actor? completion.event = some who
    · simp [owned, decisions completion member owned]
    · simp [owned]
  simp only [EventGraph.ownCompletions, filters, List.filter_map]
  rfl

/-- An active player's strategic actions are recoverable from source own-action
history and public event identities; execution-mode conversion loses none. -/
theorem ownCompletions_eq_of_decoded_eq (who : Player)
    (left right : (serviceGraph setup mode).Config)
    {leftInputs rightInputs : (serviceGraph setup mode).Inputs}
    (leftReachable : left.Reachable leftInputs) (rightReachable : right.Reachable rightInputs)
    (leftActive : who ∉ left.defaulted) (rightActive : who ∉ right.defaulted)
    (order : left.history.map EventGraph.Completion.event =
      right.history.map EventGraph.Completion.event)
    (decoded : decodeHistory setup.program
        (left.history.map (setup.eventGraph.fromModeCompletion mode)) who =
      decodeHistory setup.program
        (right.history.map (setup.eventGraph.fromModeCompletion mode)) who) :
    (serviceGraph setup mode).ownCompletions who left.history =
      (serviceGraph setup mode).ownCompletions who right.history := by
  let fromMode := setup.eventGraph.fromModeCompletion mode
  have encoding (config : (serviceGraph setup mode).Config)
      {inputs : (serviceGraph setup mode).Inputs} (reachable : config.Reachable inputs)
      (active : who ∉ config.defaulted) :
      encodeCompletions? setup.program
          (((serviceGraph setup mode).ownCompletions who config.history).map
            EventGraph.Completion.event)
          (decodeHistory setup.program (config.history.map fromMode) who) =
        some (((serviceGraph setup mode).ownCompletions who config.history).map fromMode) := by
    rw [ownCompletions_fromModeCompletion setup]
    let own := setup.eventGraph.ownCompletions who (config.history.map fromMode)
    have strategic : ∀ completion ∈ own, ∃ action sourceAction,
        completion.decision = some action ∧
          decodeEventAction setup.program completion.event action = some sourceAction := by
      intro completion member
      have filtered := List.mem_filter.mp member
      have selected := of_decide_eq_true filtered.2
      obtain ⟨action, chosen⟩ := Option.isSome_iff_exists.mp selected.2
      have ownerLaw := decodeEventAction_owner setup.program completion.event action
      have actorLaw : setup.eventGraph.actor? completion.event = some who :=
        selected.1
      change (toEventGraph setup.program).actor? completion.event = some who at actorLaw
      rw [eventOwner?_eq_actor setup.program completion.event, actorLaw] at ownerLaw
      cases decoded : decodeEventAction setup.program completion.event action with
      | none => simp [decoded] at ownerLaw
      | some sourceAction => exact ⟨action, sourceAction, chosen, decoded⟩
    have noDefault : ∀ completion ∈ own, completion.defaultEvent = none := by
      intro completion member
      change completion ∈ setup.eventGraph.ownCompletions who (config.history.map fromMode)
        at member
      rw [← ownCompletions_fromModeCompletion setup] at member
      obtain ⟨original, ownedMember, rfl⟩ := List.mem_map.mp member
      have filtered := List.mem_filter.mp ownedMember
      exact reachable.owned_defaultEvent_eq_none_of_active who active original filtered.1
        (of_decide_eq_true filtered.2).1
    have restored := encodeCompletions?_decodeCompletions_eq_some setup.program own
      strategic noDefault
    change encodeCompletions? setup.program (own.map EventGraph.Completion.event)
      (decodeCompletions setup.program own) = some own at restored
    have ids : own.map EventGraph.Completion.event =
        ((serviceGraph setup mode).ownCompletions who config.history).map
          EventGraph.Completion.event := by
      change (setup.eventGraph.ownCompletions who (config.history.map fromMode)).map _ = _
      rw [← ownCompletions_fromModeCompletion setup]
      rw [List.map_map]
      rfl
    rw [ids] at restored
    exact restored
  have ids : ((serviceGraph setup mode).ownCompletions who left.history).map
        EventGraph.Completion.event =
      ((serviceGraph setup mode).ownCompletions who right.history).map
        EventGraph.Completion.event := by
    rw [ownCompletions_eventIds setup who left.history
      (leftReachable.owned_decision_isSome_of_active who leftActive),
      ownCompletions_eventIds setup who right.history
        (rightReachable.owned_decision_isSome_of_active who rightActive), order]
  have first := encoding left leftReachable leftActive
  rw [ids, decoded] at first
  have mapped := Option.some.inj
    (first.symm.trans (encoding right rightReachable rightActive))
  have restored := congrArg (List.map (setup.eventGraph.toModeCompletion mode)) mapped
  simpa [fromMode, List.map_map, Function.comp_def] using restored

/-- At active source checkpoints with the same completion order, equal source
views determine the entire native semantic observation, including original owner
actions and public default history. Initialized secrets may be correlated. -/
theorem checkpoint_playerObservation_eq_of_order {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ) (offset : Nat)
    (covered : refs.CoversPrefix setup.program offset) (who : Player)
    (left right : Config Player L Γ)
    (nativeLeft nativeRight : (serviceGraph setup mode).Config)
    {leftInputs rightInputs : (serviceGraph setup mode).Inputs}
    (leftReachable : nativeLeft.Reachable leftInputs)
    (rightReachable : nativeRight.Reachable rightInputs)
    (leftActive : who ∉ nativeLeft.defaulted) (rightActive : who ∉ nativeRight.defaulted)
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
    (leftDefaults : nativeLeft.defaults = left.defaults)
    (rightDefaults : nativeRight.defaults = right.defaults)
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
    exact congrArg (encodeObservationStore who refs) (congrArg DecisionView.observation same)
  · apply ownCompletions_eq_of_decoded_eq setup who nativeLeft nativeRight
      leftReachable rightReachable leftActive rightActive order
    rw [leftHistory, rightHistory]
    exact congrArg DecisionView.history same
  · exact leftDefaults.trans ((congrArg DecisionView.defaults same).trans rightDefaults.symm)

end Vegas
