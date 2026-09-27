/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingRestoration

/-! # The domain of private binding reconstruction

Only the repaired player's private binding outputs and original binding actions
are overridden. Public samples and publication results continue to be read from
the actual execution. These are invariants of the existing private strategy,
not additional fields in the game state.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace BindingShadow

def OwnBindings (memory : BindingShadow graph) (who : Player) : Prop :=
  (∀ field, (memory.values field).isSome →
    ∃ event payload, field = .inr event ∧ graph.outputLayout event = .binding who payload) ∧
  (∀ event, (memory.actions event).isSome →
    ∃ payload, graph.outputLayout event = .binding who payload)

theorem ownBindings_empty (who : Player) : (empty : BindingShadow graph).OwnBindings who := by
  constructor <;> intro field present <;> cases present

theorem OwnBindings.rememberCandidate {memory : BindingShadow graph} {who : Player}
    (onlyBindings : memory.OwnBindings who) (slot : CandidateSlot graph)
    (candidate : CommitmentCandidate (Raw L)) :
    (memory.rememberCandidate slot candidate).OwnBindings who := onlyBindings

theorem OwnBindings.rememberCompletion {memory : BindingShadow graph} {who : Player}
    (onlyBindings : memory.OwnBindings who) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding who payload)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    (memory.rememberCompletion event action value).OwnBindings who := by
  classical
  constructor
  · intro field present
    by_cases selected : field = .inr event
    · exact ⟨event, payload, selected, binding⟩
    · apply onlyBindings.1 field
      simpa only [BindingShadow.rememberCompletion, Function.update_of_ne selected] using present
  · intro query present
    by_cases selected : query = event
    · subst query
      exact ⟨payload, binding⟩
    · apply onlyBindings.2 query
      simpa only [BindingShadow.rememberCompletion, Function.update_of_ne selected] using present

theorem OwnBindings.public_value_none {memory : BindingShadow graph} {who : Player}
    (onlyBindings : memory.OwnBindings who) (field : graph.Field)
    (visible : (graph.layout field).IsPublic) : memory.values field = none := by
  cases stored : memory.values field with
  | none => rfl
  | some value =>
      obtain ⟨event, payload, rfl, binding⟩ := onlyBindings.1 field (by simp only [stored]; rfl)
      change (graph.outputLayout event).IsPublic at visible
      rw [binding] at visible
      exact visible.elim

theorem OwnBindings.public_action_none {memory : BindingShadow graph} {who : Player}
    (onlyBindings : memory.OwnBindings who) (event : graph.EventId)
    (visible : (graph.outputLayout event).IsPublic) : memory.actions event = none := by
  cases stored : memory.actions event with
  | none => rfl
  | some action =>
      obtain ⟨payload, binding⟩ := onlyBindings.2 event (by simp only [stored]; rfl)
      rw [binding] at visible
      exact visible.elim

variable [DecidableEq Player]

/-- A completion with no private override is read from the real runtime.
This includes public results and other owners' private bindings. -/
theorem complete_unmodified_observation (memory : BindingShadow graph) (who : Player)
    (left right : graph.Config)
    (stores : memory.store (graph.playerObserve who right).store =
      (graph.playerObserve who left).store)
    (actions : (graph.playerObserve who right).ownActions.map memory.completion =
      (graph.playerObserve who left).ownActions)
    (event : graph.EventId) (leftReady : left.cut.Ready event)
    (rightReady : right.cut.Ready event)
    (noValue : memory.values (.inr event) = none)
    (noAction : memory.actions event = none)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    memory.store (graph.playerObserve who
      (right.complete event rightReady action value)).store =
        (graph.playerObserve who (left.complete event leftReady action value)).store ∧
    ((graph.playerObserve who
      (right.complete event rightReady action value)).ownActions.map memory.completion) =
        (graph.playerObserve who (left.complete event leftReady action value)).ownActions := by
  classical
  constructor
  · funext field
    by_cases selected : field = .inr event
    · subst field
      by_cases visible : graph.fieldVisibleTo who (.inr event)
      · simp only [store, EventGraph.playerObserve, EventGraph.playerStore_of_visible,
          visible, EventGraph.Config.store_output, EventGraph.Config.complete_output_same,
          noValue, Option.map_some, Option.getD_none]
      · simp only [store, EventGraph.playerObserve,
          EventGraph.playerStore, visible, ↓reduceIte, Option.map_none]
    · change memory.store (graph.playerStore who
        (right.complete event rightReady action value).store) field =
          graph.playerStore who (left.complete event leftReady action value).store field
      rw [EventGraph.store_complete, EventGraph.store_complete]
      have prior := congrFun stores field
      simpa only [store, EventGraph.playerObserve, EventGraph.playerStore,
        Function.update_of_ne selected] using prior
  · change List.map memory.completion
      (graph.ownCompletions who (right.history ++ [⟨event, action⟩])) =
        graph.ownCompletions who (left.history ++ [⟨event, action⟩])
    by_cases owned : graph.actor? event = some who
    · simp only [EventGraph.ownCompletions, List.filter_append, List.filter_cons, owned,
        decide_true, ↓reduceIte, List.filter_nil, List.map_append, List.map_cons, List.map_nil]
      change (graph.playerObserve who right).ownActions.map memory.completion ++
        [memory.completion ⟨event, action⟩] =
          (graph.playerObserve who left).ownActions ++ [⟨event, action⟩]
      rw [actions]
      simp only [completion, noAction, Option.getD_none]
    · simp only [EventGraph.ownCompletions, List.filter_append, List.filter_cons, owned,
        decide_false, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
      exact actions

end BindingShadow

variable [DecidableEq Player]
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

namespace BindingMemory

theorem repairResponse_ownBindings (who : Player) (memory : BindingMemory runtime leaks)
    (onlyBindings : memory.shadow.OwnBindings who)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action) :
    (memory.repairResponse runtime leaks who view response).2.OwnBindings who := by
  unfold repairResponse
  split
  · split
    · rename_i owner payload outputEq codeEq node
      dsimp only
      split
      · rename_i selected
        have owned := selected.2.1
        subst owner
        exact (onlyBindings.rememberCandidate _ _).rememberCompletion _ payload outputEq _ _
      · exact onlyBindings
    · exact onlyBindings
    · exact onlyBindings
  · exact onlyBindings

end BindingMemory

end Vegas.EventGraphRuntime
