/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingRepairObservation

/-! # Saved and live completion equations for a directed binding repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Remembering a repaired binding does not add it to an older checkpoint in
which the event is still absent, including its original dependent action. -/
theorem rememberCompletion_config_pending (memory : BindingShadow graph)
    (state : graph.Config) (event : graph.EventId)
    (missing : event ∉ state.cut.completed) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    (memory.rememberCompletion event action value).config state = memory.config state := by
  classical
  apply Config.ext_fields (left := (memory.rememberCompletion event action value).config state)
    (right := memory.config state) rfl rfl
  · funext query
    by_cases selected : query = event
    · subst query
      have absent : state.outputs event = none := by
        cases stored : state.outputs event with
        | none => rfl
        | some old => exact (missing ((state.output_available event).mp (by rw [stored]; rfl))).elim
      simp only [config, absent, Option.map_none]
    · have fieldDifferent : Sum.inr query ≠ (Sum.inr event : graph.Field) :=
        fun same => selected (Sum.inr.inj same)
      simp only [config, rememberCompletion, Function.update_of_ne fieldDifferent]
  · apply List.map_congr_left
    intro prior member
    have different : prior.event ≠ event := by
      intro same
      apply missing
      apply (state.history_exact event).mp
      exact List.mem_map.mpr ⟨prior, member, same⟩
    simp only [completion, rememberCompletion, Function.update_of_ne different]

/-- The remembered original value and action are stored only at the actual
completion edge. This equation applies equally to failed and mistyped inputs. -/
theorem rememberCompletion_config_complete (memory : BindingShadow graph)
    (state : graph.Config) (event : graph.EventId) (ready : state.cut.Ready event)
    (originalAction repairedAction : graph.Action event)
    (originalValue repairedValue : (graph.outputLayout event).Value) :
    (memory.rememberCompletion event originalAction originalValue).config
        (state.complete event ready repairedAction repairedValue) =
      (memory.config state).complete event ready originalAction originalValue := by
  classical
  apply Config.ext_fields (left :=
    (memory.rememberCompletion event originalAction originalValue).config
      (state.complete event ready repairedAction repairedValue))
    (right := (memory.config state).complete event ready originalAction originalValue) rfl rfl
  · funext query
    by_cases selected : query = event
    · subst query
      simp only [config, Config.complete, Function.update_self, Option.map_some,
        rememberCompletion, Option.getD_some]
    · have fieldDifferent : Sum.inr query ≠ (Sum.inr event : graph.Field) :=
        fun same => selected (Sum.inr.inj same)
      simp only [config, Config.complete, Function.update_of_ne selected,
        rememberCompletion, Function.update_of_ne fieldDifferent]
  · have earlier := congrArg Config.history
      (rememberCompletion_config_pending memory state event ready.1 originalAction originalValue)
    change state.history.map (memory.rememberCompletion event originalAction
      originalValue).completion = state.history.map memory.completion at earlier
    change ((state.history ++ [(⟨event, repairedAction⟩ : graph.Completion)]).map
      (memory.rememberCompletion event originalAction originalValue).completion) =
      state.history.map memory.completion ++ [⟨event, originalAction⟩]
    rw [List.map_append, earlier]
    simp only [List.map_cons, List.map_nil, completion, rememberCompletion,
      Function.update_self, Option.getD_some]

variable [DecidableEq Player]

/-- The same override is absent from both a live ready frontier and every saved
prefix. Catalogue reconstruction is unchanged by completion bookkeeping. -/
theorem rememberCompletion_native_pending (memory : BindingShadow graph) (owner : Player)
    (state : State graph) (event : graph.EventId) (missing : event ∉ state.config.cut.completed)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    (memory.rememberCompletion event action value).native owner state = memory.native owner state :=
  by
  change ({ state with
    config := (memory.rememberCompletion event action value).config state.config
    candidates := _ } : State graph) = _
  rw [rememberCompletion_config_pending memory state.config event missing action value]
  rfl

end Vegas.EventGraphRuntime.BindingShadow
