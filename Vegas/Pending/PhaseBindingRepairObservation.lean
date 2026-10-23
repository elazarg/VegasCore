/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseBindingShadow
import Vegas.Pending.ReactiveEventStability

/-! # Physical observations reconstructed by owner-local binding repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {memory : BindingShadow graph} {owner : Player}

omit [DecidableEq Player] in
theorem OwnBindings.foreign_value_none (owned : memory.OwnBindings owner)
    (who : Player) (different : who ≠ owner) (field : graph.Field)
    (visible : graph.fieldVisibleTo who field) : memory.values field = none := by
  cases stored : memory.values field with
  | none => rfl
  | some value =>
      obtain ⟨event, payload, rfl, binding⟩ := owned.1 field (by simp only [stored]; rfl)
      change (graph.outputLayout event).VisibleTo who at visible
      rw [binding] at visible
      exact (different visible.symm).elim

omit [DecidableEq Player] in
theorem OwnBindings.foreign_action_none (owned : memory.OwnBindings owner)
    (who : Player) (different : who ≠ owner) (event : graph.EventId)
    (acting : graph.actor? event = some who) : memory.actions event = none := by
  cases stored : memory.actions event with
  | none => rfl
  | some action =>
      obtain ⟨payload, binding⟩ := owned.2 event (by simp only [stored]; rfl)
      have actual := EventGraph.actor?_of_outputLayout_binding graph binding
      exact (different (Option.some.inj (acting.symm.trans actual))).elim

omit [DecidableEq Player] in
theorem config_publicObserve (owned : memory.OwnBindings owner) (state : graph.Config) :
    graph.publicObserve (memory.config state) = graph.publicObserve state := by
  apply PublicObservation.ext graph
  · simp only [publicObserve, config_history, List.map_map, completion, Function.comp_def]
  · funext field
    simp only [publicObserve, publicStore, config_store owned]
    split
    · rename_i visible
      simp only [store, owned.public_value_none field visible, Option.getD_none]
      exact congrFun Option.map_id _
    · rfl

theorem config_playerObserve_other (owned : memory.OwnBindings owner)
    (state : graph.Config) (who : Player) (different : who ≠ owner) :
    graph.playerObserve who (memory.config state) = graph.playerObserve who state := by
  apply PlayerObservation.ext graph
  · simp only [playerObserve, config_history, List.map_map, completion, Function.comp_def]
  · funext field
    simp only [playerObserve, playerStore, config_store owned]
    split
    · rename_i visible
      simp only [store, owned.foreign_value_none who different field visible,
        Option.getD_none]
      exact congrFun Option.map_id _
    · rfl
  · change (state.history.map memory.completion).filter _ = state.history.filter _
    rw [List.filter_map]
    have unchanged : ∀ entry ∈ state.history.filter
        (fun entry => decide (graph.actor? entry.event = some who)),
        memory.completion entry = entry := by
      intro entry member
      have acting := of_decide_eq_true (List.mem_filter.mp member).2
      simp only [completion, owned.foreign_action_none who different entry.event acting,
        Option.getD_none]
    conv_rhs => rw [← List.map_id (state.history.filter _)]
    exact List.map_congr_left unchanged

theorem native_publicView (owned : memory.OwnBindings owner) (state : State graph) :
    (memory.native owner state).publicView = state.publicView := by
  change (⟨graph.publicObserve (memory.config state.config), state.accepted,
    state.clock, state.activatedAt⟩ : PublicView graph) = _
  rw [config_publicObserve owned]
  rfl

theorem native_playerView_other (owned : memory.OwnBindings owner) (state : State graph)
    (who : Player) (different : who ≠ owner) :
    (memory.native owner state).playerView who = state.playerView who := by
  change (⟨who, (memory.native owner state).publicView,
    graph.playerObserve who (memory.config state.config),
    fun slot => if who = owner then memory.candidate slot (state.candidates.table who slot)
      else state.candidates.table who slot⟩ : PlayerView graph) = _
  rw [native_publicView owned, config_playerObserve_other owned state.config who different]
  simp only [different, ↓reduceIte]
  rfl

end Vegas.EventGraphRuntime.BindingShadow
