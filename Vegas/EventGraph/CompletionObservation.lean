module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.Information

@[expose] public section

/-! # Recovering an observation before the latest graph completion -/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Recover the observation immediately before the specified last completion. -/
def beforeCompletion {who : Player} (event : graph.EventId)
    (observed : graph.PlayerObservation who) : graph.PlayerObservation who where
  completionOrder := observed.completionOrder.dropLast
  store := fun field => if field = .inr event then none else observed.store field
  ownActions := observed.ownActions.filter fun record => record.event ≠ event
  defaults := observed.defaults.back

/-- Every graph completion retains the previous observation, including its
actual chronology, own recall, and full public default record. -/
theorem beforeCompletion_playerObserve (who : Player) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    beforeCompletion event (graph.playerObserve who (config.complete event ready action value)) =
      graph.playerObserve who config := by
  apply EventPlayerObservation.ext
  · simp [beforeCompletion, playerObserve, EventGraph.completion]
  · funext field
    cases field with
    | inl input => simp [beforeCompletion, playerObserve, playerStore, Config.complete]
    | inr query =>
        by_cases same : query = event
        · subst query
          have absent : config.outputs event = none := by
            cases known : config.outputs event with
            | none => rfl
            | some output =>
                exact (ready.1 ((config.output_available event).mp (by simp [known]))).elim
          simp [beforeCompletion, playerObserve, playerStore, absent]
        · simp [beforeCompletion, playerObserve, playerStore, same,
            config.complete_output_of_ne event query ready action value same]
  · let completion := EventGraph.completion graph event (config.actualDecision event action) value
    have unchanged : ((graph.ownCompletions who config.history).filter
        fun record => record.event ≠ event) = graph.ownCompletions who config.history := by
      apply List.filter_eq_self.mpr
      intro record present
      have retained := ((graph.mem_ownCompletions who config.history record).mp present).1
      apply decide_eq_true
      intro equal
      exact ready.1 ((config.history_exact event).mp
        (List.mem_map.mpr ⟨record, retained, equal⟩))
    change ((graph.ownCompletions who (config.history ++ [completion])).filter
      fun record => record.event ≠ event) = graph.ownCompletions who config.history
    rw [show graph.ownCompletions who (config.history ++ [completion]) =
        graph.ownCompletions who config.history ++ graph.ownCompletions who [completion]
      from List.filter_append _ _]
    rw [List.filter_append, unchanged]
    simp [ownCompletions, completion, EventGraph.completion]
  · simp [beforeCompletion, playerObserve, Config.complete_defaults]

/-- A supported semantic step determines the preceding observation. -/
theorem beforeCompletion_playerObserve_of_step (who : Player) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event) (action : graph.Action event)
    (next : graph.Config) (supported : next ∈ (config.step event ready action).support) :
    beforeCompletion event (graph.playerObserve who next) = graph.playerObserve who config := by
  rw [Config.step, PMF.support_map] at supported
  obtain ⟨value, _, rfl⟩ := supported
  exact beforeCompletion_playerObserve who config event ready action value

end Vegas.EventGraph
