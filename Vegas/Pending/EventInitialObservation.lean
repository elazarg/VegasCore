/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventInvariant
import Vegas.EventGraph.ObservationStep

/-! # Initial states with equal focal observations

Equal focal graph observations of two initial configurations identify the
initial public view and the focal player's initial candidate catalogue. Foreign
initial candidate meanings remain unrelated.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- A player's initial candidate catalogue is determined by its graph
observation, including failed initial bindings. -/
theorem State.initial_candidates_eq_of_observation (focal : Player)
    (left right : graph.Inputs)
    (observations : graph.playerObserve focal (Config.initial left) =
      graph.playerObserve focal (Config.initial right)) :
    (fun slot => (State.initial left).candidates.lookup (focal, slot)) =
      fun slot => (State.initial right).candidates.lookup (focal, slot) := by
  funext slot
  rw [State.initial_candidate, State.initial_candidate]
  cases slot with
  | prepared serial => rfl
  | initial input =>
      have inputsEqual (visible : (graph.inputLayout input).VisibleTo focal) :
          left input = right input := by
        have stored := store_eq_of_playerObserve_eq focal (Config.initial left)
          (Config.initial right) observations (.inl input) visible
        exact Option.some.inj stored
      have candidateCongr (kind : EventField Player L) (x y : kind.Value)
          (same : kind.VisibleTo focal → x = y) :
          State.candidateOfValue focal kind x = State.candidateOfValue focal kind y := by
        cases kind with
        | publicData payload | publication payload | privateInput _ payload => rfl
        | binding owner payload =>
            by_cases owned : owner = focal
            · rw [same (by simp [EventField.VisibleTo, owned])]
            · simp only [State.candidateOfValue, ite_eq_right owned]
      exact candidateCongr _ _ _ inputsEqual

/-- The initial public view is determined by any player's graph observation of
the initial configuration. -/
theorem State.initial_publicView_eq_of_observation (focal : Player)
    (left right : graph.Inputs)
    (observations : graph.playerObserve focal (Config.initial left) =
      graph.playerObserve focal (Config.initial right)) :
    (State.initial left).publicView = (State.initial right).publicView := by
  have publicObservation := publicObserve_eq_of_playerObserve_eq focal
    (Config.initial left) (Config.initial right) observations
  unfold State.publicView
  congr 1

end Vegas.EventGraphRuntime
