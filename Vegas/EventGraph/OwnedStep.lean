/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.Information

/-! # Deterministic execution of a supplied owned action -/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Once an owned event's action is fixed, its ready configuration step is pure.
Readiness supplies every declared read, including those of failed disclosures. -/
theorem Config.step_eq_pure_of_actor (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event) (owner : Player)
    (owned : graph.actor? event = some owner) :
    ∃ next, config.step event ready action = PMF.pure next := by
  obtain ⟨value, evaluates⟩ := (graph.nodes event).eval?_eq_pure_of_actor owner owned
    action config.store (fun _ read => config.read_available ready read)
  refine ⟨config.complete event ready action value, ?_⟩
  rw [config.step_eq_map_of_eval event ready action (PMF.pure value) evaluates, PMF.pure_map]

end Vegas.EventGraph
