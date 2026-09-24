/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Information

/-! # Evidence of graph bindings, independent of runtime handles -/

namespace Vegas.EventGraph

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

structure CommitmentEvidence (graph : Vegas.EventGraph Player L) where
  owner : Player
  payload : L.Ty
  binding : FieldRef graph.layout (.binding owner payload)
  value : L.Val payload

namespace CommitmentEvidence

def Holds (fact : CommitmentEvidence graph) (store : Store graph.layout) : Prop :=
  fact.binding.get? store = some (.success fact.value)

theorem holds_preserved (fact : CommitmentEvidence graph) (before after : Store graph.layout)
    (preserved : ∀ field value, before field = some value → after field = some value)
    (valid : fact.Holds before) : fact.Holds after :=
  fact.binding.get?_preserved before after preserved (.success fact.value) valid

theorem holds_step (fact : CommitmentEvidence graph) (config next : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event) (action : graph.Action event)
    (reached : next ∈ (config.step event ready action).support) (valid : fact.Holds config.store) :
    fact.Holds next.store :=
  fact.holds_preserved _ _ (config.step_store_of_some next event ready action reached) valid

end CommitmentEvidence
end Vegas.EventGraph
