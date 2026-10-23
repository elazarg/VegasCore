/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

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
end Vegas.EventGraph
