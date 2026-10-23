/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveContinuationObservation

/-! # Public chance under hidden binding repair

Public distributions read only public fields. Equal public observations give
one common sampling law, whose shared draws preserve opponents' views jointly.
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
theorem PublicRead.field_isPublic {payload : L.Ty}
    (read : PublicRead graph.layout payload) : graph.fieldPublic read.field := by
  cases read with
  | publicData ref | publication ref =>
      change (graph.layout ref.field).IsPublic
      rw [ref.layout_eq]
      trivial

omit [DecidableEq Player] in
/-- Conservative dependency footprints do not expose otherwise unused hidden
fields to a public distribution. -/
theorem PublicDist.eval?_publicStore {payload : L.Ty}
    (law : PublicDist graph.layout payload) (store : Store graph.layout) :
    law.eval? (graph.publicStore store) = law.eval? store := by
  apply law.eval?_congr_reads
  intro name input ref _
  exact PublicRead.get?_congr (law.reads ref) _ _
    (graph.publicStore_of_public store _ (law.reads ref).field_isPublic)

end Vegas.EventGraph
