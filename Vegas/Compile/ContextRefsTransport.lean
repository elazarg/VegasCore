/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphEvaluation

/-! # Typed context agreement under a change of dependent index -/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]

omit [IExpr.ResultTypes L] in
/-- Reindexing a typed source configuration and its actual field references
preserves agreement with the same complete graph store. -/
theorem ContextRefs.Agrees.cast_config {Index : Type*}
    (context : Index → SourceCtx Player L) {left right : Index} (equal : left = right)
    {Field : Type} {layout : Field → EventGraph.EventField Player L}
    (leftRefs : ContextRefs layout (context left)) (rightRefs : ContextRefs layout (context right))
    (sameRefs : cast (congrArg (fun index => ContextRefs layout (context index)) equal)
      leftRefs = rightRefs)
    (rightSource : SourceProgram.Config Player L (context right))
    (store : EventGraph.Store layout) (agrees : rightRefs.Agrees rightSource.state store) :
    leftRefs.Agrees (cast (congrArg (fun index => SourceProgram.Config Player L (context index))
      equal.symm) rightSource).state store := by
  cases equal
  cases sameRefs
  exact agrees

omit [IExpr.ResultTypes L] in
/-- Equality of transported references and configurations carries their full
local agreement forward, without changing the graph store. -/
theorem ContextRefs.Agrees.of_cast_config_eq {Index : Type*}
    (context : Index → SourceCtx Player L) {left right : Index} (equal : left = right)
    {Field : Type} {layout : Field → EventGraph.EventField Player L}
    (leftRefs : ContextRefs layout (context left)) (rightRefs : ContextRefs layout (context right))
    (sameRefs : cast (congrArg (fun index => ContextRefs layout (context index)) equal)
      leftRefs = rightRefs)
    (leftSource : SourceProgram.Config Player L (context left))
    (rightSource : SourceProgram.Config Player L (context right))
    (sameSource : cast (congrArg (fun index => SourceProgram.Config Player L (context index))
      equal) leftSource = rightSource)
    (store : EventGraph.Store layout) (agrees : leftRefs.Agrees leftSource.state store) :
    rightRefs.Agrees rightSource.state store := by
  cases equal
  cases sameRefs
  cases sameSource
  exact agrees

end Vegas
