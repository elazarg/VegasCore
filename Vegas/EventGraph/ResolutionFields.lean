/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Code

/-! # The commitment field consumed by a resolution node -/

namespace Vegas.EventGraph.EventCode

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L] {Field : Type} [DecidableEq Field]
  {layout : Field → EventField Player L}

def resolutionField? : {output : EventField Player L} → EventCode layout output → Option Field
  | _, .resolve _ _ binding _ => some binding.field
  | _, .bind .. | _, .sample .. => none

@[simp] theorem resolutionField?_cast {first second : EventField Player L}
    (equal : first = second) (code : EventCode layout first) :
    (cast (congrArg (EventCode layout) equal) code).resolutionField? = code.resolutionField? := by
  cases equal
  rfl

end Vegas.EventGraph.EventCode
