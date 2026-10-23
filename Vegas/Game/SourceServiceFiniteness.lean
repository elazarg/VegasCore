/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCompletion
import Vegas.Game.SourceServiceChoiceSupport
import GameTheory.Analysis.Protocol.CounterfactualDecomposition

/-! # Finite support of the timed source service

The timed compilation of a source profile branches finitely: fresh binding
values are finite because the service covers them, the timing draw ranges over
finitely many slots, and silence is a single response.
With the service's finitely branching prior and leak rule, every reserved phase
of the actual service therefore has a finitely supported law, and so do the
source continuations it is compared with.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable [Fintype Player]

namespace TimedApproximant

variable {service : SourceServiceSpec Player L} (approx : TimedApproximant service)

omit [Fintype Player] in
/-- The service's fresh binding alphabets are finite, since it covers them. -/
theorem finiteBindingTypes : service.setup.program.FiniteBindingTypes :=
  sourceService_finiteBindingTypes service.setup service.bounds service.values

end TimedApproximant

end Vegas
