/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBoundary
import Vegas.Pending.ReactiveServiceConformance
import Vegas.Pending.ReactiveCompiledResolution
import Vegas.Pending.ReactiveGuardedResponse
import Vegas.EventGraph.ResolutionProvenance
import Interaction.ReactiveTrafficAudit
import Interaction.ReactiveTrafficContinuation
import Vegas.Game.SourceServiceDisclosure
import Vegas.Game.SourceServicePrefix
import Vegas.Game.SourceStateKernel
import Vegas.Source.DisclosureNormalization
import Vegas.Source.DisclosureSupport

/-! # Typed support of every retained full-source prefix

The actual service is folded through the existing source constructors. Policy
membership alone supplies the operational successor at each phase: private
bindings may occur at any permitted opportunity, public chance keeps its real
support, and guarded resolution records its effective disclosure. The decoded
source position and the dynamic operational boundary are derived together.
The residual-state inclusion also commutes with the existing source transition
and every later decoder offset.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

end Vegas
