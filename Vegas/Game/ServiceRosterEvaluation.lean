/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRoster
import Interaction.ReactiveRoundReachability
import Vegas.Game.RevealServicePrefix
import Vegas.Pending.ReactiveOpeningSettlement
import Vegas.Game.SourceStateKernel
import Vegas.Game.SourceInformation
import Vegas.Game.SourcePrefixKernel
import Vegas.Compile.EventGraphResolutionFields
import Interaction.ReactiveMessageIdentity
import Vegas.Pending.CompletionService

/-! # The finite roster game evaluates the physical runtime

Finite restriction agrees at every legal history. Exact prefix laws retain
the complete execution, and transfer physical support to uniformly retained
responses without requiring policy coverage at inconsistent inputs.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
theorem rosterPlanPrefix_isPrefix (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (count : Nat) :
    (rosterPlanPrefix setup rosters count).IsPrefix (rosterPlan setup rosters) := by
  refine ⟨((List.finRange (graph setup).order.eventCount).drop count).flatMap
    (rosterBlock setup rosters), ?_⟩
  simp only [rosterPlanPrefix, rosterPlan, ← List.flatMap_append, List.take_append_drop]

end Vegas
