/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePolicyFacts
import GameTheoryExtensions.Core.RegularChoice

/-! # Recovery under regular inclusion

The graph compiler's actual recovery law retains supported source choices.
This instantiates the local incentive theorem for arbitrary regular selection,
including mixtures of stable priority orders. A complete native SPE proof
must separately establish the continuation kernel and proper-root contract.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory GameTheory.Math.Probability Interaction

variable {Player : Type}
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveRecoveryLaw_regular_optimal (intentions : List (Option graph.Completion))
    (event : graph.EventId) (law : FinDist (graph.Action event))
    (selection : PendingChoice.RegularSelection (graph.Action event))
    {Outcome : Type} (continuation : graph.Action event → FinDist Outcome)
    (utility : Outcome → ℝ)
    (optimal : ∀ action, (continuation action).expect utility ≤
      (law.bind continuation).expect utility)
    (alternative : FinDist (Option (graph.Action event))) :
    ((selection.responseLaw alternative).bind continuation).expect utility ≤
      ((selection.responseLaw
        ((reactiveRecoveryLaw intentions event law).map some)).bind
          continuation).expect utility :=
  selection.optimal_response_of_support law _ continuation utility optimal
    (fun _ supported => reactiveRecoveryLaw_support intentions event law _ supported)
    alternative

end Vegas.EventGraphRuntime
