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
    (event : graph.EventId) (law : PMF (graph.Action event))
    (selection : PendingChoice.RegularSelection (graph.Action event))
    {Outcome : Type} (continuation : graph.Action event → PMF Outcome)
    (utility : Outcome → ℝ)
    (actionIntegrable : ∀ action, PayoffIntegrable (continuation action) utility)
    (lawIntegrable : PayoffIntegrable (law.bind continuation) utility)
    (optimal : ∀ action, expect (continuation action) utility ≤
      expect (law.bind continuation) utility)
    (submittedIntegrable : PayoffIntegrable ((selection.responseLaw
      ((reactiveRecoveryLaw intentions event law).map some)).bind continuation) utility)
    (alternative : PMF (Option (graph.Action event)))
    (alternativeIntegrable : PayoffIntegrable
      ((selection.responseLaw alternative).bind continuation) utility) :
    expect ((selection.responseLaw alternative).bind continuation) utility ≤
      expect ((selection.responseLaw
        ((reactiveRecoveryLaw intentions event law).map some)).bind
          continuation) utility :=
  selection.optimal_response_of_support law _ continuation utility lawIntegrable
    (reactiveRecoveryLaw_bind_integrable intentions event law continuation utility
      actionIntegrable lawIntegrable) optimal
    (fun _ supported => reactiveRecoveryLaw_support intentions event law _ supported)
    submittedIntegrable alternative alternativeIntegrable

end Vegas.EventGraphRuntime
