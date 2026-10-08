/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveAsyncContract
import Interaction.ReactiveSchedulerRefinement

/-! # Asynchronous guarantees under scheduler support refinement

The service contract quantifies over legal raw histories. A scheduler that
only removes supported commands inherits the same opportunity, inclusion and
completion guarantees. Probabilities and equilibrium beliefs may still change.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
  (smaller larger : (runtime.reactiveApplication leaks).Scheduler)
  (included : ∀ past view, (smaller past view).support ⊆ (larger past view).support)
  (delay bound : graph.EventId → Nat)

include included

/-- Removing scheduler possibilities preserves all three all-history clauses
of the actual asynchronous service contract with their original bounds. -/
theorem AsyncContract.of_scheduler_support_subset
    (contract : AsyncContract runtime leaks initial horizon larger delay bound) :
    AsyncContract runtime leaks initial horizon smaller delay bound where
  opportunity control trace := contract.opportunity control
    ((runtime.reactiveApplication leaks).trace_of_scheduler_support_subset
      initial horizon smaller larger included trace)
  inclusion control trace := contract.inclusion control
    ((runtime.reactiveApplication leaks).trace_of_scheduler_support_subset
      initial horizon smaller larger included trace)
  completes control trace := contract.completes control
    ((runtime.reactiveApplication leaks).trace_of_scheduler_support_subset
      initial horizon smaller larger included trace)

end Vegas.EventGraphRuntime
