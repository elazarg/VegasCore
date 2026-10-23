/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReservedEpochCompletion
import Vegas.Pending.ReservedEpochMixtureOpportunity
import Vegas.Pending.ReservedEpochMixtureReceipts

/-! # An actual all-raw asynchronous contract for reserved joint tapes -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem implementation_asyncContract {length : Nat} (prior : PMF (Tape Player length))
    (activationGap processingGap : Nat)
    (gaps : ∀ tape ∈ prior.support,
      tape.BoundedGaps (completionCycles runtime) activationGap processingGap)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) (inputs : PMF graph.Inputs) :
    PhaseService.AsyncContract runtime leaks (inputs.map (PhaseRuntimeState.initial plan))
      (executionHorizon runtime)
        (implementation runtime leaks (packetCapacity runtime) prior).scheduler
          (fun _ => activationGap + 1) (fun _ => processingGap + 1) where
  opportunity := implementation_opportunity runtime leaks (packetCapacity runtime)
    (completionCycles runtime) prior activationGap processingGap gaps plan ordered maximal inputs
  inclusion := implementation_protectedInclusion runtime leaks (completionCycles runtime) prior
    activationGap processingGap gaps plan inputs
  completes current trace terminal :=
    (implementation_terminal_history_complete runtime leaks prior plan ordered maximal inputs
      current trace terminal).2

omit [Fintype Player] [DecidableEq Player] in
theorem asyncTimely (activationGap processingGap : Nat)
    (margin : ∀ event, (graph.actor? event).isSome →
      activationGap + processingGap + 2 < runtime.deadline event) :
    runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1) := by
  intro event owned
  have bound := margin event owned
  change (activationGap + 1) + (processingGap + 1) < runtime.deadline event
  omega

end Vegas.EventGraphRuntime.ReservedEpoch
