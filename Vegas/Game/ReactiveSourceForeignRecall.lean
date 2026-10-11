/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReactiveSourceDecision
import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactiveReceipts

/-! # Foreign source recall across arbitrary raw deviations -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Any raw response by another player preserves the complete reconstructed
source past of this owner. The acting player's policy need not be prescribed. -/
theorem originalReactiveSourceRecall_respond_other
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (whole : SourceProgram Player L Γ names)
    (runtime : EventGraphRuntime (toEventGraph whole))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (toEventGraph whole)))
    (owner acting : Player) (different : owner ≠ acting)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (intentions : List (Option (toEventGraph whole).Completion))
    (action : (runtime.reactiveApplication leaks).Action) :
    originalReactiveSourceRecall whole runtime leaks owner
      (execution.respond (runtime.reactiveApplication leaks) acting action) intentions =
      originalReactiveSourceRecall whole runtime leaks owner execution intentions := by
  have configEq := (runtime.reactive_respond_application leaks execution acting action).1
  unfold originalReactiveSourceRecall
  rw [configEq, (runtime.reactiveApplication leaks).respond_recall_other execution acting owner
    different action, (runtime.reactiveApplication leaks).respond_receipts]

/-- An arbitrary opponent callback cannot reweight an owner's posterior source
history. Both private memory and its decoded source readout are retained. -/
theorem originalReactiveSourceRecall_posterior_respond_other
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (whole : SourceProgram Player L Γ names)
    (runtime : EventGraphRuntime (toEventGraph whole))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (toEventGraph whole)))
    (owner acting : Player) (different : owner ≠ acting)
    (policy : (toEventGraph whole).BehavioralPolicy owner)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (action : (runtime.reactiveApplication leaks).Action) :
    let next := execution.respond (runtime.reactiveApplication leaks) acting action
    ((runtime.prescribedReactiveImplementation leaks owner policy).posterior
      (next.recall owner)).map (originalReactiveSourceRecall whole runtime leaks owner next) =
      ((runtime.prescribedReactiveImplementation leaks owner policy).posterior
        (execution.recall owner)).map
          (originalReactiveSourceRecall whole runtime leaks owner execution) := by
  intro next
  rw [(runtime.reactiveApplication leaks).respond_recall_other execution acting owner
    different action]
  apply map_congr_on_support
  intro intentions _
  exact originalReactiveSourceRecall_respond_other whole runtime leaks owner acting different
    execution intentions action

end Vegas
