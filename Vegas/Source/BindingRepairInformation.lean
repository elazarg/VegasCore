/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ValueBindingContinuation

/-! # Full foreign information across repaired source commitments

A failed commitment has a value-interface successor with the same information
for every other player, including that player's entire original action recall.
The claim is local to a focal owner's repair: another player's own failed
commitment is observable to that player and cannot be silently represented.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [IExpr.ResultTypes L] in
theorem Patched.foreign_view_eq {Γ : SourceCtx Player L} {who observer : Player}
    {unpatch : ViewMap who Γ} {patched : PatchMap who Γ}
    {original repaired : Config Player L Γ}
    (related : Patched unpatch patched original.state repaired.state
      original.history repaired.history)
    (foreign : observer ≠ who) : repaired.view observer = original.view observer := by
  exact Prod.ext
    (sourceObserve_congr observer repaired.state original.state related.publicEq
      related.publicationEq related.inputEq (fun cell => related.foreignEq cell foreign))
    (related.historyEq observer foreign)

end Vegas.SourceProgram
