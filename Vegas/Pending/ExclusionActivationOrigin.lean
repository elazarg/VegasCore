/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionInvariant
import Vegas.Pending.EventActivationOrigin

/-! # Activation origins through automatic completion -/

noncomputable section

namespace Vegas.EventGraphRuntime.State

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Automatic completion retains live activation times or starts them at the
unchanged clock, throughout its finite completion path. -/
theorem drainFuel_activationOrigin (fuel : Nat) (state : State graph) :
    ActivationOrigin state (state.drainFuel fuel) := by
  induction fuel generalizing state with
  | zero => exact activationOrigin_of_activatedEq rfl
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        have eligible := Classical.choose_spec pending
        have first := activationOrigin_of_refreshEq
          (state.completeAutomatic_activatedAt _ eligible)
        have clock : state.clock ≤ (state.completeAutomatic _ eligible).clock := by
          change state.clock ≤ (state.completeFailure _ eligible.1).clock
          rw [(state.completeFailure_tables _ eligible.1).2.2]
        exact first.trans (ih _) clock
          ((state.completeAutomatic _ eligible).drainFuel_completed_subset fuel)
      · exact activationOrigin_of_activatedEq rfl

/-- Draining automatic events preserves activation origins without an
initialized-state or service assumption. -/
theorem drain_activationOrigin (state : State graph) :
    ActivationOrigin state state.drain :=
  drainFuel_activationOrigin _ state

end Vegas.EventGraphRuntime.State
