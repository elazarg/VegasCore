/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveRuntime
import Vegas.Pending.EventCommitmentBinding

/-! # Binding under arbitrary reactive continuations

Every player response and scheduler step retains every fixed candidate meaning.
The statements cover arbitrary policies and raw protocol states; no service,
honesty, or eventual inclusion assumption is needed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactive_respond_candidate_fixed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action) (candidate : Handle graph)
    (fixed : execution.application.candidates.lookup candidate ≠ .fresh) :
    (execution.respond (runtime.reactiveApplication leaks) who
      action).application.candidates.lookup
      candidate = execution.application.candidates.lookup candidate := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some submission =>
      have registered : (submission.call.register execution.application who).candidates.lookup
          candidate = execution.application.candidates.lookup candidate := by
        rw [submission.call.register_eq]
        cases submission.call.registrationCommand who with
        | none => rfl
        | some command => exact privateStep_lookup_of_not_fresh _ who command candidate fixed
      exact (submitStep_lookup_of_not_fresh _ who submission.call.packet candidate
        (by rwa [registered])).trans registered

end Vegas.EventGraphRuntime
