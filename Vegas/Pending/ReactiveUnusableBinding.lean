/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveBindingRepair

/-! # Inclusion of arbitrary private commitment material

The submitted packet is opaque. Missing and mistyped opening material both
produce the typed failed binding, while retaining their distinct private raw
catalog entries. Acceptance and its receipt do not certify hidden usability.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem submitted_bindingResult (execution : (runtime.reactiveApplication leaks).Execution)
    (who : Player) (event : graph.EventId) (payload : L.Ty) (serial : Nat)
    (opening : Option (Raw L))
    (fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh) :
    let response : (runtime.reactiveApplication leaks).Action :=
      ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩
    (execution.respond (runtime.reactiveApplication leaks) who response).application.bindingResult
      (who, .prepared serial) payload =
      (opening.bind fun raw => raw.as? payload).elim .failure PublicationResult.success := by
  cases opening with
  | none =>
      change (submitStep execution.application who
        (.commitment event (who, .prepared serial))).bindingResult _ _ = _
      rw [submitStep_bindingResult]
      simp only [State.bindingResult, fresh, Option.bind_none, Option.elim_none]
  | some raw =>
      change (submitStep (Submission.register
        ⟨.commitment event (who, .prepared serial), some raw⟩ execution.application who) who
          (.commitment event (who, .prepared serial))).bindingResult _ _ = _
      rw [submitStep_bindingResult]
      simp only [Submission.register, ↓reduceIte, State.bindingResult,
        CommitmentCandidates.lookup_prepare_self, fresh, Option.bind_some]

end Vegas.EventGraphRuntime
