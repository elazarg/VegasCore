/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingRepairFrame
import Vegas.Pending.ReactiveBindingSubmissionFrame

/-! # Count admission discharges native response replay guards -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- Authentic local authorization discharges both actual physical masks. -/
theorem localEnvelope_admitted (physical : (phaseApplication runtime leaks).Execution)
    (who : Player) (material : WitnessedSubmission graph)
    (authorized : (PhaseCount.localEnvelope runtime leaks who (physical.recall who)
      (physical.observe (phaseApplication runtime leaks) who) material).payload.packet.tokenValid =
        true) :
    physical.application.allows material.call.packet = true ∧
      physical.application.current.excludedCall material.call.packet = false := by
  let packet : WitnessedPacket graph :=
    ⟨material.call.packet, material.evidence.resolve who
      (material.call.candidateAfter who
        (physical.application.current.native.playerView who).candidates)
      ((ReactiveApplication.ResponseMenu.knownPackets (physical.recall who)
        (physical.observe (phaseApplication runtime leaks) who)).map PhaseCount.nativeMessage),
      physical.application.current.native.publicView.tokenFor material.call.packet⟩
  change (PhaseCount.maskPacket physical.application.publicView packet).tokenValid = true
    at authorized
  have allowed : PhaseCount.allows physical.application.publicView packet.call = true := by
    cases permission : PhaseCount.allows physical.application.publicView packet.call with
    | false =>
        simp only [PhaseCount.maskPacket, permission, Bool.false_eq_true, ↓reduceIte,
          WitnessedPacket.tokenValid_none] at authorized
    | true => rfl
  have unexcluded : PhaseCount.excludedCall physical.application.publicView packet.call =
      false := by
    cases excluded : PhaseCount.excludedCall physical.application.publicView packet.call with
    | false => rfl
    | true =>
        simp only [PhaseCount.maskPacket, allowed, excluded, ↓reduceIte,
          WitnessedPacket.tokenValid_none, Bool.false_eq_true] at authorized
  exact ⟨(PhaseCount.allows_publicView _ _).symm.trans allowed, unexcluded⟩

variable [Fintype Player] (bounds : MessageBounds graph)

end Vegas.EventGraphRuntime.PhaseBindingRepair
