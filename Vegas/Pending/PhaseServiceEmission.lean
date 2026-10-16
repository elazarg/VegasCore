/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseCountMenu
import Vegas.Pending.PhaseSeedOperationalInput

/-! # Actual counted emissions reveal only their owner nonce and authorization -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every real nonempty counted response has the current owner's transport
nonce and a valid current-attempt token, regardless of its private contents. -/
theorem operational_emission_of_onePacket (bounds : MessageBounds graph)
    (execution : (app).Execution) (recalled : PhaseCount.CountRecall runtime leaks execution)
    (owner : Player) (material : WitnessedSubmission graph)
    (permitted : (⟨some material⟩ : (app).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds owner (execution.recall owner)
        (execution.observe app owner)) (elapsed : Nat) :
    let issued := (execution.network.submit owner
      ((execution.application.submit owner material).emit owner
        (execution.network.known owner) material)).1
    PhaseSeedInput.operationalEmission execution.application.attempt (elapsed, issued) =
      ⟨elapsed, (owner, execution.network.nextSerial owner), true⟩ := by
  rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp permitted).2 with
    silent | ⟨actual, same, admitted⟩
  · cases silent
  · have materialEq : material = actual := Option.some.inj same
    subst actual
    rw [PhaseCount.localEnvelope_eq_of_recall runtime leaks execution recalled.1 recalled.2.1]
      at admitted
    have authorized := ((PhaseCount.permits_eq_true_iff _ _).mp admitted).1
    have stamped : ((execution.application.submit owner material).emit owner
        (execution.network.known owner) material).attempt = execution.application.attempt := by
      rw [PhaseCount.emit_after_submit]
    change PhaseSeedEmission.mk elapsed (owner, execution.network.nextSerial owner)
      (((execution.application.submit owner material).emit owner
        (execution.network.known owner) material).tokenValid execution.application.attempt) = _
    apply congrArg (PhaseSeedEmission.mk elapsed (owner, execution.network.nextSerial owner))
    simp only [CommitAttemptPacket.tokenValid, stamped, decide_true, Bool.true_and]
    exact authorized

end Vegas.EventGraphRuntime.PhaseServiceScheduler
