/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseReactiveValueSwap
import Vegas.Pending.OnePacketValueSwap
import Interaction.ReactiveRecordedResponse
import Vegas.Pending.PhaseLatestBindings

/-! # Complete observer information under phased hidden-value replay -/

noncomputable section

namespace Vegas.EventGraphRuntime.HiddenSwap

open Interaction EventGraph GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  (swap : HiddenSwap graph)

/-- A counted commitment changes only its sender's prepared value. Hence a
swap fixing that sender's handles fixes the complete original response. -/
theorem phaseAction_eq_of_onePacket [Fintype Player] (bounds : MessageBounds graph)
    (who : Player) (handles : ∀ slot, swap.raw (who, slot) = id)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (member : response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view) :
    swap.phaseAction response = response := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some submission =>
      obtain ⟨_, onePacket⟩ := (PhaseCount.mem_onePacketActions runtime leaks bounds
        who past view ⟨some submission⟩).mp member
      rcases onePacket with silent | ⟨material, sent, permitted⟩
      · cases silent
      · cases sent
        have correct := ((PhaseCount.permits_eq_true_iff _ _).mp permitted).2.1
        unfold phaseAction
        simp only [Option.map_some]
        congr 2
        rcases submitted : submission with ⟨⟨packet, opening⟩, evidence⟩
        rw [submitted] at correct
        cases packet with
        | commitment event candidate =>
            unfold CountCallCorrect at correct
            have packetEq : (PhaseCount.nativeMessage (PhaseCount.localEnvelope runtime leaks
                who past view ⟨⟨.commitment event candidate, opening⟩, evidence⟩)).payload.call =
                .commitment event candidate := by
              change (PhaseCount.maskPacket _ _).call = _
              exact PhaseCount.maskPacket_call _ _
            rw [packetEq] at correct
            have owned : candidate.1 = who := correct.2.2.1
            have same : candidate = (who, candidate.2) := by rw [← owned]
            change WitnessedSubmission.mk ⟨_, opening.map (swap.raw candidate)⟩ evidence = _
            rw [same, handles candidate.2, Option.map_id]
            rfl
        | opening | malformed => rfl

end Vegas.EventGraphRuntime.HiddenSwap
