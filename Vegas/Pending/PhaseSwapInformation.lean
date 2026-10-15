/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSwapMenu
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

/-- Fixing visible fields, owned actions and owned candidate values fixes the
actual native view; public phase observations alone would not suffice. -/
theorem phaseView_observe_eq_of_fixed (who : Player)
    (fields : ∀ field, graph.fieldVisibleTo who field → swap.values.value field = id)
    (actions : ∀ event, graph.actor? event = some who → swap.values.action event = id)
    (handles : ∀ slot, swap.raw (who, slot) = id)
    (current : (phaseApplication runtime leaks).Execution) :
    swap.phaseView (current.observe (phaseApplication runtime leaks) who) =
      current.observe (phaseApplication runtime leaks) who := by
  change (⟨current.network.observe who,
    (PlayerView.swap swap (current.application.current.native.playerView who),
      current.application.publicView), current.receipts⟩ :
      (phaseApplication runtime leaks).PlayerView) = _
  congr 1
  unfold PlayerView.swap State.playerView
  simp only [PlayerObservation.swap_eq_self swap.values fields actions]
  congr 1
  congr 1
  funext slot
  rw [handles slot]
  cases current.application.current.native.candidates.lookup (who, slot) <;> rfl

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

/-- Actual recalled entries have their original legal response and actual
pre-response view. These two facts fix the observer's whole private recall. -/
theorem phaseRecall_eq_of_fixed [Fintype Player] (bounds : MessageBounds graph)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial
      horizon scheduler).Trace (some control)) (who : Player)
    (fields : ∀ field, graph.fieldVisibleTo who field → swap.values.value field = id)
    (actions : ∀ event, graph.actor? event = some who → swap.values.action event = id)
    (handles : ∀ slot, swap.raw (who, slot) = id) :
    (control.execution.recall who).map swap.phaseEntry = control.execution.recall who := by
  conv_rhs => rw [← List.map_id (control.execution.recall who)]
  apply List.map_congr_left
  intro entry member
  obtain ⟨before, _, _prefix, _, viewed, legal, _⟩ :=
    (PhaseCount.onePacketMenu runtime leaks bounds).recorded_response_prefix initial horizon
      scheduler control trace who entry member
  rcases entry with ⟨beforeView, action, emitted⟩
  change beforeView = before.execution.observe (phaseApplication runtime leaks) who at viewed
  change (⟨swap.phaseView beforeView, swap.phaseAction action, emitted⟩ :
    (phaseApplication runtime leaks).PlayerEntry) = _
  rw [swap.phaseAction_eq_of_onePacket bounds who handles _ _ action legal, viewed,
    swap.phaseView_observe_eq_of_fixed who fields actions handles]
  rfl

/-- The swapped full execution presents exactly the same information input
to a fixed observer at every actual counted history. -/
theorem phaseInput_eq_of_fixed [Fintype Player] (bounds : MessageBounds graph)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial
      horizon scheduler).Trace (some control)) (who : Player)
    (fields : ∀ field, graph.fieldVisibleTo who field → swap.values.value field = id)
    (actions : ∀ event, graph.actor? event = some who → swap.values.action event = id)
    (handles : ∀ slot, swap.raw (who, slot) = id) :
    ((swap.phaseExecution control.execution).recall who,
        (swap.phaseExecution control.execution).observe (phaseApplication runtime leaks) who) =
      (control.execution.recall who,
        control.execution.observe (phaseApplication runtime leaks) who) := by
  rw [swap.observe_phaseExecution,
    swap.phaseView_observe_eq_of_fixed who fields actions handles]
  change ((control.execution.recall who).map swap.phaseEntry, _) = _
  rw [swap.phaseRecall_eq_of_fixed bounds initial horizon scheduler control trace
    who fields actions handles]

end Vegas.EventGraphRuntime.HiddenSwap
