/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalArchive
import Interaction.ReactiveCompleteInput

/-! # Reconstructing submitted proposals from actual decision inputs

Own recall, complete leaked pending traffic and the retained ledger recover the
entire submitted proposal set. No accepting receipt, usable preparation, clean
history or scheduler restriction is required. In particular, rejected and stale
opening packets contribute the same proposal as an opening still pending.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Complete observation recovers every submitted envelope from own outputs,
leaked packets and ledger, without consulting the scheduler's history. -/
theorem mem_knownPackets_iff_submitted
    (complete : leaks = MessageNetwork.completePendingObservation)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((app).protocol initial horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (message : Message Player (CommitAttemptPacket graph)) :
    message ∈ ReactiveApplication.ResponseMenu.knownPackets
        (control.execution.recall who) (control.execution.observe (app) who) ↔
      message ∈ control.execution.network.inputs := by
  have inputRecall := (app).history_inputRecall initial horizon scheduler trace who
  have retained := (app).retained_envelopes_mem_inputs control.execution
    ((app).history_provenance initial horizon scheduler trace)
    ((app).history_inputRecall initial horizon scheduler trace)
  simp only [ReactiveApplication.ResponseMenu.knownPackets, List.mem_append]
  constructor
  · rintro ((own | leaked) | ledger)
    · rw [← inputRecall] at own
      exact (List.mem_filter.mp own).1
    · exact retained.leaked who message leaked
    · exact retained.ledger message ledger
  · intro submitted
    by_cases own : message.sender = who
    · left; left
      rw [← inputRecall]
      exact List.mem_filter.mpr ⟨submitted, by simp [own]⟩
    · have visible := (app).complete_decision_submitted_visible complete scheduler initial
        horizon control trace who active message submitted own
      exact visible.elim (fun leaked => Or.inl (Or.inr leaked)) Or.inr

end Vegas.EventGraphRuntime.PhaseProposal
