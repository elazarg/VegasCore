/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalArchive
import Interaction.ReactiveCompleteInput
import Interaction.ReactiveResponseNormalization

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

/-- This readout is a function of the player's full ordinary decision input. -/
def observedArchive (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    Finset (Proposal graph) :=
  archive (ReactiveApplication.ResponseMenu.knownPackets past view)

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

/-- Actual complete raw inputs determine the proposal archive, whether or not
the calls were included, certified, accepted, rejected or retired. -/
theorem observedArchive_eq_submitted
    (complete : leaks = MessageNetwork.completePendingObservation)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((app).protocol initial horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who) :
    observedArchive runtime leaks (control.execution.recall who)
        (control.execution.observe (app) who) = archive control.execution.network.inputs := by
  apply archive_congr
  exact mem_knownPackets_iff_submitted runtime leaks complete initial horizon scheduler
    control trace who active

/-- Equal full decision inputs identify the same archive even under different
schedulers and different hidden application preparations. -/
theorem archive_eq_of_completeInput
    (complete : leaks = MessageNetwork.completePendingObservation)
    (initial : PMF (app).State) (horizon : Nat)
    (leftScheduler rightScheduler : (app).Scheduler) (left right : (app).Control)
    (leftTrace : ((app).protocol initial horizon leftScheduler).Trace (some left))
    (rightTrace : ((app).protocol initial horizon rightScheduler).Trace (some right))
    (who : Player) (leftActive : left.actor = some who) (rightActive : right.actor = some who)
    (recalled : left.execution.recall who = right.execution.recall who)
    (observed : left.execution.observe (app) who = right.execution.observe (app) who) :
    archive left.execution.network.inputs = archive right.execution.network.inputs := by
  exact archive_congr _ _ ((app).complete_decision_inputs_congr complete initial horizon
    leftScheduler rightScheduler left right leftTrace rightTrace who leftActive rightActive
      recalled observed)

/-- A ledger proposal remains visible even when its inclusion receipt is false. -/
theorem ledger_proposal_mem_observedArchive
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (message : Message Player (CommitAttemptPacket graph)) (proposal : Proposal graph)
    (published : message ∈ view.messages.ledger)
    (proposed : packetProposal? message.payload = some proposal) :
    proposal ∈ observedArchive runtime leaks past view := by
  apply (mem_archive _ proposal).mpr
  refine ⟨message, ?_, proposed⟩
  simp only [ReactiveApplication.ResponseMenu.knownPackets, List.mem_append]
  exact Or.inr published

end Vegas.EventGraphRuntime.PhaseProposal
