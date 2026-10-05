/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceImmediatePolicy
import Vegas.Game.SourceServiceFirstTurnRisk
import Vegas.Pending.ReactiveDecisionOrigin

/-! # Own-turn coverage after a clear immediate response

Earlier silent own turns need not have recorded any call. At an actual
clear owner decision point, completed decisions have accepted-call provenance,
and any earlier unfinished own turn still names the current ready event.
The immediate response records that event. This establishes coverage without
discarding earlier private recall or requiring an earlier turn index of zero.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A completed unmarked owned decision has an actual owner submission in
recall, including explicit withholding and commitments whose value failed. -/
theorem completed_owned_decision_recorded {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) (event : (graph setup).EventId)
    (completed : event ∈ control.execution.application.config.cut.completed)
    (clear : control.execution.application.publicView.missedDecisionBy who = false)
    (owned : (graph setup).actor? event = some who) :
    (runtime setup).eventRecorded leaks (control.execution.recall who) event = true := by
  let app := application setup leaks
  have facts := legalFacts setup leaks horizon scheduler control trace
  have unmarked :=
    (control.execution.application.publicView.missedDecisionBy_eq_false_iff who).mp clear event
      owned
  have initialized := trace
  rw [initialLaw_eq_inputs] at initialized
  have origins := (runtime setup).completedDecisionRecall_history leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler initialized
  obtain ⟨message, output, sender, addressed⟩ := origins event who owned completed unmarked
  rw [← facts.inputs who] at output
  obtain ⟨entry, member, material, transmitted, emitted, state, known, packet⟩ :=
    facts.provenance.inputs message (List.mem_filter.mp output).1
  rw [sender] at member
  have named : (runtime setup).submittedEvent? leaks entry.action = some event := by
    unfold EventGraphRuntime.submittedEvent?
    rw [transmitted]
    change (app.packet state message.sender known material).call.event? (graph setup) = some event
    rw [packet]
    exact addressed
  exact List.any_eq_true.mpr ⟨entry, member, by simp only [named, decide_true]⟩

/-- A supported immediate response at an actual clear active owner site records
every earlier own turn, even when the owner previously deferred there. -/
theorem sourceServiceImmediatePolicy_ownTurnsRecorded_respond {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {bound : (graph setup).EventId → Nat} {profile : BehavioralProfile setup.program}
    {execution : (application setup leaks).Execution} {who : Player}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks execution who)
    (slots : CanonicalSlotsUsed setup leaks execution who)
    (clear : (runtime setup).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) = false)
    (response : (application setup leaks).Action)
    (chosen : response ∈ (sourceServiceImmediatePolicy setup leaks bound profile who
      (execution.recall who) (execution.observe (application setup leaks) who)).support) :
    OwnTurnsRecorded setup leaks (execution.respond (application setup leaks) who response)
      who := by
  let app := application setup leaks
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have publicClear := ((runtime setup).persistentServiceRisk_clear_iff leaks bound who _ _).mp
    (((runtime setup).serviceRisk_clear_iff leaks bound who _ _).mp clear).1 |>.1.1
  have recordsCurrent (event : (graph setup).EventId)
      (turn : execution.application.publicView.ownTurn? who = some event) :
      (runtime setup).eventRecorded leaks ((execution.respond app who response).recall who)
        event = true := by
    by_cases recorded : (runtime setup).eventRecorded leaks (execution.recall who) event = true
    · exact (runtime setup).eventRecorded_respond_of_recorded leaks execution who who response
        event recorded
    · have unrecorded := Bool.eq_false_of_not_eq_true recorded
      obtain ⟨material, _, _, recorded⟩ := sourceServiceImmediatePolicy_call trace atTurn slots
        clear event turn unrecorded response chosen
      exact recorded
  obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks execution who response
  intro entry member event turn
  rw [recalled] at member
  rcases List.mem_append.mp member with old | new
  · have ready := (PublicView.ownTurn?_spec _ who event turn).1
    by_cases completed : event ∈ execution.application.config.cut.completed
    · have recorded := completed_owned_decision_recorded trace who event completed publicClear
        (PublicView.ownTurn?_spec _ who event turn).2
      exact (runtime setup).eventRecorded_respond_of_recorded leaks execution who who response
        event recorded
    · have observation := (entry_view_current setup leaks execution facts.stable who entry old
        event ready completed).1
      exact recordsCurrent event ((ownTurn?_congr observation who).symm.trans turn)
  · cases List.mem_singleton.mp new
    exact recordsCurrent event turn

end Vegas
