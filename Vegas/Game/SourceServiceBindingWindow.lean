/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceMenu
import Vegas.Pending.ReactivePlayerWindow

/-! # A deferred binding cannot be omitted or submitted twice

The real final owner activation records a first typed binding, including its
passive sample. That fact persists through every later service command. A
previous submission instead excludes every second fresh call of that event.
The claims are over all supported retained responses, without a chosen policy
or equilibrium. Fresh allocation and capacity are explicit operational inputs.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- An event already present in actual own recall cannot be freshly submitted
again. Exact known-envelope replays remain separate permitted responses. -/
theorem sourceService_response_once
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (recorded : (runtime setup).eventRecorded leaks past event = true)
    (response : (application setup leaks).Action)
    (member : response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view) :
    (runtime setup).submittedEvent? leaks response ≠ some event := by
  intro repeated
  have first := bounds.compiledActions_firstSubmission (runtime setup) leaks who past view
    response (sourceServiceMenu_in_compiled setup leaks bounds rosters who past view member)
  have stopped := (runtime setup).firstSubmission_false_of_recorded leaks past event recorded
    response repeated
  rw [stopped] at first
  cases first

/-- Every supported result of the actual last owner activation has submitted
the binding. Activation's random passive sample does not alter this obligation. -/
theorem final_binding_step_recorded
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (covered : bounds.CoversBindingValues)
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (initial final : (application setup leaks).Execution)
    (who : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (granted : initial.application.serviceGrant = some event)
    (owned : (graph setup).actor? event = some who)
    (ready : initial.application.config.cut.Ready event)
    (last : (initial.recall who).length + 1 =
      rosterOffset setup rosters who event + (rosters event).count who)
    (serial : Nat)
    (fresh : reactiveFreshSlot (initial.observe (application setup leaks) who).application =
      some serial)
    (capacity : serial < bounds.candidateCount)
    (reached : final ∈ ((runtime setup).interactionStep leaks players network (.player who)
      initial).support) :
    (runtime setup).eventRecorded leaks (final.recall who) event = true := by
  let app := application setup leaks
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind] at reached
  change final ∈ ((initial.environmentStep app (.activate who)).bind
    (app.invoke players who)).support at reached
  rw [ReactiveApplication.Execution.activation_samples, FinDist.bind_map] at reached
  obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  obtain ⟨response, supported, rfl⟩ := FinDist.support_map .. ▸ reached
  let activated := initial.sampledActivation app who sample
  by_cases recorded : (runtime setup).eventRecorded leaks (initial.recall who) event = true
  · exact (runtime setup).eventRecorded_respond_of_recorded leaks activated who who response
      event recorded
  · have unsent : (runtime setup).eventRecorded leaks (activated.recall who) event = false :=
      Bool.eq_false_iff.mpr recorded
    have localReady : (activated.observe app who).application.publicView.EventReady event :=
      (initial.application.publicView_eventReady event).mpr ready
    obtain ⟨value, _, responseEq⟩ := sourceService_final_binding_cases setup leaks bounds rosters
      covered who (activated.recall who) (activated.observe app who) event payload outputEq
        codeEq node granted owned localReady unsent last serial fresh capacity response
          (lawful who _ _ response supported)
    apply (runtime setup).eventRecorded_respond leaks activated who response event
    rw [responseEq, (runtime setup).submittedEvent_normalization]
    rfl

omit [Fintype Player] in
/-- Once the actual final opportunity has executed, no subsequent service
instruction can erase the binding's recorded submission. -/
theorem binding_recorded_after_service
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (plan : List (ServiceInstruction (graph setup)))
    (initial final : (application setup leaks).Execution) (who : Player)
    (event : (graph setup).EventId)
    (recorded : (runtime setup).eventRecorded leaks (initial.recall who) event = true)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network plan
      initial).support) :
    (runtime setup).eventRecorded leaks (final.recall who) event = true := by
  obtain ⟨entry, member, submitted⟩ :=
    ((runtime setup).eventRecorded_iff leaks (initial.recall who) event).mp recorded
  apply ((runtime setup).eventRecorded_iff leaks (final.recall who) event).mpr
  exact ⟨entry, (runtime setup).interactionPlan_recall_mono leaks players network plan
    initial final reached who member, submitted⟩

end Vegas.SourceProgram.RevealService
