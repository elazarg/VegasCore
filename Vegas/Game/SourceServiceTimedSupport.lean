/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedPolicy
import Vegas.Game.SourceServiceLocalSupport
import Vegas.Pending.ReactiveUnsubmittedWindow
import Interaction.ScheduledOpeningSupport

/-! # Timing support at actual full-source information sites

Before the first submission, actual retained prefixes are silent windows.
Each still-future timing choice therefore has positive posterior probability
whenever it had positive initial probability. The argument uses the complete
recorded native input, including observations made during earlier phases.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem silent_recall
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (network : (runtime setup).NetworkPolicy leaks) (owner : Player)
    (event : (graph setup).EventId) (visits : List Player)
    (initial final : (application setup leaks).Execution)
    (ready : initial.application.publicView.EventReady event)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      (fun _ => (application setup leaks).silentPolicy) network
        (visits.map ServiceInstruction.player) initial).support) :
    ∃ suffix, final.recall owner = initial.recall owner ++ suffix ∧
      ∀ before entry after, suffix = before ++ entry :: after →
        entry.action ∈ ((application setup leaks).silentPolicy
          (initial.recall owner ++ before) entry.beforeView).support ∧
        entry.beforeView.application.publicView.EventReady event := by
  let app := application setup leaks
  induction visits generalizing initial with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨[], (List.append_nil _).symm, by intros; simp_all⟩
  | cons actor rest ih =>
      obtain ⟨middle, step, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      simp only [interactionStep, interactionInstruction, PMF.pure_bind] at step
      change middle ∈ ((initial.environmentStep app (.activate actor)).bind
        (app.invoke (fun _ => app.silentPolicy) actor)).support at step
      rw [ReactiveApplication.Execution.activation_samples, PMF.bind_map] at step
      obtain ⟨sample, _, step⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ step)
      obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ step
      let activated := initial.sampledActivation app actor sample
      have nextReady : (activated.respond app actor response).application.publicView.EventReady
          event :=
        ((runtime setup).reactive_respond_application leaks activated actor response).2 ▸ ready
      obtain ⟨suffix, recalled, legal⟩ :=
        ih (activated.respond app actor response) nextReady reached
      by_cases same : actor = owner
      · subst actor
        obtain ⟨entry, entryRecall, entryView, entryAction⟩ :=
          (runtime setup).response_recall_entry leaks activated owner response
        refine ⟨entry :: suffix, ?_, ?_⟩
        · rw [recalled, entryRecall, List.append_assoc, List.singleton_append]
          rfl
        · intro before recorded after split
          cases before with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at split
              rcases split with ⟨rfl, rfl⟩
              rw [List.append_nil, entryView, entryAction]
              exact ⟨chosen, ready⟩
          | cons earlier before =>
              simp only [List.cons_append, List.cons.injEq] at split
              rcases split with ⟨rfl, split⟩
              have facts := legal before recorded after split
              rw [entryRecall, List.append_assoc, List.singleton_append] at facts
              exact facts
      · rw [app.respond_recall_other activated actor owner (Ne.symm same) response]
          at recalled legal
        exact ⟨suffix, recalled, legal⟩

variable [Fintype Player]

/-- The current unsent phase contributes only genuinely supported silent
responses to own recall, at actual local views that show the event ready. -/
theorem sourceService_unsubmitted_recall
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (owner : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some owner)
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (unsent : (runtime setup).eventRecorded leaks (control.execution.recall owner) event = false)
    : ∃ past suffix, control.execution.recall owner = past ++ suffix ∧
      past.length = rosterOffset setup rosters owner event ∧
      ∀ before entry after, suffix = before ++ entry :: after →
        entry.action ∈ ((application setup leaks).silentPolicy
          (past ++ before) entry.beforeView).support ∧
        entry.beforeView.application.publicView.EventReady event := by
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  obtain ⟨selectedEvent, position, initial, _, _, Γ, names, program, programProfile, source,
      refs, embedding, refsBefore, _, _, _, boundary, prior, sample, checkpoint, sole, reached,
      _, sampled, _, publicEq, _, _⟩ :=
    sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
      network (failureProfile setup.program) owner control trace active
  have eventEq : selectedEvent = event :=
    (sole.2 event ((control.execution.application.publicView_eventReady event).mpr ready)).symm
  subst selectedEvent
  have priorUnsent : (runtime setup).eventRecorded leaks (prior.recall owner) event = false := by
    rw [sampled] at unsent
    exact unsent
  have silenced := (runtime setup).compiled_unsubmitted_window leaks bounds menu.uniformResponses
    (fun who past view response supported =>
      sourceServiceMenu_in_compiled setup leaks bounds rosters who past view
        ((menu.uniformResponses_support who past view response).mp supported))
    network event owner owned ((rosters event).take position) boundary prior
      (soleReady_of_ready setup boundary.application (checkpoint.ready event rfl)) reached
      priorUnsent
  obtain ⟨suffix, recalled, legal⟩ := silent_recall setup leaks network owner event
    ((rosters event).take position) boundary prior
    ((boundary.application.publicView_eventReady event).mpr (checkpoint.ready event rfl)) silenced
  refine ⟨boundary.recall owner, suffix, ?_, checkpoint.response_offset event rfl owner, legal⟩
  rw [sampled]
  exact recalled

/-- Any current or future timing slot remains possible at every actual unsent
owner information site, independently of the policy that generated its trace. -/
theorem sourceServiceTimedPolicy_future_supported
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (owner : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some owner)
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (unsent : (runtime setup).eventRecorded leaks (control.execution.recall owner) event = false)
    (timing : PMF (Fin ((rosters event).count owner)))
    (slot : Fin ((rosters event).count owner)) (positive : slot ∈ timing.support)
    (future : (control.execution.recall owner).length ≤
      rosterOffset setup rosters owner event + slot.val) :
    slot ∈ (((application setup leaks).policyMixture timing
      (sourceServiceTimedFamily setup leaks rosters profile owner event)).posterior
        (control.execution.recall owner)).support := by
  let app := application setup leaks
  let family := sourceServiceTimedFamily setup leaks rosters profile owner event
  obtain ⟨past, suffix, recalled, offset, legal⟩ := sourceService_unsubmitted_recall setup leaks
    bounds values capacity rosters opportunities network owner control trace active
    event ready owned unsent
  have dormant := app.policyMixture_posterior_dormant timing family app.silentPolicy
    (rosterOffset setup rosters owner event)
    (fun slot past view earlier => app.scheduledPolicy_before _ _ _ _ past view earlier)
    past offset.le
  rw [recalled] at future ⊢
  apply app.policyMixture_posterior_support_append timing family past suffix slot
  · rw [dormant]
    exact positive
  · intro before entry after split
    have earlier : before.length < suffix.length := by
      have lengths := congrArg List.length split
      simp only [List.length_append, List.length_cons] at lengths
      omega
    have unused : some (rosterOffset setup rosters owner event + slot.val) ≠
        some (past ++ before).length := by
      simp only [List.length_append, offset] at future ⊢
      intro equal
      have equal := Option.some.inj equal
      omega
    simpa only [family, sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy,
      Option.map_some, ite_eq_right unused] using (legal before entry after split).1

end Vegas
