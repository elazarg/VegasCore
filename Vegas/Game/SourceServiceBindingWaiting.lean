/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRepairOpportunity
import Vegas.Pending.ReactiveBindingAuditStep
import Vegas.Pending.ReactiveServiceRecall

/-! # Legal binding deferral reaches the next actual owner visit

The selected silence uses the same private repair memory update
as a raw response. Arbitrary unchanged opponents and passive observations then
lead to a real retained active history. The event stays unsubmitted, while no
pending observation or private recall is discarded.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem foreign_roster_recall
    {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (owner : Player) (visits : List Player)
    (absent : owner ∉ visits)
    (initial final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support) :
    final.recall owner = initial.recall owner := by
  let app := runtime.reactiveApplication leaks
  induction visits generalizing initial with
  | nil => cases (PMF.mem_support_pure_iff _ _).mp reached; rfl
  | cons who rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map,
        PMF.bind_bind, Function.comp_def] at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨response, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have different : owner ≠ who := fun same => absent (same ▸ List.mem_cons_self)
      rw [ih (fun member => absent (List.mem_cons_of_mem _ member)) _ reached,
        app.respond_recall_other _ who owner different response]
      rfl

theorem binding_waiting_opportunity
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (source : ∀ who, ((sourceServiceMenu setup leaks bounds rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralPolicy who)
    (target : ∀ who, ((bounds.menu (runtime setup) leaks).information
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).BehavioralPolicy who)
    (agrees : ((sourceServiceMenu_in_effective setup leaks bounds rosters).actionRestriction
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).ExtendsProfile source target)
    (owner : Player) (policy : (application setup leaks).Policy)
    (reference : List (application setup leaks).PlayerEntry)
    (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Execution)
    (frame : BindingMemory.Frame (runtime setup) leaks memory owner original repaired)
    (remaining : Nat) (visits : List Player) (absent : owner ∉ visits)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining + 1 + visits.length, some owner, repaired⟩))
    (leftRecall : original.InputRecall (application setup leaks))
    (_rightRecall : repaired.InputRecall (application setup leaks))
    (response : (application setup leaks).Action)
    (transport : response ∈ ((application setup leaks).silentPolicy (original.recall owner)
      (original.observe (application setup leaks) owner)).support)
    (optional : ¬ bindingRequired setup leaks rosters owner (repaired.recall owner)
      (repaired.observe (application setup leaks) owner))
    (event : (graph setup).EventId)
    (ready : repaired.application.config.cut.Ready event)
    (unsent : (runtime setup).eventRecorded leaks (repaired.recall owner) event = false)
    (before after : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ visits.map ServiceInstruction.player ++
      .player owner :: after)
    (position : original.environmentRecall.length = before.length) :
    let app := application setup leaks
    let players := Function.update ((bounds.menu (runtime setup) leaks).decodeProfile
      (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) target) owner policy
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (sourceServiceMenu setup leaks bounds rosters) owner reference (players owner)
    let remembered := memory.record (runtime setup) leaks
      (memory.shadow.inputView (runtime setup) leaks (repaired.observe app owner)) response
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
      coupling.map Prod.fst = ((runtime setup).runInteractionPlan leaks players network
        (visits.map ServiceInstruction.player) (original.respond app owner response)).bind
          (fun next => next.environmentStep app (.activate owner)) ∧
      coupling.map Prod.snd = (strategy.runJoint owner players
        (rosterScheduler setup leaks rosters network) visits.length
          (repaired.respond app owner response) remembered).bind
            (fun next => (next.1.environmentStep app (.activate owner)).map
              (fun execution => (execution, next.2))) ∧
      ∀ next ∈ coupling.support,
        BindingMemory.Frame (runtime setup) leaks next.2.2 owner next.1 next.2.1 ∧
          next.2.2 = remembered ∧
          Nonempty (((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
            (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
              (some ⟨remaining, some owner, next.2.1⟩)) ∧
          next.1.InputRecall app ∧ next.2.1.application.config.cut.Ready event ∧
          (runtime setup).eventRecorded leaks (next.2.1.recall owner) event = false ∧
          ∃ prior ∈ ((runtime setup).runInteractionPlan leaks players network
              (visits.map ServiceInstruction.player) (original.respond app owner response)).support,
            next.1 ∈ (prior.environmentStep app (.activate owner)).support := by
  classical
  intro app players strategy remembered
  let menu := sourceServiceMenu setup leaks bounds rosters
  have nonSubmit : ∀ submission, response.transmission ≠ some submission := by
    intro submission
    rcases app.silentPolicy_cases _ _ response transport with rfl; simp
  have unchanged : (runtime setup).submittedEvent? leaks response = none := by
    rcases app.silentPolicy_cases _ _ response transport with rfl; rfl
  have legal : response ∈ menu.actions owner (repaired.recall owner)
      (repaired.observe app owner) := by
    change response ∈ sourceServiceActions setup leaks bounds rosters owner _ _
    rw [sourceServiceActions, ite_eq_right optional]
    apply bounds.silent_compiled
    exact app.mem_silentPolicy_support.mpr (app.silentPolicy_cases _ _ response transport)
  obtain ⟨responded⟩ := menu.trace_respond (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network) (remaining + 1 + visits.length) repaired owner
      response trace legal
  obtain ⟨coupling, first, second, related⟩ := repair_next_owner_opportunity setup leaks bounds
    rosters network source target agrees owner policy reference remembered
      (original.respond app owner response) (repaired.respond app owner response)
      (frame.transport_response response nonSubmit) remaining visits absent responded before after
      split (by rw [app.respond_environmentRecall]; exact position)
  refine ⟨coupling, first, second, ?_⟩
  intro next supported
  obtain ⟨paired, memoryEq, nextTrace, prior, priorSupport, sampled⟩ := related next supported
  have recalled := (runtime setup).runInteractionPlan_inputRecall leaks players network
    (visits.map ServiceInstruction.player) (original.respond app owner response) prior
      (app.respond_inputRecall original owner response leftRecall) priorSupport
  have currentRecall := app.environment_inputRecall prior next.1 (.activate owner) recalled sampled
  have service := (runtime setup).player_window_application leaks players network visits
    (original.respond app owner response) prior priorSupport
  have currentApplication : next.1.application.publicView = original.application.publicView := by
    rw [ReactiveApplication.Execution.activation_samples, PMF.support_map] at sampled
    obtain ⟨selected, _, same⟩ := sampled
    rw [← same]
    exact service.2.trans ((runtime setup).reactive_respond_application leaks original owner
      response).2
  have currentOwn : next.1.recall owner = (original.respond app owner response).recall owner := by
    rw [app.environmentStep_recall prior next.1 (.activate owner) sampled]
    exact foreign_roster_recall (runtime setup) leaks players network owner visits absent
      (original.respond app owner response) prior priorSupport
  refine ⟨paired, memoryEq, nextTrace, currentRecall, ?_, ?_, prior, priorSupport, sampled⟩
  · exact ready_of_publicView_eq paired.publicView.symm
      (ready_of_publicView_eq currentApplication (ready_of_publicView_eq frame.publicView ready))
  · rw [← (runtime setup).eventRecorded_congr leaks _ _ paired.submissions event, currentOwn,
      (runtime setup).eventRecorded_respond_other leaks original owner owner response event
        (by intro _; rw [unchanged]; simp),
      (runtime setup).eventRecorded_congr leaks _ _ frame.submissions event]
    exact unsent

end Vegas
