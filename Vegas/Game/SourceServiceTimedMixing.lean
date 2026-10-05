/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedAdmissibility

/-! # Full support of the timed full-source compiler

Actual retained histories determine the current owner count. Positive timing
and supported effective source choices then cover the entire retained menu,
including deferral before the final owner visit and explicit false disclosure.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem current_slot
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event) :
    ∃ slot : Fin ((rosters event).count who),
      (control.execution.recall who).length = rosterOffset setup rosters who event + slot.val ∧
      (control.execution.observe (application setup leaks) who).application.publicView.EventReady
        event := by
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  obtain ⟨selectedEvent, visit, initial, selected, _, Γ, names, program, programProfile, source,
      refs, embedding, refsBefore, _, _, _, boundary, prior, sample, checkpoint, sole, reached,
      _, sampled, _, publicEq, _, _⟩ :=
    sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
      network (failureProfile setup.program) who control trace active
  have eventEq : selectedEvent = event :=
    (sole.2 event ((control.execution.application.publicView_eventReady event).mpr ready)).symm
  subst selectedEvent
  let slot : Fin ((rosters event).count who) :=
    ⟨((rosters event).take visit).count who, roster_count_before selected⟩
  refine ⟨slot, ?_, ?_⟩
  · have count := fixed_plan_response_counts setup leaks network menu.uniformResponses
      (((rosters event).take visit).map ServiceInstruction.player)
      (by intro member; obtain ⟨_, _, impossible⟩ := List.mem_map.mp member; cases impossible)
      boundary prior reached who
    simp only [List.filterMap_map, instructionActor, Function.comp_def, List.filterMap_some,
      checkpoint.response_offset event rfl who] at count
    rw [sampled]
    exact count
  · change control.execution.application.publicView.EventReady event
    rw [publicEq]
    exact (boundary.application.publicView_eventReady event).mpr (checkpoint.ready event rfl)

omit [Fintype Player] in
private theorem opportunity_source
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : BehavioralProfile setup.program) (who : Player) (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (unsent : (runtime setup).eventRecorded leaks past event = false)
    (response : (application setup leaks).Action)
    (supported : response ∈ (sourceServicePolicy setup leaks profile who past view).support) :
    response ∈ (sourceServiceOpportunity setup leaks profile who event past view).support := by
  simp only [sourceServiceOpportunity, unsent, Bool.false_eq_true, ↓reduceIte,
    PMF.support_bind]
  refine Set.mem_iUnion₂.mpr ⟨response, supported, ?_⟩
  split
  · rename_i silent
    have same : response = ⟨none⟩ := by cases response; cases silent; rfl
    rw [same]
    exact (application setup leaks).silentPolicy_support past view
  · exact (PMF.mem_support_pure_iff _ _).mpr rfl

private theorem required_choices
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (witness : (application setup leaks).Action)
    (present : witness ∈ bounds.requiredDecisionActions (runtime setup) leaks who past view)
    (nonsilent : witness ≠ ⟨none⟩)
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.requiredDecisionActions (runtime setup) leaks who past view) :
    response ∈ bounds.decisionActions (runtime setup) leaks who past view := by
  classical
  dsimp only [MessageBounds.requiredDecisionActions] at present member
  split at present
  · rename_i nonempty
    rw [ite_eq_left nonempty] at member
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp member).1).1
  · exact False.elim (nonsilent (Finset.mem_singleton.mp present))

private theorem required_decision
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some who)
    (unsent : (runtime setup).eventRecorded leaks (control.execution.recall who) event = false)
    (required : decisionRequired setup leaks rosters who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who))
    (response : (application setup leaks).Action)
    (member : response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who)) :
    response ∈ bounds.decisionActions (runtime setup) leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) := by
  classical
  let app := application setup leaks
  let past := control.execution.recall who
  let view := control.execution.observe app who
  change decisionRequired setup leaks rosters who past view at required
  have memberRequired : response ∈
      bounds.requiredDecisionActions (runtime setup) leaks who past view := by
    change response ∈ sourceServiceActions setup leaks bounds rosters who past view at member
    simpa only [sourceServiceActions, ite_eq_left required] using member
  have serving := ownTurn?_of_ready setup control.execution.application ready owned
  obtain ⟨other, otherTurn, _, ready, _, last⟩ := required
  have same : other = event := Option.some.inj (otherTurn.symm.trans serving)
  subst other
  obtain ⟨action, supported⟩ :=
    (sourceServiceOpportunity setup leaks profile who event past view).support_nonempty
  have covered := sourceServiceOpportunity_at_history setup leaks bounds values initialValues
    capacity rosters opportunities network profile permitted who control trace active event
      serving owned unsent action supported
  have actionRequired : action ∈
      bounds.requiredDecisionActions (runtime setup) leaks who past view := by
    have permittedAction := covered.1
    change action ∈ sourceServiceActions setup leaks bounds rosters who past view at permittedAction
    have selectedRequired : decisionRequired setup leaks rosters who past view :=
      ⟨event, serving, owned, ready, unsent, last⟩
    simpa only [sourceServiceActions, ite_eq_left selectedRequired] using permittedAction
  have nonsilent : action ≠ ⟨none⟩ := by
    intro silent
    have submitted := covered.2
    rw [silent] at submitted
    cases submitted
  exact required_choices setup leaks bounds who past view action actionRequired nonsilent
    response memberRequired

/-- Every retained physical choice has positive probability at every actual
native information site under supported effective source choices and positive
timing. No support condition is imposed on impossible private inputs. -/
theorem sourceServiceTimedPolicy_supported
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (timing : TimingLaw setup rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (full : ∀ player, (profile player).SupportsEffectiveChoices setup.program
      (CommitmentInterface.values setup.program) [] (Revelations.initial setup.context))
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (response : (application setup leaks).Action)
    (member : response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who)) :
    response ∈ (sourceServiceTimedPolicy setup leaks rosters timing profile who
      (control.execution.recall who)
      (control.execution.observe (application setup leaks) who)).support := by
  classical
  let app := application setup leaks
  let past := control.execution.recall who
  let view := control.execution.observe app who
  obtain ⟨event, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, checkpoint, _⟩ :=
    sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
      network profile who control trace active
  have controlReady : control.execution.application.config.cut.Ready event :=
    (ready_iff_rank setup _ event.val checkpoint.ordered event).mpr rfl
  have sole := soleReady_of_ready setup control.execution.application controlReady
  have ordinary := sourceServiceMenu_in_compiled setup leaks bounds rosters who _ _ member
  change response ∈ bounds.compiledActions (runtime setup) leaks who past view at ordinary
  change response ∈ (sourceServiceTimedPolicy setup leaks rosters timing profile who
    past view).support
  by_cases owned : (graph setup).actor? event = some who
  · have serving : view.application.publicView.ownTurn? who = some event :=
      PublicView.ownTurn?_of_ownTurn _ who event (sole.ownTurn owned)
    by_cases recorded : (runtime setup).eventRecorded leaks past event = true
    · rw [sourceServiceTimedPolicy_recorded setup leaks rosters timing profile who past view
        event serving recorded]
      rcases Finset.mem_union.mp (Finset.mem_inter.mp ordinary).1 with decision | silenced
      · have first := (Finset.mem_filter.mp decision).2
        rcases bounds.compiled_current_response (runtime setup) leaks who past view
          response ordinary with transport | ⟨named, selectedNamed, _, submitted⟩
        · exact transport
        · cases Option.some.inj (selectedNamed.symm.trans serving)
          have denied := (runtime setup).firstSubmission_false_of_recorded leaks past event
            recorded response submitted
          simp only [denied, Bool.false_eq_true] at first
      · exact (application setup leaks).mem_silentPolicy_support.mpr
          (Finset.mem_singleton.mp silenced)
    · have unsent : (runtime setup).eventRecorded leaks past event = false :=
        Bool.eq_false_iff.mpr recorded
      obtain ⟨current, count, ready⟩ := current_slot setup leaks bounds values capacity rosters
        opportunities network who control trace active event controlReady
      change past.length = rosterOffset setup rosters who event + current.val at count
      have currentSupported := sourceServiceTimedPolicy_future_supported setup leaks bounds
        values
        capacity rosters opportunities network profile who control trace active
          event controlReady owned
          unsent (timing event who owned) current (timingFull event who owned current) count.le
      simp only [sourceServiceTimedPolicy, serving, dite_eq_left owned]
      have selected (supported : response ∈
          (sourceServiceOpportunity setup leaks profile who event past view).support) :
          response ∈ ((app.policyMixture (timing event who owned)
            (sourceServiceTimedFamily setup leaks rosters profile who event)).policy
              past view).support := by
        apply app.policyMixture_action_support _ _ past view current response currentSupported
        simpa only [sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy,
          Option.map_some, ← count, ↓reduceIte] using supported
      by_cases required : decisionRequired setup leaks rosters who past view
      · have decision := required_decision setup leaks bounds values initialValues capacity rosters
          opportunities network profile permitted who control trace active event controlReady owned
            unsent required response member
        apply selected
        exact opportunity_source setup leaks profile who event past view unsent response
          (sourceService_decision_supported setup leaks bounds values capacity rosters opportunities
            network profile full who control trace active
              event controlReady owned response decision)
      · rcases sourceService_response_supported setup leaks bounds values capacity rosters
          opportunities network profile full who control trace active response member with
          silenced | source
        · by_cases future : current.val + 1 < (rosters event).count who
          · let next : Fin ((rosters event).count who) := ⟨current.val + 1, future⟩
            have later : past.length ≤ rosterOffset setup rosters who event + next.val := by
              dsimp only [next]
              omega
            have nextSupported := sourceServiceTimedPolicy_future_supported setup leaks bounds
              values
              capacity rosters opportunities network profile who control trace active
                event controlReady
                owned unsent (timing event who owned) next (timingFull event who owned next) later
            apply app.policyMixture_action_support _ _ past view next response nextSupported
            have waiting : some (rosterOffset setup rosters who event + next.val) ≠
                some past.length := by
              dsimp only [next]
              intro equal
              have := Option.some.inj equal
              omega
            simpa only [sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy,
              Option.map_some, ite_eq_right waiting] using silenced
          · have final : past.length + 1 =
                rosterOffset setup rosters who event + (rosters event).count who := by
              have within := current.isLt
              omega
            exact False.elim (required ⟨event, serving, owned, ready, unsent, final⟩)
        · exact selected (opportunity_source setup leaks profile who event past view
            unsent response source)
  · have idle : view.application.publicView.ownTurn? who = none := sole.ownTurn?_foreign owned
    simp only [sourceServiceTimedPolicy, idle]
    exact bounds.compiled_foreign_transport (runtime setup) leaks who past view idle response
      ordinary

/-- An original source policy with full support at abstract inputs induces
one genuinely fully mixed retained native strategy under positive shared
timing. Its private-intention normalization is not required to be fully mixed
in the original source game. -/
theorem sourceServiceTimedProfile_fullyMixed
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (timing : TimingLaw setup rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (source : Profile (setup.informationModel
      (CommitmentInterface.values setup.program)).behavioralSignature)
    (full : ∀ who info, FullSupport (source who info)) :
    (InformationModel.BehavioralAssessment.ofStrategy
      (sourceServiceTimedProfile setup leaks bounds rosters network timing
        (setup.decodeBehavioralProfile
          (CommitmentInterface.values setup.program) source))).IsFullyMixed := by
  let admission := CommitmentInterface.values setup.program
  let original := setup.decodeBehavioralProfile admission source
  let normalized := normalizeDisclosureProfile setup.program []
    (Revelations.initial setup.context) original
  have permitted (who : Player) : (normalized who).Admitted setup.program admission :=
    normalized_sourceService_admitted setup original
      (fun player => ((setup.behavioralPolicyEquiv admission player).symm (source player)).2) who
  have supported (who : Player) : (normalized who).SupportsEffectiveChoices setup.program
      admission [] (Revelations.initial setup.context) :=
    sourceService_normalized_support setup source full who
  exact ReactiveApplication.ResponseMenu.restrictProfile_fullSupport
    (sourceServiceMenu setup leaks bounds rosters) (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
    (sourceServiceTimedPolicy setup leaks rosters timing normalized)
    (sourceServiceTimedPolicy_admissible setup leaks bounds values initialValues capacity rosters
      opportunities network timing timingFull normalized permitted)
    (fun who control trace active response member =>
      sourceServiceTimedPolicy_supported setup leaks bounds values initialValues capacity rosters
        opportunities network timing timingFull normalized permitted supported who control trace
          active response member)

end Vegas
