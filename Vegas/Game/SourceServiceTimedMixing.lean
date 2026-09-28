/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedAdmissibility

/-! # Full support of the timed full-source compiler

Actual retained histories determine the current owner count. Positive timing
and supported effective source choices then cover the entire retained menu,
including silence after failed guarded disclosure and pending-envelope replay.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem current_slot
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (event : (graph setup).EventId)
    (granted : control.execution.application.serviceGrant = some event) :
    ∃ slot : Fin ((rosters event).count who),
      (control.execution.recall who).length = rosterOffset setup rosters who event + slot.val ∧
      (control.execution.observe (application setup leaks) who).application.publicView.EventReady
        event := by
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  obtain ⟨selectedEvent, visit, initial, selected, _, Γ, names, program, programProfile, source,
      refs, embedding, refsBefore, _, _, _, boundary, prior, sample, checkpoint, grant, reached,
      _, sampled, _, publicEq, _, _⟩ :=
    sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
      network (failureProfile setup.program) who control trace active
  have eventEq : selectedEvent = event := Option.some.inj
    (((congrArg PublicView.serviceGrant publicEq).trans grant).symm.trans granted)
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
private theorem nonbinding_silence
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (granted : view.application.publicView.serviceGrant = some event)
    (owned : (graph setup).actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (nonbinding : ∀ payload, (graph setup).outputLayout event ≠ .binding who payload) :
    (⟨none⟩ : (application setup leaks).Action) ∈
      bounds.decisionActions (runtime setup) leaks who past view := by
  classical
  simp only [MessageBounds.decisionActions, granted, owned, ready, and_self, ↓reduceIte]
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq => exact Finset.mem_singleton_self _
  | bind owner payload outputEq codeEq =>
      have actor : (graph setup).actor? event = some owner := by
        change EventGraph.EventCode.actor ((graph setup).nodes event) = _
        rw [← EventGraph.EventCode.actor_cast outputEq ((graph setup).nodes event), codeEq]
        rfl
      cases Option.some.inj (owned.symm.trans actor)
      exact False.elim (nonbinding payload outputEq)
  | resolve owner payload binding checks outputEq codeEq =>
      refine Finset.mem_image.mpr ⟨false, Finset.mem_univ _, ?_⟩
      simp only [serviceDecision, reactiveDecision, node, reactiveResolutionPacket,
        cast_cast, cast_eq, Bool.false_eq_true, ↓reduceIte,
        disclosureSubmission_normalize_withhold]
      rfl

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
    FinDist.support_bind]
  refine Set.mem_iUnion₂.mpr ⟨response, supported, ?_⟩
  split
  · rename_i silent
    have same : response = ⟨none⟩ := by cases response; cases silent; rfl
    rw [same]
    exact (application setup leaks).replayPolicy_support past view none
      (Finset.mem_insert_self _ _)
  · exact FinDist.mem_support_pure.mpr rfl

omit [Fintype Player] in
private theorem opportunity_replay
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : BehavioralProfile setup.program) (who : Player) (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (unsent : (runtime setup).eventRecorded leaks past event = false)
    (silence : (⟨none⟩ : (application setup leaks).Action) ∈
      (sourceServicePolicy setup leaks profile who past view).support)
    (response : (application setup leaks).Action)
    (supported : response ∈ ((application setup leaks).replayPolicy past view).support) :
    response ∈ (sourceServiceOpportunity setup leaks profile who event past view).support := by
  simp only [sourceServiceOpportunity, unsent, Bool.false_eq_true, ↓reduceIte,
    FinDist.support_bind]
  exact Set.mem_iUnion₂.mpr ⟨⟨none⟩, silence, by simpa only [↓reduceIte] using supported⟩

private theorem required_choices
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (witness : (application setup leaks).Action)
    (present : witness ∈ bounds.requiredBindingActions (runtime setup) leaks who past view)
    (nonsilent : witness ≠ ⟨none⟩)
    (response : (application setup leaks).Action)
    (member : response ∈ bounds.requiredBindingActions (runtime setup) leaks who past view) :
    response ∈ bounds.decisionActions (runtime setup) leaks who past view := by
  classical
  dsimp only [MessageBounds.requiredBindingActions] at present member
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
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (event : (graph setup).EventId)
    (granted : control.execution.application.serviceGrant = some event)
    (owned : (graph setup).actor? event = some who)
    (unsent : (runtime setup).eventRecorded leaks (control.execution.recall who) event = false)
    (required : bindingRequired setup leaks rosters who (control.execution.recall who)
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
  change bindingRequired setup leaks rosters who past view at required
  have memberRequired : response ∈
      bounds.requiredBindingActions (runtime setup) leaks who past view := by
    change response ∈ sourceServiceActions setup leaks bounds rosters who past view at member
    simpa only [sourceServiceActions, ite_eq_left required] using member
  obtain ⟨other, payload, otherGrant, binding, _, ready, _, last⟩ := required
  have same : other = event := Option.some.inj (otherGrant.symm.trans granted)
  subst other
  obtain ⟨action, supported⟩ :=
    (sourceServiceOpportunity setup leaks profile who event past view).support_nonempty
  have covered := sourceServiceOpportunity_at_history setup leaks bounds values initialValues
    capacity rosters opportunities network profile permitted who control trace active event
      granted owned unsent action supported
  have actionRequired : action ∈
      bounds.requiredBindingActions (runtime setup) leaks who past view := by
    have permittedAction := covered.1
    change action ∈ sourceServiceActions setup leaks bounds rosters who past view at permittedAction
    have selectedRequired : bindingRequired setup leaks rosters who past view :=
      ⟨event, payload, granted, binding, owned, ready, unsent, last⟩
    simpa only [sourceServiceActions, ite_eq_left selectedRequired] using permittedAction
  have nonsilent : action ≠ ⟨none⟩ := by
    intro silent
    have submitted := covered.2 payload binding
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
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (timing : TimingLaw setup rosters)
    (timingFull : ∀ event who owned, (timing event who owned).FullSupport)
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
  obtain ⟨event, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, grant,
      _, _, _, _, publicEq, _, _⟩ :=
    sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
      network profile who control trace active
  have granted : view.application.publicView.serviceGrant = some event :=
    (congrArg PublicView.serviceGrant publicEq).trans grant
  have ordinary := sourceServiceMenu_in_compiled setup leaks bounds rosters who _ _ member
  change response ∈ bounds.compiledActions (runtime setup) leaks who past view at ordinary
  change response ∈ (sourceServiceTimedPolicy setup leaks rosters timing profile who
    past view).support
  by_cases owned : (graph setup).actor? event = some who
  · by_cases recorded : (runtime setup).eventRecorded leaks past event = true
    · rw [sourceServiceTimedPolicy_recorded setup leaks rosters timing profile who past view
        event granted recorded]
      rcases Finset.mem_union.mp (Finset.mem_inter.mp ordinary).1 with decision | replay
      · have first := (Finset.mem_filter.mp decision).2
        rcases bounds.compiled_current_response (runtime setup) leaks who past view event granted
          response ordinary with transport | ⟨_, submitted⟩
        · exact transport
        · have denied := (runtime setup).firstSubmission_false_of_recorded leaks past event
            recorded response submitted
          simp only [denied, Bool.false_eq_true] at first
      · exact FinDist.mem_supportFinset.mp replay
    · have unsent : (runtime setup).eventRecorded leaks past event = false :=
        Bool.eq_false_iff.mpr recorded
      obtain ⟨current, count, ready⟩ := current_slot setup leaks bounds values capacity rosters
        opportunities network who control trace active event granted
      change past.length = rosterOffset setup rosters who event + current.val at count
      have currentSupported := sourceServiceTimedPolicy_future_supported setup leaks bounds
        values
        capacity rosters opportunities network profile who control trace active event granted owned
          unsent (timing event who owned) current (timingFull event who owned current) count.le
      simp only [sourceServiceTimedPolicy, granted, dite_eq_left owned]
      have selected (supported : response ∈
          (sourceServiceOpportunity setup leaks profile who event past view).support) :
          response ∈ ((app.policyMixture (timing event who owned)
            (sourceServiceTimedFamily setup leaks rosters profile who event)).policy
              past view).support := by
        apply app.policyMixture_action_support _ _ past view current response currentSupported
        simpa only [sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy,
          Option.map_some, ← count, ↓reduceIte] using supported
      by_cases required : bindingRequired setup leaks rosters who past view
      · have decision := required_decision setup leaks bounds values initialValues capacity rosters
          opportunities network profile permitted who control trace active event granted owned
            unsent required response member
        apply selected
        exact opportunity_source setup leaks profile who event past view unsent response
          (sourceService_decision_supported setup leaks bounds values capacity rosters opportunities
            network profile full who control trace active event granted owned response decision)
      · rcases sourceService_response_supported setup leaks bounds values capacity rosters
          opportunities network profile full who control trace active response member with
          replay | source
        · by_cases future : current.val + 1 < (rosters event).count who
          · let next : Fin ((rosters event).count who) := ⟨current.val + 1, future⟩
            have later : past.length ≤ rosterOffset setup rosters who event + next.val := by
              dsimp only [next]
              omega
            have nextSupported := sourceServiceTimedPolicy_future_supported setup leaks bounds
              values
              capacity rosters opportunities network profile who control trace active event granted
                owned unsent (timing event who owned) next (timingFull event who owned next) later
            apply app.policyMixture_action_support _ _ past view next response nextSupported
            have waiting : some (rosterOffset setup rosters who event + next.val) ≠
                some past.length := by
              dsimp only [next]
              intro equal
              have := Option.some.inj equal
              omega
            simpa only [sourceServiceTimedFamily, ReactiveApplication.scheduledPolicy,
              Option.map_some, ite_eq_right waiting] using replay
          · have final : past.length + 1 =
                rosterOffset setup rosters who event + (rosters event).count who := by
              have within := current.isLt
              omega
            have nonbinding : ∀ payload,
                (graph setup).outputLayout event ≠ .binding who payload := by
              intro payload binding
              exact required ⟨event, payload, granted, binding, owned, ready, unsent, final⟩
            have silence := sourceService_decision_supported setup leaks bounds values capacity
              rosters opportunities network profile full who control trace active event granted
              owned ⟨none⟩ (nonbinding_silence setup leaks bounds who past view event
                granted owned ready nonbinding)
            exact selected (opportunity_replay setup leaks profile who event past view
              unsent silence response replay)
        · exact selected (opportunity_source setup leaks profile who event past view
            unsent response source)
  · simp only [sourceServiceTimedPolicy, granted, dite_eq_right owned]
    exact bounds.compiled_foreign_transport (runtime setup) leaks who past view event
      granted owned response ordinary

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
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (timing : TimingLaw setup rosters)
    (timingFull : ∀ event who owned, (timing event who owned).FullSupport)
    (source : Profile (setup.informationModel
      (CommitmentInterface.values setup.program)).behavioralSignature)
    (full : ∀ who info, (source who info).FullSupport) :
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

end Vegas.SourceProgram.RevealService
