/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePrefixSupport
import Vegas.Game.RevealServiceRosterDecisionSupport
import Vegas.Pending.ReactiveResolutionEvidence

/-! # Actual full-source decision histories start at typed boundaries

The uniformly supported retained menu witnesses every legal history. Its
actual scheduler prefix is then factored at the current phase boundary, where
the full source-prefix induction supplies both semantic and runtime facts.
No prescribed source strategy or probability of the information site is used.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every actual retained decision has a complete typed source boundary and
the exact partial roster leading to its native private observation. -/
theorem sourceService_decision_boundary
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (profile : BehavioralProfile setup.program)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who) :
    ∃ event : (graph setup).EventId, ∃ slot initial,
      (rosters event)[slot]? = some who ∧ initial ∈ setup.initialLaw.support ∧
      ∃ (Γ : SourceCtx Player L) (names : Finset VarId)
        (remaining : SourceProgram Player L Γ names)
        (remainingProfile : BehavioralProfile remaining)
        (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
        (embedding : OutputEmbedding (inputLayout setup.context)
          (outputLayout setup.program) remaining)
        (refsBefore : ContextRefsBefore refs embedding),
        CompiledPolicySuffix setup.program profile remaining remainingProfile refs
          source.revelations source.registry embedding refsBefore event.val ∧
        ((∀ player, (profile player).Admitted setup.program
          (CommitmentInterface.values setup.program)) →
            ∀ player, (remainingProfile player).Admitted remaining
              (CommitmentInterface.values remaining)) ∧
        (((∀ player, (profile player).SupportsEffectiveChoices setup.program
          (CommitmentInterface.values setup.program) [] (Revelations.initial setup.context)) →
            ∀ player, (remainingProfile player).SupportsEffectiveChoices remaining
              (CommitmentInterface.values remaining) source.registry source.revelations) ∧
          ((∀ player, (profile player).EffectiveDisclosures setup.program []
            (Revelations.initial setup.context)) →
              ∀ player, (remainingProfile player).EffectiveDisclosures remaining
                source.registry source.revelations) ∧
          ∃ lift : ProtocolState remaining → ProtocolState setup.program,
            ((∀ tailState, ProtocolState.behavioralStateStep setup.program profile
              (lift tailState) =
                (ProtocolState.behavioralStateStep remaining remainingProfile tailState).map
                  lift) ∧
              (∀ tailState joint, ProtocolState.step setup.program (lift tailState) joint =
                (ProtocolState.step remaining tailState joint).map lift) ∧
              Function.Injective lift) ∧
            ∀ more store history,
              decodeSourcePrefix? setup.program
                (ContextRefs.initial setup.context (outputLayout setup.program)) []
                (Revelations.initial setup.context) (outputRef setup.program)
                (HAdd.hAdd event.val more) store history =
              (decodeSourcePrefix? remaining refs source.registry source.revelations
                embedding.ref more store history).map lift) ∧
        ∃ boundary prior sample,
          ServiceBoundary setup leaks rosters initial source refs event.val boundary ∧
          control.execution.application.publicView.SoleReady event ∧
          prior ∈ ((runtime setup).runInteractionPlan leaks
            (sourceServiceMenu setup leaks bounds rosters).uniformResponses network
            (((rosters event).take slot).map ServiceInstruction.player) boundary).support ∧
          control.execution ∈
            (prior.environmentStep (application setup leaks) (.activate who)).support ∧
          control.execution = prior.sampledActivation (application setup leaks) who sample ∧
          control.execution.application.config = boundary.application.config ∧
          control.execution.application.publicView = boundary.application.publicView ∧
          SourceCheckpoint setup source refs event.val control.execution.application.config ∧
          control.execution.environmentRecall.length =
            (rosterPlanPrefix setup rosters event.val).length + slot + 1 ∧
          (runtime setup).ResolutionEvidenceOrigins leaks boundary := by
  let menu := sourceServiceMenu setup leaks bounds rosters
  obtain ⟨event, slot, boundary, prior, selected, position, boundarySupport, phase, activated⟩ :=
    roster_decision_boundary setup leaks rosters network menu who control trace active
  obtain ⟨initial, initialSupport, _, _, _, Γ, names, remaining, remainingProfile, source,
      refs, embedding, refsBefore, aligned, admitted, lift, _, commutes, transport, effective,
      supported, checkpoint⟩ :=
    initialized_sourceService_prefix_support setup leaks bounds values capacity rosters
      opportunities menu.uniformResponses
      (fun owner past view response supported =>
        (menu.uniformResponses_support owner past view response).mp supported)
      network profile event.val event.isLt.le boundary boundarySupport
  have boundaryOrigins : (runtime setup).ResolutionEvidenceOrigins leaks boundary := by
    obtain ⟨state, stateSupport, reachedBoundary⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ boundarySupport)
    obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ stateSupport
    exact ((runtime setup).resolutionEvidenceOrigins_run leaks bounds menu.uniformResponses
      (fun owner past view response supported => sourceServiceMenu_in_compiled setup leaks bounds
        rosters owner past view ((menu.uniformResponses_support owner past view response).mp
          supported)) network _ _ boundary
      (State.initial_bindingInvariant (graph := graph setup) (setup.eventInputs initial))
      ((application setup leaks).initial_inputRecall _) MessageNetwork.Satisfies.empty
      reachedBoundary).2.2
  have sampling := activated
  rw [ReactiveApplication.Execution.activation_samples, PMF.support_map] at sampling
  obtain ⟨sample, _, same⟩ := sampling
  have unchanged := (runtime setup).player_window_application leaks menu.uniformResponses network
    ((rosters event).take slot) boundary prior phase
  have config : control.execution.application.config = boundary.application.config := by
    rw [← same]
    exact unchanged.1
  have publicEq : control.execution.application.publicView = boundary.application.publicView := by
    rw [← same]
    exact unchanged.2
  have sole : control.execution.application.publicView.SoleReady event := by
    rw [publicEq]
    exact soleReady_of_ready setup boundary.application (checkpoint.ready event rfl)
  exact ⟨event, slot, initial, selected, initialSupport, Γ, names, remaining, remainingProfile,
    source, refs, embedding, refsBefore, aligned, admitted,
    ⟨supported, effective, lift, commutes, transport⟩,
    boundary, prior, sample, checkpoint,
    sole, phase, activated, same.symm, config, publicEq,
    config.symm ▸ checkpoint.toSourceCheckpoint, position, boundaryOrigins⟩

/-- At every decision of the fixed calendar exactly one event is ready. -/
theorem sourceService_decision_sole
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
        (some control)) (active : control.actor = some who) :
    ∃ event, control.execution.application.publicView.SoleReady event ∧
      control.execution.application.config.cut.Ready event := by
  obtain ⟨event, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, sole,
      _, _, _, _, _, checkpoint, _⟩ :=
    sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
      network (failureProfile setup.program) who control trace active
  exact ⟨event, sole, (ready_iff_rank setup _ event.val checkpoint.ordered event).mpr rfl⟩

/-- Binding resources hold at every legal retained information site, including
sites reached only after deviations in an implementation. Before submission,
the actual candidate is fresh and unused and all older packets are published. -/
theorem sourceService_binding_decision_resources
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
    (ready : control.execution.application.config.cut.Ready event)
    (owner : Player) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (owned : (graph setup).actor? event = some owner) :
    control.execution.application.config.cut.Ready event ∧
      control.execution.application.WithinDeadline (runtime setup) event ∧
      control.execution.application.BindingInvariant ∧
      control.execution.InputRecall (application setup leaks) ∧
      control.execution.SerialRecall (application setup leaks) ∧
      control.execution.network.SerialsBeforeNext ∧
      ((runtime setup).eventRecorded leaks (control.execution.recall owner) event = false →
        let serial := control.execution.application.publicView.bindingCount owner
        serial < bounds.candidateCount ∧
        reactiveFreshSlot (control.execution.observe (application setup leaks) owner).application =
          some serial ∧
        control.execution.application.candidates.lookup (owner, .prepared serial) = .fresh ∧
        control.execution.application.HandleUnused (owner, .prepared serial) ∧
        control.execution.application.accepted (.inr event) = none ∧
        (∀ player, control.execution.network.nextSerial player =
          Message.distinctAuthoredCount control.execution.network.ledger player) ∧
        control.execution.network.Satisfies
          (fun message => message.id ∈ control.execution.network.ledger.map Message.id)) := by
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  obtain ⟨selectedEvent, slot, initial, _, _, Γ, names, remaining, remainingProfile, source,
      refs, embedding, refsBefore, _, _, _, boundary, prior, sample, checkpoint, sole, reached,
      activated, sampled, _, publicEq, _, _⟩ :=
    sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
      network (failureProfile setup.program) who control trace active
  have eventEq : selectedEvent = event :=
    (sole.2 event ((control.execution.application.publicView_eventReady event).mpr ready)).symm
  subst selectedEvent
  have lawful := fun player past view response supported =>
    (menu.uniformResponses_support player past view response).mp supported
  obtain ⟨ready, timely, _, binding, recalled, serialRecall, serials, unsubmitted⟩ :=
    checkpoint.binding_prefix_resources bounds menu.uniformResponses lawful network event rfl
      owner payload outputEq codeEq node owned ((rosters event).take slot) prior reached
  refine ⟨?_, ?_, ?_, app.environment_inputRecall prior control.execution (.activate who)
    recalled activated, app.environment_serialRecall prior control.execution (.activate who)
      serialRecall activated, ?_, ?_⟩
  · rw [sampled]
    exact ready
  · rw [sampled]
    exact timely
  · rw [sampled]
    exact binding
  · rw [sampled]
    exact serials.learn who sample
  · intro unsent
    have priorUnsent : (runtime setup).eventRecorded leaks (prior.recall owner) event = false := by
      rw [sampled] at unsent
      exact unsent
    obtain ⟨sameApp, selected, accounted, published⟩ := unsubmitted priorUnsent
    have currentApp : control.execution.application = boundary.application := by
      rw [sampled]
      exact sameApp
    have resources := checkpoint.binding_resources event rfl owner
    dsimp only
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [currentApp]
      exact checkpoint.binding_capacity bounds capacity event rfl owner
    · rw [sampled]
      exact selected
    · rw [currentApp]
      exact resources.2.1
    · rw [currentApp]
      exact resources.2.2.1
    · rw [currentApp]
      exact resources.2.2.2
    · rw [sampled]
      exact accounted
    · rw [sampled]
      exact published.learn who sample

/-- At an actual unsent binding opportunity, the information-local required
menu is selected exactly when the fixed roster has no later owner visit. -/
theorem sourceService_bindingRequired_iff_no_later_owner
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (owner : Player) (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some owner)
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (payload : L.Ty)
    (binding : (graph setup).outputLayout event = .binding owner payload)
    (owned : (graph setup).actor? event = some owner)
    (unsent : (runtime setup).eventRecorded leaks (control.execution.recall owner) event = false)
    (visited remaining : List Player)
    (split : rosters event = visited ++ owner :: remaining)
    (position : control.execution.environmentRecall.length =
      (rosterPlanPrefix setup rosters event.val).length + visited.length + 1) :
    bindingRequired setup leaks rosters owner (control.execution.recall owner)
      (control.execution.observe (application setup leaks) owner) ↔ owner ∉ remaining := by
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  obtain ⟨selectedEvent, slot, initial, _, _, Γ, names, program, programProfile, source,
      refs, embedding, refsBefore, _, _, _, boundary, prior, sample, checkpoint, sole, reached,
      _, sampled, _, publicEq, _, clock, _⟩ :=
    sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
      network (failureProfile setup.program) owner control trace active
  have eventEq : selectedEvent = event :=
    (sole.2 event ((control.execution.application.publicView_eventReady event).mpr ready)).symm
  subst selectedEvent
  have slotEq : slot = visited.length := by omega
  have visitedEq : (rosters event).take slot = visited := by
    rw [slotEq, split, List.take_left]
  have count := fixed_plan_response_counts setup leaks network menu.uniformResponses
    (((rosters event).take slot).map ServiceInstruction.player)
    (by intro member; obtain ⟨_, _, impossible⟩ := List.mem_map.mp member; cases impossible)
    boundary prior reached owner
  simp only [List.filterMap_map, instructionActor, Function.comp_def, List.filterMap_some,
    checkpoint.response_offset event rfl owner, visitedEq] at count
  have counted : (control.execution.recall owner).length =
      rosterOffset setup rosters owner event + visited.count owner := by
    rw [sampled]
    exact count
  have ready : (control.execution.observe app owner).application.publicView.EventReady event := by
    change control.execution.application.publicView.EventReady event
    rw [publicEq]
    exact (boundary.application.publicView_eventReady event).mpr (checkpoint.ready event rfl)
  have serving : (control.execution.observe app owner).application.publicView.ownTurn? owner =
      some event := by
    change control.execution.application.publicView.ownTurn? owner = some event
    rw [publicEq]
    exact ownTurn?_of_ready setup boundary.application (checkpoint.ready event rfl) owned
  rw [bindingRequired_iff_no_later_owner setup leaks rosters owner _ _ event payload serving
    binding owned ready unsent visited remaining split counted]
  exact List.count_eq_zero

end Vegas
