/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterDecisionSupport
import Vegas.Game.RevealServicePrefixChoice
import Vegas.Game.RevealServiceRosterCoverage
import Vegas.Game.SourcePrefixKernel
import Vegas.Game.RevealServiceRosterCounts
import Vegas.Pending.ReactiveServiceRecall

/-! # Source information and opening data at legal roster decisions -/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem PublicPrefixCheckpoint.grant
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} {refs : ContextRefs (graph setup).layout Γ}
    {revelations : Revelations Γ}
    {outputs : ∀ event, EventGraph.FieldRef (graph setup).layout (outputLayout program event)}
    {offset count : Nat} {state : ProtocolState program}
    {execution : (application setup leaks).Execution}
    (related : PublicPrefixCheckpoint setup leaks initial program refs revelations outputs
      offset count state execution)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) (event : (graph setup).EventId) :
    ∃ granted, PublicPrefixCheckpoint setup leaks initial program refs revelations outputs
        offset count state granted ∧
      granted.application.serviceGrant = some event ∧ granted.recall = execution.recall ∧
      granted.network = execution.network ∧
      (runtime setup).runInteractionPlan leaks players network [.grant event] execution =
        FinDist.pure granted := by
  let app := application setup leaks
  let granted : app.Execution := { execution with
    application := { execution.application with serviceGrant := some event }
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .application (.grant event)⟩] }
  have law : (runtime setup).runInteractionPlan leaks players network [.grant event] execution =
      FinDist.pure granted := by
    simp only [runInteractionPlan, interactionStep, interactionInstruction, FinDist.pure_bind,
      ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
      reactiveApplication, environmentStep, FinDist.map_pure,
      ReactiveApplication.Command.actor?, ReactiveApplication.resume]
    rfl
  refine ⟨granted, ?_, rfl, rfl, rfl, law⟩
  apply PublicPrefixCheckpoint.map_execution execution granted _ program refs revelations outputs
    offset count state related
  intro context source sourceRefs rank checkpoint
  obtain ⟨other, preserved, _, _, _, otherLaw⟩ := checkpoint.grant players network event
  have same : granted ∈ (FinDist.pure other).support := by
    rw [← otherLaw, law]
    exact FinDist.mem_support_pure.mpr rfl
  cases FinDist.mem_support_pure.mp same
  exact preserved

/-- The active roster occurrence follows strictly fewer occurrences of the
same player. This counts actual responses, including silence and replay. -/
theorem roster_count_before {visits : List Player} {slot : Nat} {who : Player}
    (selected : visits[slot]? = some who) :
    (visits.take slot).count who < visits.count who := by
  induction visits generalizing slot with
  | nil => simp at selected
  | cons first rest ih =>
      cases slot with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
          subst first
          simp
      | succ slot =>
          simp only [List.getElem?_cons_succ] at selected
          simpa only [List.take_succ_cons, List.count_cons, beq_iff_eq] using
            Nat.add_lt_add_right (ih selected) (if first = who then 1 else 0)

variable [Fintype Player]

/-- Every legal retained activation is a partial roster following a genuine
source checkpoint, with the allocator and own-response counts derived from
the initialized execution. -/
theorem roster_decision_phase
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((rosterMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who) :
    ∃ event : (graph setup).EventId, ∃ slot granted prior sample initial state,
      (rosters event)[slot]? = some who ∧ initial ∈ setup.initialLaw.support ∧
      PublicPrefixCheckpoint setup leaks initial setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) (outputRef setup.program)
        0 event.val state granted ∧
      state ∈ ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program
        (fun owner => RevealOnly.uniformPolicy owner setup.program reveals)))^[event.val]
          (FinDist.pure (ProtocolState.entry setup.program
            (setup.initialConfig initial)))).support ∧
      granted.application.serviceGrant = some event ∧
      (∀ player, (granted.recall player).length = rosterOffset setup rosters player event) ∧
      granted.network.SerialsBeforeNext ∧
      granted.network.Satisfies (fun message =>
        message.id ∈ granted.network.ledger.map Message.id) ∧
      prior ∈ ((runtime setup).runInteractionPlan leaks
        (rosterMenu setup leaks bounds rosters).uniformResponses network
        (((rosters event).take slot).map ServiceInstruction.player) granted).support ∧
      control.execution = prior.sampledActivation (application setup leaks) who sample ∧
      control.execution.application = granted.application := by
  let app := application setup leaks
  let menu := rosterMenu setup leaks bounds rosters
  obtain ⟨event, slot, boundary, prior, selected, _, boundarySupport, phase, activated,
      initial, initialSupport, state, checkpoint, _, sourceSupport, clean⟩ :=
    roster_decision_source setup leaks bounds rosters network reveals openable
      who control trace active
  obtain ⟨granted, related, grant, recall, net, law⟩ :=
    checkpoint.grant menu.uniformResponses network event
  rw [runInteractionPlan_append, law, FinDist.pure_bind] at phase
  rw [ReactiveApplication.Execution.activation_samples, FinDist.support_map] at activated
  obtain ⟨sample, _, same⟩ := activated
  have unchanged := roster_run_application setup leaks bounds rosters menu.uniformResponses
    (fun player past view response supported =>
      (menu.uniformResponses_support player past view response).mp supported)
    network ((rosters event).take slot) granted prior phase
  rw [FinDist.support_bind] at boundarySupport
  obtain ⟨nativeInitial, _, reached⟩ := Set.mem_iUnion₂.mp boundarySupport
  have serials := (runtime setup).runInteractionPlan_serials leaks menu.uniformResponses network
    (rosterPlanPrefix setup rosters event.val)
    (ReactiveApplication.Execution.initial app nativeInitial) boundary
    MessageNetwork.SerialsBeforeNext.empty reached
  refine ⟨event, slot, granted, prior, sample, initial, state, selected, initialSupport,
    related, sourceSupport, grant, ?_, ?_, ?_, phase, same.symm, ?_⟩
  · intro player
    have counts := roster_prefix_response_counts setup leaks rosters network menu.uniformResponses
      event (ReactiveApplication.Execution.initial app nativeInitial) boundary reached player
    rw [recall]
    simpa only [ReactiveApplication.Execution.initial, List.length_nil, Nat.zero_add] using counts
  · rwa [net]
  · rwa [net]
  · rw [← same]
    exact unchanged

/-- A supported source prefix determines a genuine source information site.
No compiled strategy or native full-mixing premise is used to witness it. -/
theorem roster_source_site
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (reveals : setup.program.RevealOnly) (admission : CommitmentInterface setup.program)
    (who : Player) (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (initial : State L setup.context) (initialSupport : initial ∈ setup.initialLaw.support)
    (state : ProtocolState setup.program) (execution : (application setup leaks).Execution)
    (related : PublicPrefixCheckpoint setup leaks initial setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) (outputRef setup.program) 0 event.val state execution)
    (supported : state ∈ ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program
      (fun owner => RevealOnly.uniformPolicy owner setup.program reveals)))^[event.val]
        (FinDist.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).support) :
    ∃ site : (setup.informationModel admission).InformationSite who,
      site.1 = setup.protocolObserve who (some state) := by
  obtain ⟨history, _, stateEq⟩ := setup.exists_history_of_prefix_support admission
    (fun owner => RevealOnly.uniformPolicy owner setup.program reveals)
    (fun owner => RevealOnly.uniformPolicy_admitted owner setup.program reveals admission)
    initial initialSupport event.val state supported
  have acting := PublicPrefixCheckpoint.actor who setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputRef setup.program) 0 event.val state execution
    related event.isLt
  rw [eventOwner?_eq_actor] at acting
  change ProtocolView.actor who setup.program (ProtocolState.observe who setup.program state) =
    (graph setup).actor? event at acting
  rw [owned] at acting
  have active : (setup.executionProtocol admission).active history.state who := by
    rw [stateEq]
    exact acting
  have running : ¬ (setup.executionProtocol admission).terminal history.state := by
    rw [stateEq]
    intro stopped
    have absent := ProtocolState.terminal_actor_none who setup.program state stopped
    rw [acting] at absent
    cases absent
  obtain ⟨joint, legal⟩ := history.exists_legal_of_not_terminal running
  obtain ⟨action, chosen⟩ :=
    ((setup.executionProtocol admission).legalOption_of_legal legal who).exists_eq_some_of_active
      (joint who) active
  have allowed : some action ∈ (setup.informationModel admission).menu who
      ((setup.informationModel admission).infoOf who history.trace) := by
    apply ((setup.informationModel admission).menu_adequate who history.trace (some action)).mpr
    have localLegal := (setup.executionProtocol admission).legalOption_of_legal legal who
    rwa [chosen] at localLegal
  refine ⟨(setup.informationModel admission).informationSite who history action running allowed, ?_⟩
  exact (setup.protocol_info admission who history.trace).trans
    (congrArg (setup.protocolObserve who) stateEq)

end Vegas.SourceProgram.RevealService
