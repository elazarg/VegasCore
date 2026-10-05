/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceExecution
import Vegas.Game.SourceServiceCoverage
import Vegas.Game.SourceServiceDecisionSupport
import Vegas.Source.DisclosureContinuation
import Vegas.Game.SourceServiceRestrictedEvaluation

/-! # Exact execution of the total full-source compiler

The finite policy is total at arbitrary inputs. Its equality with the physical
source policy is proved at every legal retained history from the actual
source-prefix support theorem and current runtime bounds.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Actual source opportunities are legal at every retained unsent owner site.
Every supported source decision submits, even before the final visit. -/
theorem sourceServiceOpportunity_at_history
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
    (serving : control.execution.application.publicView.ownTurn? who = some event)
    (owned : (graph setup).actor? event = some who)
    (unsent : (runtime setup).eventRecorded leaks (control.execution.recall who) event = false)
    (response : (application setup leaks).Action)
    (supported : response ∈ (sourceServiceOpportunity setup leaks profile who event
      (control.execution.recall who)
      (control.execution.observe (application setup leaks) who)).support) :
    response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who) ∧
    (runtime setup).submittedEvent? leaks response = some event := by
  classical
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  let horizon := (rosterPlan setup rosters).length
  let scheduler := rosterScheduler setup leaks rosters network
  obtain ⟨selectedEvent, slot, initial, _selected, _initialSupport, Γ, names, remaining,
      remainingProfile, source, refs, embedding, refsBefore, aligned, inherited, _,
      turn, prior, sample, boundary, _sole, _phase, _activated, _sampled, _config,
      _publicEq, checkpoint, _position⟩ :=
    sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
      network profile who control trace active
  have selectedReady : control.execution.application.config.cut.Ready selectedEvent :=
    (ready_iff_rank setup _ selectedEvent.val checkpoint.ordered selectedEvent).mpr rfl
  have eventReady := (PublicView.ownTurn?_spec _ who event serving).1
  have eventEq : selectedEvent = event :=
    ((soleReady_of_ready setup control.execution.application selectedReady).2 event
      eventReady).symm
  subst selectedEvent
  have ready := selectedReady
  cases remaining with
  | ret result =>
      have count := aligned.graphSuffix.countEq
      simp only [eventCount, Nat.add_zero] at count
      have inside := event.isLt
      change event.val < eventCount setup.program at inside
      omega
  | sample name fresh law next =>
      let index : Fin (eventCount (.sample name fresh law next)) := ⟨0, by simp [eventCount]⟩
      have same : embedding.event index = event := by
        apply Fin.ext
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have actor := aligned.actorEq index
      rw [same] at actor
      change (graph setup).actor? event = none at actor
      rw [owned] at actor
      cases actor
  | @commit Γ names name owner payload fresh guard next =>
      let index : Fin (eventCount (.commit name owner fresh guard next)) :=
        ⟨0, by simp [eventCount]⟩
      have same : embedding.event index = event := by
        apply Fin.ext
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have actor := aligned.actorEq index
      rw [same] at actor
      change (graph setup).actor? event = some owner at actor
      cases Option.some.inj (owned.symm.trans actor)
      have outputEq : (graph setup).outputLayout event = .binding who payload := by
        change outputLayout setup.program event = _
        simpa [← same, index, outputLayout, eventCount] using embedding.layout_eq index
      have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes event) = .bind who _ := by
        have transport (other : (graph setup).EventId)
            (located : embedding.event index = other)
            (kind : (graph setup).outputLayout other = .binding who payload) :
            cast (congrArg (EventGraph.EventCode (graph setup).layout) kind)
              ((graph setup).nodes other) = .bind who payload := by
          cases located
          change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) kind)
            ((toEventGraph setup.program).nodes (embedding.event index)) = _
          simpa [index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
        exact transport event same outputEq
      have node : nodeView (graph setup) event = .bind who _ outputEq codeEq :=
        EventGraphRuntime.nodeView_eq_bind _ _
      obtain ⟨_, _, _, _, _, _, resources⟩ := sourceService_binding_decision_resources
        setup leaks bounds values capacity rosters opportunities network who control
          trace active event ready who _ outputEq codeEq node owned
      obtain ⟨room, selected, candidate, _, _, _, _⟩ := resources unsent
      have covered := sourceServiceOpportunity_commit_covered setup leaks bounds values rosters
        fresh guard next profile remainingProfile (inherited permitted who) refs source embedding
        refsBefore event.val aligned control.execution checkpoint.agrees checkpoint.history
        (control.execution.application.publicView.bindingCount who) selected candidate room
        (by simpa only [← same] using ready)
        (by simpa only [← same] using unsent) response (by simpa only [← same] using supported)
      exact ⟨covered.1, by simpa only [← same] using covered.2⟩
  | @reveal Γ names published owner name sourcePayload fresh binding unresolved next =>
      let index : Fin (eventCount (.reveal published owner name fresh binding unresolved next)) :=
        ⟨0, by simp [eventCount]⟩
      have same : embedding.event index = event := by
        apply Fin.ext
        simpa only [index, Nat.add_zero] using aligned.graphSuffix.rankEq index
      have actor := aligned.actorEq index
      rw [same] at actor
      change (graph setup).actor? event = some owner at actor
      cases Option.some.inj (owned.symm.trans actor)
      have rawTrace := menu.toRawTrace (initialLaw setup) horizon scheduler trace
      have boundedTrace := (sourceServiceMenu_in_raw setup leaks bounds rosters).trace
        (initialLaw setup) horizon scheduler trace
      let inputs : PMF (graph setup).Inputs := setup.initialLaw.map setup.eventInputs
      have initialEq : inputs.map
          (EventGraphRuntime.State.initial (graph := graph setup)) = initialLaw setup := by
        rw [PMF.map_comp]
        rfl
      have valid := (runtime setup).reactiveBindingInvariant_history leaks inputs horizon
        scheduler
        (by rw [initialEq]; exact rawTrace)
      have recalled := app.history_inputRecall (initialLaw setup) horizon scheduler rawTrace
      have bounded := bounds.executionHandles_raw_history (runtime setup) leaks inputs horizon
        scheduler (by rw [initialEq]; exact boundedTrace)
      have candidateValues := bounds.candidateValues_raw_history (runtime setup) leaks
        (initialLaw setup) horizon scheduler initialValues boundedTrace
      have covered := sourceServiceOpportunity_reveal_covered setup leaks bounds rosters fresh
        binding unresolved next profile remainingProfile refs source embedding refsBefore event.val
        aligned control.execution checkpoint valid recalled bounded.1 candidateValues
        (by simpa only [← same] using ready)
        (by simpa only [← same] using unsent) response (by simpa only [← same] using supported)
      exact ⟨covered.1, covered.2.trans (congrArg some same)⟩

theorem sourceServiceLastPolicy_admissible
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
    (who : Player) :
    (sourceServiceMenu setup leaks bounds rosters).Admissible (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) who
      (sourceServiceLastPolicy setup leaks rosters profile who) := by
  classical
  intro control trace active response supported
  let app := application setup leaks
  let past := control.execution.recall who
  let view := control.execution.observe app who
  have silent_covered (silenced : response ∈ (app.silentPolicy past view).support)
      (optional : ¬ decisionRequired setup leaks rosters who past view) :
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view := by
    change response ∈ sourceServiceActions setup leaks bounds rosters who past view
    rw [sourceServiceActions, ite_eq_right optional]
    exact bounds.silent_compiled (runtime setup) leaks who past view response silenced
  change response ∈ (sourceServiceLastPolicy setup leaks rosters profile who past view).support
    at supported
  cases serving : view.application.publicView.ownTurn? who with
  | none =>
      simp only [sourceServiceLastPolicy, serving] at supported
      exact silent_covered supported (by rintro ⟨event, same, _⟩; simp [serving] at same)
  | some event =>
      simp only [sourceServiceLastPolicy, serving] at supported
      split at supported
      · rename_i chosen
        exact (sourceServiceOpportunity_at_history setup leaks bounds values initialValues capacity
          rosters opportunities network profile permitted who control trace active event serving
          chosen.1 chosen.2.1 response (by
            change response ∈ (sourceServiceOpportunity setup leaks profile who event
              past view).support
            simpa only [sourceServiceOpportunity, chosen.2.1, Bool.false_eq_true, ↓reduceIte]
              using supported)).1
      · rename_i waiting
        apply silent_covered supported
        rintro ⟨other, otherTurn, owned, _, unsent, final⟩
        have same : other = event := Option.some.inj (otherTurn.symm.trans serving)
        subst other
        exact waiting ⟨owned, unsent, final⟩

omit [Fintype Player] in
/-- Private-intention normalization preserves the actual value-only source
interface. This is a consequence of source legality, not an extra condition on
the selected equilibrium or on successful paths. -/
theorem normalized_sourceService_admitted
    (setup : Setup (Player := Player) (L := L))
    (original : BehavioralProfile setup.program)
    (permitted : ∀ who, (original who).Admitted setup.program
      (CommitmentInterface.values setup.program)) (who : Player) :
    (normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context) original who).Admitted setup.program
        (CommitmentInterface.values setup.program) :=
  (original who).normalizeDisclosureFrom_admitted setup.program
    (CommitmentInterface.values setup.program) (permitted who) []
    (Revelations.initial setup.context) (fun view => PMF.pure view.2)

/-- The total finite compiler has the complete physical execution law of the
original source policy's disclosure normalization. Every retained sample,
message, private recall and public record is preserved jointly. -/
theorem sourceServiceCompiledProfile_complete_state
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (original : BehavioralProfile setup.program)
    (permitted : ∀ who, (original who).Admitted setup.program
      (CommitmentInterface.values setup.program)) :
    (((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).runBehavioral
      (sourceServiceCompiledProfile setup leaks bounds rosters network original)
      (2 * (rosterPlan setup rosters).length + 1)).map ExecutionProtocol.History.state =
      ((initialLaw setup).bind fun state =>
        (runtime setup).runInteractionPlan leaks
          (sourceServiceLastPolicy setup leaks rosters (normalizeDisclosureProfile setup.program []
            (Revelations.initial setup.context) original)) network (rosterPlan setup rosters)
          (ReactiveApplication.Execution.initial (application setup leaks) state)).map
        (fun final => some ⟨0, none, final⟩) := by
  exact roster_restrict_complete_state setup leaks rosters network
    (sourceServiceMenu setup leaks bounds rosters)
    (sourceServiceLastPolicy setup leaks rosters (normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context) original))
    (sourceServiceLastPolicy_admissible setup leaks bounds values initialValues capacity rosters
      opportunities network _ (normalized_sourceService_admitted setup original permitted))

end Vegas
