/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceExecution
import Vegas.Game.SourceServiceCoverage
import Vegas.Game.SourceServiceDecisionSupport
import Vegas.Source.DisclosureContinuation
import Vegas.Game.RevealServiceRosterInitialized

/-! # Exact execution of the total full-source compiler

The finite policy is total at arbitrary inputs. Its equality with the physical
source policy is proved at every legal retained history from the actual
source-prefix support theorem and current runtime bounds.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem sourceServiceLastPolicy_admissible
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ∀ event owner payload,
      (graph setup).outputLayout event = .binding owner payload → owner ∈ rosters event)
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
  let menu := sourceServiceMenu setup leaks bounds rosters
  let horizon := (rosterPlan setup rosters).length
  let scheduler := rosterScheduler setup leaks rosters network
  obtain ⟨event, slot, initial, _selected, _initialSupport, Γ, names, remaining,
      remainingProfile, source, refs, embedding, refsBefore, aligned, inherited,
      granted, prior, sample, boundary, grant, _phase, _activated, _sampled, _config,
      publicEq, checkpoint, _position⟩ :=
    sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
      network profile who control trace active
  have grantedCurrent : control.execution.application.serviceGrant = some event :=
    (congrArg PublicView.serviceGrant publicEq).trans grant
  by_cases waiting : (graph setup).actor? event ≠ some who ∨
      (runtime setup).eventRecorded leaks (control.execution.recall who) event = true ∨
      (control.execution.recall who).length + 1 ≠
        rosterOffset setup rosters who event + (rosters event).count who
  · rw [sourceServiceLastPolicy_wait setup leaks rosters profile who _ _ event
      grantedCurrent waiting] at supported
    have optional : ¬ bindingRequired setup leaks rosters who (control.execution.recall who)
        (control.execution.observe app who) := by
      rintro ⟨other, payload, otherGrant, _binding, owned, _ready, unsent, last⟩
      have same : other = event := Option.some.inj (otherGrant.symm.trans grantedCurrent)
      subst other
      rcases waiting with foreign | recorded | earlier
      · exact foreign owned
      · simp only [recorded, Bool.true_eq_false] at unsent
      · exact earlier last
    change response ∈ sourceServiceActions setup leaks bounds rosters who
      (control.execution.recall who) (control.execution.observe app who)
    rw [sourceServiceActions, ite_eq_right optional]
    exact bounds.replay_compiled (runtime setup) leaks who _ _ response supported
  · push Not at waiting
    obtain ⟨owned, notSent, last⟩ := waiting
    have unsent : (runtime setup).eventRecorded leaks (control.execution.recall who) event =
        false := Bool.eq_false_iff.mpr notSent
    have ready : control.execution.application.config.cut.Ready event :=
      (ready_iff_rank setup _ event.val checkpoint.ordered event).mpr rfl
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
        have node : nodeView (graph setup) event = .bind who _ outputEq codeEq := by
          cases viewed : nodeView (graph setup) event with
          | sample payload law kind code => cases kind.symm.trans outputEq
          | resolve other payload binding checks kind code => cases kind.symm.trans outputEq
          | bind other payload kind code =>
              obtain ⟨rfl, rfl⟩ := EventGraph.EventField.binding.inj (kind.symm.trans outputEq)
              rfl
        obtain ⟨_, _, _, _, _, _, resources⟩ := sourceService_binding_decision_resources
          setup leaks bounds values capacity rosters opportunities network profile who control
            trace active event grantedCurrent who _ outputEq codeEq node owned
        obtain ⟨room, selected, candidate, _, _, _, _⟩ := resources unsent
        apply sourceServiceLastPolicy_commit_covered setup leaks bounds values rosters fresh guard
          next profile remainingProfile (inherited permitted who) refs source embedding refsBefore
          event.val aligned control.execution checkpoint.agrees checkpoint.history
          (control.execution.application.publicView.bindingCount who) selected candidate room
        · simpa only [← same] using grantedCurrent
        · simpa only [← same] using ready
        · simpa only [← same] using unsent
        · simpa only [← same] using last
        · exact supported
    | reveal published owner name fresh binding unresolved next =>
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
        let inputs : FinDist (graph setup).Inputs := setup.initialLaw.map setup.eventInputs
        have initialEq : inputs.map
            (EventGraphRuntime.State.initial (graph := graph setup)) = initialLaw setup := by
          rw [FinDist.map_comp]
          rfl
        have valid := (runtime setup).reactiveBindingInvariant_history leaks inputs horizon
          scheduler
          (by rw [initialEq]; exact rawTrace)
        have recalled := app.history_inputRecall (initialLaw setup) horizon scheduler rawTrace
        have bounded := bounds.executionHandles_raw_history (runtime setup) leaks inputs horizon
          scheduler (by rw [initialEq]; exact boundedTrace)
        have candidateValues := bounds.candidateValues_raw_history (runtime setup) leaks
          (initialLaw setup) horizon scheduler initialValues boundedTrace
        apply sourceServiceLastPolicy_reveal_covered setup leaks bounds rosters fresh binding
          unresolved next profile remainingProfile refs source embedding refsBefore event.val
          aligned
          control.execution checkpoint valid recalled bounded.1 candidateValues
        · simpa only [← same] using grantedCurrent
        · simpa only [← same] using ready
        · simpa only [← same] using unsent
        · simpa only [← same] using last
        · exact supported

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
    (Revelations.initial setup.context) (fun view => FinDist.pure view.2)

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
    (opportunities : ∀ event owner payload,
      (graph setup).outputLayout event = .binding owner payload → owner ∈ rosters event)
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

end Vegas.SourceProgram.RevealService
