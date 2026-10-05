/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceContinuationBridge
import Vegas.Game.SourceServiceAssessment
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheoryExtensions.Math.Probability.Support

/-! # Owner sites as mixtures of original source deviations

At an owner's information site of a timed approximant built from a source
assessment, suppose every history of the site continues, under the prescribed
native strategy, as the prescribed source continuation from its decoded state,
and, under a local native lottery, as the continuation of one admitted source
alternative. The alternative is fixed for the whole site before any hidden
history is chosen. Then the native prescribed and alternative laws are the
prescribed and alternative laws of one common finite mixture of original
source assessment comparisons. The mixture weights are the native Bayes belief
decoded to source states; the original source assessment supplies the
comparisons.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace TimedApproximant

/-- The source prefix state decoded from a native history at the start of an
event's phase. -/
def decodedState (service : SourceServiceSpec Player L) (event : (graph service.setup).EventId)
    (history : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).History) : Option (ProtocolState service.setup.program) :=
  history.state.bind fun current =>
    sourceServicePrefix? service.setup event.val current.execution.application.config

/-- The roster position of an owner site: a reference history of the site,
its activation's plan index, and the owner's earlier visits in the event's
roster. -/
private theorem owner_site_position (service : SourceServiceSpec Player L) (who : Player)
    (site : service.model.InformationSite who)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view)) {event : (graph service.setup).EventId}
    (readyView : view.application.publicView.EventReady event) :
    ∃ (reference : service.model.InformationHistory who site.1)
      (control : (application service.setup service.leaks).Control)
      (_ : reference.1.state = some control) (visits : List Player) (count : Nat),
      (rosterPlan service.setup service.rosters)[count]? = some (.player who) ∧
      (rosterPlan service.setup service.rosters).take count =
        rosterPlanPrefix service.setup service.rosters event.val ++
          visits.map ServiceInstruction.player ∧
      control.execution.environmentRecall.length = count + 1 := by
  obtain ⟨reference, _, _⟩ := site.2
  have active := InformationModel.InformationSite.active service.model site reference
  obtain ⟨control, current⟩ : ∃ control, reference.1.state = some control := by
    cases state : reference.1.state with
    | none => rw [state] at active; cases active
    | some control => exact ⟨control, rfl⟩
  have actor : control.actor = some who := by rw [current] at active; exact active
  obtain ⟨remaining, actorValue, execution⟩ := control
  change actorValue = some who at actor
  subst actorValue
  have trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    current ▸ reference.1.trace
  obtain ⟨phase⟩ := service.exists_decisionPhase who remaining execution trace
  have input := Option.some.inj
    ((service.infoOf_decision reference.1 current).symm.trans (reference.2.trans observed))
  have readyNow :=
    (congrArg (fun pair : List (application service.setup service.leaks).PlayerEntry ×
      (application service.setup service.leaks).PlayerView =>
        pair.2.application.publicView.EventReady event) input).mpr readyView
  have same : phase.event = event := (phase.sole.2 event readyNow).symm
  subst same
  have selected : (rosterPlan service.setup service.rosters)[phase.before.length]? =
      some (.player who) := by
    rw [phase.plan_split]
    simp
  have before : (rosterPlan service.setup service.rosters).take phase.before.length =
      rosterPlanPrefix service.setup service.rosters phase.event.val ++
        ((service.rosters phase.event).take phase.slot).map ServiceInstruction.player := by
    rw [phase.plan_split, List.append_assoc, List.take_append_of_le_length le_rfl,
      List.take_length]
    rfl
  exact ⟨reference, ⟨remaining, some who, execution⟩, current, _, _, selected, before,
    phase.position_before⟩

/-- At an owner site of the `ofSource` approximant, the source continuations
from the decoded states of the site's histories, averaged under the native
belief, are the prescribed laws of one mixture of original source assessment
comparisons; after replacing the owner's policy by any admitted alternative,
they are the mixture's alternative laws. -/
theorem owner_source_comparisons (service : SourceServiceSpec Player L)
    (timing : TimingLaw service.setup service.rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (source : service.sourceModel.BehavioralAssessment)
    (full : ∀ who info, FullSupport (source.strategy who info))
    (sourceBayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      service.sourceModel source
      (service.setup.decision_antichain (CommitmentInterface.values service.setup.program)))
    (approx : TimedApproximant service)
    (built : approx = ofSource service timing timingFull source.strategy full)
    (who : Player) (site : service.model.InformationSite who)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view))
    {event : (graph service.setup).EventId}
    (owned : (graph service.setup).actor? event = some who)
    (readyView : view.application.publicView.EventReady event)
    (alternative : BehavioralPolicy who service.setup.program)
    (admitted : alternative.Admitted service.setup.program
      (CommitmentInterface.values service.setup.program)) :
    ∃ mixture : PMF (service.sourceModel.AssessmentDeviation who),
      ((approx.assessment.belief who site).bind fun history =>
        (service.setup.continuationLaw approx.profile
          (decodedState service event history.1)).map some) =
        mixture.bind (fun deviation => (service.sourceModel.assessmentComparisonWith
            (service.sourceModel.truncatedRunner (instructionCount service.setup.program + 1))
            (fun final => service.setup.protocolReadout final.state) source who
            deviation).prescribed) ∧
      ((approx.assessment.belief who site).bind fun history =>
        (service.setup.continuationLaw (Function.update approx.profile who alternative)
          (decodedState service event history.1)).map some) =
        mixture.bind (fun deviation => (service.sourceModel.assessmentComparisonWith
            (service.sourceModel.truncatedRunner (instructionCount service.setup.program + 1))
            (fun final => service.setup.protocolReadout final.state) source who
            deviation).alternative) := by
  subst built
  obtain ⟨reference, control, current, visits, count, selected, before, position⟩ :=
    owner_site_position service who site past view observed readyView
  obtain ⟨_, mixture, prescribedLaw, alternativeLaw⟩ := sourceService_owner_assessment_comparisons
    service.setup service.leaks service.bounds service.values service.initialValues
    service.capacity service.rosters service.opportunities timing timingFull
    service.network source (fun player site => full player site.1) sourceBayes
    (ofSource service timing timingFull source.strategy full).assessment rfl
    (ofSource service timing timingFull source.strategy full).mixed
    (ofSource_bayes service timing timingFull source.strategy full) event who owned
    visits count selected before site reference control current position alternative admitted
  refine ⟨mixture, ?_, ?_⟩
  · rw [← prescribedLaw]
    simp only [InformationModel.BehavioralAssessment.stateBelief, PMF.map_bind,
      PMF.bind_map]
    rfl
  · rw [← alternativeLaw]
    simp only [InformationModel.BehavioralAssessment.stateBelief, PMF.map_bind,
      PMF.bind_map]
    rfl

open Classical in
/-- An owner site whose native prescribed and alternative continuations are,
history by history, the prescribed source continuation and the continuation of
one admitted source alternative has native prescribed and alternative laws
equal to the prescribed and alternative laws of one mixture of original source
assessment comparisons. -/
theorem owner_comparisons_of_continuations (service : SourceServiceSpec Player L)
    (timing : TimingLaw service.setup service.rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (source : service.sourceModel.BehavioralAssessment)
    (full : ∀ who info, FullSupport (source.strategy who info))
    (sourceBayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      service.sourceModel source
      (service.setup.decision_antichain (CommitmentInterface.values service.setup.program)))
    (approx : TimedApproximant service)
    (built : approx = ofSource service timing timingFull source.strategy full)
    (who : Player) (site : service.model.InformationSite who)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view))
    {event : (graph service.setup).EventId}
    (owned : (graph service.setup).actor? event = some who)
    (readyView : view.application.publicView.EventReady event)
    (law : PMF (service.model.Choice who site.1))
    (alternative : BehavioralPolicy who service.setup.program)
    (admitted : alternative.Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (prescribedContinuation : ∀ history ∈ (approx.assessment.belief who site).support,
      (service.model.runBehavioralFrom approx.assessment.strategy service.fuel history.1).map
        service.readout =
        (service.setup.continuationLaw approx.profile
          (decodedState service event history.1)).map some)
    (alternativeContinuation : ∀ history ∈ (approx.assessment.belief who site).support,
      (service.model.runBehavioralFrom (Profile.update (sig := service.model.behavioralSignature)
        approx.assessment.strategy who ((approx.assessment.strategy who).withLaw site.1 law))
          service.fuel history.1).map service.readout =
        (service.setup.continuationLaw (Function.update approx.profile who alternative)
          (decodedState service event history.1)).map some) :
    ∃ mixture : PMF (service.sourceModel.AssessmentDeviation who),
      (service.model.assessmentComparisonWith (service.model.truncatedRunner service.fuel)
          service.readout approx.assessment who
        (site, (approx.assessment.strategy who).withLaw site.1 law)).prescribed =
        mixture.bind (fun deviation => (service.sourceModel.assessmentComparisonWith
            (service.sourceModel.truncatedRunner (instructionCount service.setup.program + 1))
            (fun final => service.setup.protocolReadout final.state) source who
            deviation).prescribed) ∧
      (service.model.assessmentComparisonWith (service.model.truncatedRunner service.fuel)
          service.readout approx.assessment who
        (site, (approx.assessment.strategy who).withLaw site.1 law)).alternative =
        mixture.bind (fun deviation => (service.sourceModel.assessmentComparisonWith
            (service.sourceModel.truncatedRunner (instructionCount service.setup.program + 1))
            (fun final => service.setup.protocolReadout final.state) source who
            deviation).alternative) := by
  obtain ⟨mixture, prescribedLaw, alternativeLaw⟩ := owner_source_comparisons service timing
    timingFull source full sourceBayes approx built who site past view observed owned readyView
    alternative admitted
  refine ⟨mixture, ?_, ?_⟩
  · rw [← prescribedLaw]
    simp only [InformationModel.assessmentComparisonWith, InformationModel.assessmentLawWith,
      Profile.update_eq_self, PMF.map_bind]
    apply bind_congr_on_support _
    intro history member
    exact prescribedContinuation history member
  · rw [← alternativeLaw]
    simp only [InformationModel.assessmentComparisonWith, InformationModel.assessmentLawWith,
      PMF.map_bind]
    apply bind_congr_on_support _
    intro history member
    exact alternativeContinuation history member

/-- Every history in the Bayes belief of an owner site of the `ofSource`
approximant decodes to a state that an actual source history reaches, and all
these source histories give the owner one common information state. -/
theorem owner_site_source_histories (service : SourceServiceSpec Player L)
    (timing : TimingLaw service.setup service.rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (source : service.sourceModel.BehavioralAssessment)
    (full : ∀ who info, FullSupport (source.strategy who info))
    (sourceBayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      service.sourceModel source
      (service.setup.decision_antichain (CommitmentInterface.values service.setup.program)))
    (approx : TimedApproximant service)
    (built : approx = ofSource service timing timingFull source.strategy full)
    (who : Player) (site : service.model.InformationSite who)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view))
    {event : (graph service.setup).EventId}
    (owned : (graph service.setup).actor? event = some who)
    (readyView : view.application.publicView.EventReady event) :
    ∃ sourceView : SourceProgram.ProtocolView who service.setup.program,
      ∀ history ∈ (approx.assessment.belief who site).support,
        ∃ sourceHistory : (service.setup.executionProtocol
            (CommitmentInterface.values service.setup.program)).History,
          sourceHistory.state = decodedState service event history.1 ∧
          ¬ (service.setup.executionProtocol
            (CommitmentInterface.values service.setup.program)).terminal sourceHistory.state ∧
          (service.setup.executionProtocol
            (CommitmentInterface.values service.setup.program)).active sourceHistory.state who ∧
          service.sourceModel.infoOf who
              sourceHistory.trace = some sourceView := by
  subst built
  obtain ⟨reference, control, current, visits, count, selected, before, position⟩ :=
    owner_site_position service who site past view observed readyView
  let admission := CommitmentInterface.values service.setup.program
  let original := service.setup.decodeBehavioralProfile admission source.strategy
  have permitted (player : Player) : (original player).Admitted service.setup.program admission :=
    ((service.setup.behavioralPolicyEquiv admission player).symm (source.strategy player)).2
  have normalizedAdmitted := normalized_sourceService_admitted service.setup original permitted
  obtain ⟨⟨sourceView, viewSupport, active, belief⟩, _⟩ :=
    sourceService_owner_assessment_comparisons service.setup service.leaks service.bounds
      service.values service.initialValues service.capacity service.rosters
      service.opportunities timing timingFull service.network source
      (fun player site => full player site.1) sourceBayes
      (ofSource service timing timingFull source.strategy full).assessment rfl
      (ofSource service timing timingFull source.strategy full).mixed
      (ofSource_bayes service timing timingFull source.strategy full) event who owned
      visits count selected before site reference control current position
      _ (normalizedAdmitted who)
  refine ⟨sourceView, fun history member => ?_⟩
  have decodedMember : decodedState service event history.1 ∈
      (((ofSource service timing timingFull source.strategy full).assessment.stateBelief who
        site).map (fun state => state.bind fun current => sourceServicePrefix? service.setup
          event.val current.execution.application.config)).support := by
    rw [PMF.support_map]
    exact ⟨history.1.state, PMF.support_map .. ▸ ⟨history, member, rfl⟩, rfl⟩
  rw [belief, PMF.support_map] at decodedMember
  obtain ⟨state, conditioned, stateEq⟩ := decodedMember
  obtain ⟨_, _, _⟩ := PMF.support_map .. ▸ viewSupport
  obtain ⟨matched, supported⟩ := mem_support_fiberPosterior
    (mem_support_map_of_exists_mem_fiber (by
    obtain ⟨witness, witnessSupport, witnessView⟩ := PMF.support_map .. ▸ viewSupport
    exact ⟨witness, witnessView, witnessSupport⟩)) conditioned
  let encoded := fun player => service.setup.toProtocolBehavioralPolicy admission player
    (normalizeDisclosureProfile service.setup.program [] (Revelations.initial service.setup.context)
      original player) (normalizedAdmitted player)
  have law := service.setup.encoded_prefix_state admission
    (normalizeDisclosureProfile service.setup.program [] (Revelations.initial service.setup.context)
      original) normalizedAdmitted event.val
  have reached : some state ∈ (((service.setup.informationModel admission).runBehavioral encoded
      (event.val + 1)).map History.state).support := by
    rw [law, PMF.support_bind]
    rw [PMF.support_bind] at supported
    obtain ⟨config, configSupport, supported⟩ := Set.mem_iUnion₂.mp supported
    obtain ⟨initial, initialSupport, rfl⟩ := PMF.support_map .. ▸ configSupport
    exact Set.mem_iUnion₂.mpr ⟨initial, initialSupport, PMF.support_map .. ▸
      ⟨state, supported, rfl⟩⟩
  obtain ⟨sourceHistory, _, sourceState⟩ := PMF.support_map .. ▸ reached
  refine ⟨sourceHistory, sourceState.trans stateEq, ?_, ?_, ?_⟩
  · rw [sourceState]
    intro stopped
    have absent := ProtocolState.terminal_actor_none who service.setup.program state stopped
    rw [matched, active] at absent
    cases absent
  · change (service.setup.protocolObserve who sourceHistory.state).elim False _
    simpa only [sourceState, Setup.protocolObserve, Option.map_some, Option.elim_some, matched]
      using active
  · rw [show (service.setup.informationModel admission).infoOf who sourceHistory.trace =
      service.setup.protocolObserve who sourceHistory.state from
        service.setup.protocol_info admission who sourceHistory.trace]
    simp only [sourceState, Setup.protocolObserve, Option.map_some, matched]

end TimedApproximant

end Vegas
