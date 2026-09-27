/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceLocalComparison
import Vegas.Game.SourceServiceAssessment

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

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

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

open Classical in
/-- An owner site whose native prescribed and alternative continuations are,
history by history, the prescribed source continuation and the continuation of
one admitted source alternative has native prescribed and alternative laws
equal to the prescribed and alternative laws of one mixture of original source
assessment comparisons. -/
theorem owner_comparisons_of_continuations (service : SourceServiceSpec Player L)
    (timing : ∀ event who, (graph service.setup).actor? event = some who →
      FinDist (Fin ((service.rosters event).count who)))
    (timingFull : ∀ event who owned, (timing event who owned).FullSupport)
    (source : (service.setup.informationModel
      (CommitmentInterface.values service.setup.program)).BehavioralAssessment)
    [∀ who (site : (service.setup.informationModel
      (CommitmentInterface.values service.setup.program)).InformationSite who),
      Fintype ((service.setup.informationModel
        (CommitmentInterface.values service.setup.program)).InformationHistory who site.1)]
    (full : ∀ who info, (source.strategy who info).FullSupport)
    (sourceBayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (service.setup.informationModel (CommitmentInterface.values service.setup.program)) source
      (service.setup.decision_antichain (CommitmentInterface.values service.setup.program)))
    (approx : TimedApproximant service)
    (built : approx = ofSource service timing timingFull source.strategy full)
    (who : Player) (site : service.model.InformationSite who)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view))
    {event : (graph service.setup).EventId}
    (owned : (graph service.setup).actor? event = some who)
    (granted : view.application.publicView.serviceGrant = some event)
    (law : FinDist (service.model.Choice who site.1))
    (alternative : BehavioralPolicy who service.setup.program)
    (admitted : alternative.Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (prescribedContinuation : ∀ history : service.model.InformationHistory who site.1,
      (service.model.runBehavioralFrom approx.assessment.strategy service.fuel history.1).map
        service.readout =
        (service.setup.continuationLaw approx.profile
          (decodedState service event history.1)).map some)
    (alternativeContinuation : ∀ history : service.model.InformationHistory who site.1,
      (service.model.runBehavioralFrom (Profile.update (sig := service.model.behavioralSignature)
        approx.assessment.strategy who ((approx.assessment.strategy who).withLaw site.1 law))
          service.fuel history.1).map service.readout =
        (service.setup.continuationLaw (Function.update approx.profile who alternative)
          (decodedState service event history.1)).map some) :
    ∃ mixture : FinDist ((service.setup.informationModel
        (CommitmentInterface.values service.setup.program)).AssessmentDeviation who),
      (service.model.assessmentComparison service.readout service.fuel approx.assessment who
        (site, (approx.assessment.strategy who).withLaw site.1 law)).prescribed =
        mixture.bind (fun deviation => ((service.setup.informationModel
          (CommitmentInterface.values service.setup.program)).assessmentComparison
            (fun final => service.setup.protocolReadout final.state)
            (instructionCount service.setup.program + 1) source who deviation).prescribed) ∧
      (service.model.assessmentComparison service.readout service.fuel approx.assessment who
        (site, (approx.assessment.strategy who).withLaw site.1 law)).alternative =
        mixture.bind (fun deviation => ((service.setup.informationModel
          (CommitmentInterface.values service.setup.program)).assessmentComparison
            (fun final => service.setup.protocolReadout final.state)
            (instructionCount service.setup.program + 1) source who deviation).alternative) := by
  subst built
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
  have grant : execution.application.serviceGrant = some event :=
    (congrArg (fun pair : List (application service.setup service.leaks).PlayerEntry ×
      (application service.setup service.leaks).PlayerView =>
        pair.2.application.publicView.serviceGrant) input).trans granted
  have same : phase.event = event := Option.some.inj (phase.granted.symm.trans grant)
  subst same
  have selected : (rosterPlan service.setup service.rosters)[phase.before.length]? =
      some (.player who) := by
    rw [phase.plan_split]
    simp
  have before : (rosterPlan service.setup service.rosters).take phase.before.length =
      rosterPlanPrefix service.setup service.rosters phase.event.val ++ [.grant phase.event] ++
        ((service.rosters phase.event).take phase.slot).map ServiceInstruction.player := by
    rw [phase.plan_split, List.append_assoc, List.take_append_of_le_length le_rfl,
      List.take_length]
    rfl
  obtain ⟨mixture, prescribedLaw, alternativeLaw⟩ := sourceService_owner_assessment_comparisons
    service.setup service.leaks service.bounds service.values service.initialValues
    service.capacity service.rosters service.opportunities.binding timing timingFull
    service.network source (fun player site => full player site.1) sourceBayes
    (ofSource service timing timingFull source.strategy full).assessment rfl
    (ofSource service timing timingFull source.strategy full).mixed
    (ofSource_bayes service timing timingFull source.strategy full) phase.event who owned
    ((service.rosters phase.event).take phase.slot) phase.before.length selected before site
    reference ⟨remaining, some who, execution⟩ current phase.position_before alternative admitted
  refine ⟨mixture, ?_, ?_⟩
  · rw [← prescribedLaw]
    simp only [InformationModel.assessmentComparison,
      InformationModel.BehavioralAssessment.continuationContext, Profile.update_eq_self,
      InformationModel.BehavioralAssessment.stateBelief, FinDist.map_bind, FinDist.bind_map]
    apply FinDist.bind_congr
    intro history _
    exact prescribedContinuation history
  · rw [← alternativeLaw]
    simp only [InformationModel.assessmentComparison,
      InformationModel.BehavioralAssessment.continuationContext,
      InformationModel.BehavioralAssessment.stateBelief, FinDist.map_bind, FinDist.bind_map]
    apply FinDist.bind_congr
    intro history _
    exact alternativeContinuation history

/-- Laws that are a common mixture of comparisons have, for every utility, the
mixture's average gain as their gain. This is the form the sequential
equilibrium limit theorem takes for a local comparison. -/
theorem mixture_gain_eq {Deviation Outcome : Type*} (mixture : FinDist Deviation)
    (prescribed alternative : FinDist Outcome)
    (sourcePrescribed sourceAlternative : Deviation → FinDist Outcome)
    (prescribedEq : prescribed = mixture.bind sourcePrescribed)
    (alternativeEq : alternative = mixture.bind sourceAlternative) (utility : Outcome → ℝ) :
    alternative.expect utility - prescribed.expect utility =
      mixture.expect (fun deviation =>
        (sourceAlternative deviation).expect utility -
          (sourcePrescribed deviation).expect utility) := by
  rw [prescribedEq, alternativeEq, FinDist.expect_bind, FinDist.expect_bind, FinDist.expect_sub]

end TimedApproximant

end Vegas.SourceProgram.RevealService
