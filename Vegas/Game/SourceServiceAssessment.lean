/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBayes
import Vegas.Game.DisclosureAssessment

/-! # Original assessment comparisons under actual native beliefs

The timed native owner's decoded Bayes belief is conditioned by its complete
physical input. Evaluating normalized source continuations under that belief
gives one common finite mixture of prescribed and deviating comparisons in the
original source assessment. Actual physical continuation laws can therefore
use this theorem without constructing an equilibrium of the normalized game.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Both normalized continuation laws use the same mixture of ORIGINAL
source assessment deviations. All native information-fiber likelihoods,
source observation support and the active source owner are derived here. -/
theorem sourceService_owner_assessment_comparisons
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (timing : TimingLaw setup rosters)
    (full : ∀ event who owned, (timing event who owned).FullSupport)
    (network : (runtime setup).NetworkPolicy leaks)
    (source : (setup.informationModel
      (CommitmentInterface.values setup.program)).BehavioralAssessment)
    [∀ who (site : (setup.informationModel
      (CommitmentInterface.values setup.program)).InformationSite who),
      Fintype ((setup.informationModel
        (CommitmentInterface.values setup.program)).InformationHistory who site.1)]
    (sourceMixed : source.IsFullyMixed)
    (sourceBayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (setup.informationModel (CommitmentInterface.values setup.program)) source
      (setup.decision_antichain (CommitmentInterface.values setup.program)))
    (native : ((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).BehavioralAssessment)
    (strategy : native.strategy = sourceServiceTimedProfile setup leaks bounds rosters network
      timing (setup.decodeBehavioralProfile (CommitmentInterface.values setup.program)
        source.strategy))
    (mixed : native.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      ((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network))
      native ((sourceServiceMenu setup leaks bounds rosters).decisionInformationAntichain
        (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)))
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner) (visits : List Player)
    (count : Nat)
    (selected : (rosterPlan setup rosters)[count]? = some (.player owner))
    (before : (rosterPlan setup rosters).take count =
      rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
        visits.map ServiceInstruction.player)
    (site : ((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).InformationSite owner)
    (history : ((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).InformationHistory owner site.1)
    (control : (application setup leaks).Control)
    (current : history.1.state = some control)
    (position : control.execution.environmentRecall.length = count + 1)
    (alternative : BehavioralPolicy owner setup.program)
    (admitted : alternative.Admitted setup.program (CommitmentInterface.values setup.program)) :
    let original := setup.decodeBehavioralProfile (CommitmentInterface.values setup.program)
      source.strategy
    let normalized := normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context) original
    let decodedBelief := (native.stateBelief owner site).map (fun state => state.bind
      fun current => sourceServicePrefix? setup event.val current.execution.application.config)
    let prefixLaw := (setup.initialLaw.map setup.initialConfig).bind fun config =>
      (fun distribution => distribution.bind
        (ProtocolState.behavioralStateStep setup.program normalized))^[event.val]
          (FinDist.pure (ProtocolState.entry setup.program config))
    (∃ view ∈ (prefixLaw.map (ProtocolState.observe owner setup.program)).support,
      SourceProgram.ProtocolView.actor owner setup.program view = some owner ∧
      decodedBelief =
        (prefixLaw.condOnFibre (ProtocolState.observe owner setup.program) view).map some) ∧
    ∃ mixture : FinDist ((setup.informationModel
        (CommitmentInterface.values setup.program)).AssessmentDeviation owner),
      ((decodedBelief.bind (setup.continuationLaw normalized)).map some) =
        mixture.bind (fun deviation => ((setup.informationModel
          (CommitmentInterface.values setup.program)).assessmentComparison
            (fun final => setup.protocolReadout final.state) (instructionCount setup.program + 1)
              source owner deviation).prescribed) ∧
      ((decodedBelief.bind
        (setup.continuationLaw (Function.update normalized owner alternative))).map some) =
        mixture.bind (fun deviation => ((setup.informationModel
          (CommitmentInterface.values setup.program)).assessmentComparison
            (fun final => setup.protocolReadout final.state) (instructionCount setup.program + 1)
              source owner deviation).alternative) := by
  intro original normalized decodedBelief prefixLaw
  let admission := CommitmentInterface.values setup.program
  have permitted (who : Player) : (original who).Admitted setup.program admission :=
    ((setup.behavioralPolicyEquiv admission who).symm (source.strategy who)).2
  have normalizedAdmitted := normalized_sourceService_admitted setup original permitted
  let encoded := fun who => setup.toProtocolBehavioralPolicy admission who
    (normalized who) (normalizedAdmitted who)
  let players := sourceServiceTimedPolicy setup leaks rosters timing normalized
  let executions := ((initialLaw setup).bind fun state =>
    (runtime setup).runInteractionPlan leaks players network
      (rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
        visits.map ServiceInstruction.player)
      (ReactiveApplication.Execution.initial (application setup leaks) state)).bind
    fun prior => prior.environmentStep (application setup leaks) (.activate owner)
  obtain ⟨supported, projected⟩ := sourceService_owner_bayes_at_history setup leaks bounds values
    initialValues capacity rosters opportunities timing full network original permitted native
      strategy mixed bayes event owner owned visits count selected before site history control
        current position
  have referenceSupport : control.execution ∈ executions.support := by
    simpa only [executions, before, players] using supported
  have covered := sourceServiceTimedPolicy_admissible setup leaks bounds values initialValues
    capacity rosters opportunities network timing full normalized normalizedAdmitted
  obtain ⟨state, checkpoint⟩ := sourceService_owner_checkpoint setup leaks bounds values capacity
    rosters opportunities network players covered event owner visits control.execution
      referenceSupport
  have decoded : sourceServicePrefix? setup event.val control.execution.application.config =
      some state := SourcePrefixCheckpoint.decode setup.program _ _ _ _ 0 event.val state _
        checkpoint
  have active := SourcePrefixCheckpoint.actor owner setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) []
    (Revelations.initial setup.context) (outputRef setup.program) 0 event.val state
      control.execution.application.config checkpoint event.isLt
  rw [eventOwner?_eq_actor] at active
  change ProtocolView.actor owner setup.program (ProtocolState.observe owner setup.program state) =
    (graph setup).actor? event at active
  rw [owned] at active
  have prefixEq : (((setup.informationModel admission).runBehavioral encoded
      (event.val + 1)).map History.state) = prefixLaw.map some := by
    rw [setup.encoded_prefix_state]
    simp only [prefixLaw, FinDist.bind_map, FinDist.map_bind]
  obtain ⟨channel, factor⟩ := sourceService_owner_information_law setup leaks bounds values
    initialValues capacity rosters opportunities timing full network original permitted
      event owner owned visits
  have marginal := congrArg (FinDist.map Prod.fst) factor
  simp only [FinDist.map_comp, FinDist.map_bind, Function.comp_def,
    FinDist.map_const, FinDist.bind_pure] at marginal
  have executionMarginal : executions.map (fun execution =>
      sourceServicePrefix? setup event.val execution.application.config) =
        (((setup.informationModel admission).runBehavioral encoded (event.val + 1)).map
          History.state) := by
    simpa only [executions, FinDist.map_bind] using marginal
  have sourceSupport : some state ∈ (prefixLaw.map some).support := by
    rw [← prefixEq, ← executionMarginal, FinDist.support_map]
    exact ⟨control.execution, referenceSupport, decoded⟩
  obtain ⟨actual, actualSupport, same⟩ := FinDist.support_map .. ▸ sourceSupport
  have stateSupport : state ∈ prefixLaw.support := (Option.some.inj same) ▸ actualSupport
  let view := ProtocolState.observe owner setup.program state
  have viewSupport : view ∈ (prefixLaw.map (ProtocolState.observe owner setup.program)).support :=
    FinDist.support_map .. ▸ ⟨state, stateSupport, rfl⟩
  have imagePresent : some view ∈
      (prefixLaw.map (setup.protocolObserve owner ∘ some)).support := by
    rw [FinDist.support_map]
    exact ⟨state, stateSupport, rfl⟩
  have transported := FinDist.map_conditional_readout prefixLaw some
    (setup.protocolObserve owner) (some view) imagePresent
  have fiber : prefixLaw.condOnFibre (setup.protocolObserve owner ∘ some) (some view) =
      prefixLaw.condOnFibre (ProtocolState.observe owner setup.program) view := by
    apply FinDist.condOnFibre_eq_of_support_fiber
    intro value _
    simp only [Function.comp_apply, Setup.protocolObserve, Option.map_some, Option.some.injEq]
  rw [fiber] at transported
  have belief : decodedBelief =
      (prefixLaw.condOnFibre (ProtocolState.observe owner setup.program) view).map some := by
    change decodedBelief = _ at projected
    rw [prefixEq, decoded] at projected
    exact projected.trans transported.symm
  obtain ⟨mixture, prescribed, deviating⟩ :=
    setup.normalized_disclosure_assessment_comparison admission source sourceMixed sourceBayes
      event.val owner alternative admitted view viewSupport active
  refine ⟨⟨view, viewSupport, active, belief⟩, mixture, ?_, ?_⟩
  · rw [belief, FinDist.bind_map]
    exact prescribed
  · rw [belief, FinDist.bind_map]
    exact deviating

end Vegas
