/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalCommonPerturbations
import Vegas.Game.ProposalRecoveryEquilibriumConstruction
import GameTheoryExtensions.Analysis.Protocol.Bayes
import Interaction.ReactiveTerminalEvaluation

/-! # One source construction and its actual native Bayes sequence -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  {tapeLength : Nat} (prior : PMF (ReservedEpoch.Tape Player tapeLength))

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => setup.initialLaw.map (fun theta =>
  PhaseRuntimeState.initial plan (encodeInputs theta))
local notation "horizon" => ReservedEpoch.executionHorizon runtime
local notation "scheduler" => ReactiveApplication.SchedulerImplementation.scheduler
  (ReservedEpoch.implementation runtime leaks (ReservedEpoch.packetCapacity runtime) prior)
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "sourceHorizon" =>
  ((Fintype.card Player + 1) * (instructionCount setup.program + 1))

open Classical in
/-- The original pooled source construction supplies one strict index for its
source limit and for the concrete native Bayes assessments, posterior bounds,
and initialized joint-law errors. No native optimality is asserted here. -/
theorem exists_phaseProposal_consistent_sequence
    [setup.FiniteInitialLaw] [Fintype setup.proposalRecoveryProtocol.History]
    [(app).FiniteNature initial scheduler]
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (activationGap processingGap : Nat)
    (gaps : ∀ tape ∈ prior.support,
      tape.BoundedGaps (ReservedEpoch.completionCycles runtime) activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : horizon ≤ bounds.candidateCount)
    (honest : ℕ → setup.intendedModel.BehavioralAssessment)
    (honestLimit : setup.intendedModel.BehavioralAssessment)
    (honestMixed : ∀ n, (honest n).IsFullyMixed)
    (honestBayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      setup.intendedModel (honest n) setup.intended_decision_antichain)
    (honestConverges : InformationModel.BehavioralAssessmentConvergesPointwise honest honestLimit)
    (reach : ℕ → ℝ) (reachPositive : ∀ n, 0 < reach n)
    (reachBound : ∀ n who (site : setup.intendedModel.InformationSite who), reach n ≤
      (setup.intendedModel.informationMass (honest n).strategy who site).toReal)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (equilibrium : honestLimit.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who history => (setup.protocolReadout history.state).elim 0
        (fun terminal => utility terminal who))) :
    ∃ (scale sourceBad nativeBad : ℕ → Set.Icc (0 : ℝ) 1)
      (weights : ℕ → (pool : setup.ProposalRecoveryValuePool) →
        PMF (setup.ProposalRecoveryPoolPart pool))
      (source : ℕ → setup.proposalRecoveryModel.BehavioralAssessment)
      (limit : setup.proposalRecoveryModel.BehavioralAssessment)
      (native : ℕ → (N).BehavioralAssessment) (index : ℕ → ℕ),
      let rates := fun n => (⟨nativeBad n, scale n, scale n, scale n⟩ : PhaseProposalRates)
      let pins := fun n => setup.proposalRecoveryHonestPoolPins wellFormed (honest n).strategy
      let domain := fun n => setup.proposalRecoveryPooledDomainLaw finite
        (scale n).val (scale n).property.1 (scale n).property.2 (pins n) (weights n)
      let profile := fun n => setup.proposalRecoveryNormalizedTrembledProfile
        (scale n).val (scale n).property.1 (scale n).property.2
        (sourceBad n).val (sourceBad n).property.1 (sourceBad n).property.2
        (scale n).val (scale n).property.1 (scale n).property.2 (domain n)
      let error := fun n =>
        (((Fintype.card Player * (2 * horizon + 1) : Nat) : ℝ) * (rates n).flagBound +
          ((Fintype.card Player *
            ((Fintype.card Player + 1) * (instructionCount setup.program + 1)) : Nat) : ℝ) *
              ((scale n).val + (sourceBad n).val + (scale n).val))
      StrictMono index ∧
      (∀ n, 0 < (scale n).val ∧ (scale n).val ≤ relativeTremble reach n ∧
        (scale n).val ≤ 1 / 4 ∧
        0 < (sourceBad n).val ∧ (sourceBad n).val ≤ (scale n).val ∧
        0 < (nativeBad n).val ∧ (nativeBad n).val ≤ (scale n).val) ∧
      Tendsto (fun n => (scale (index n)).val) atTop (nhds 0) ∧
      Tendsto (fun n => (sourceBad (index n)).val) atTop (nhds 0) ∧
      Tendsto (fun n => (nativeBad (index n)).val) atTop (nhds 0) ∧
      Tendsto (fun n => error (index n)) atTop (nhds 0) ∧
      (∀ n, (source n).IsFullyMixed) ∧
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
        setup.proposalRecoveryModel (source n) setup.proposalRecoveryModel_decisionAntichain) ∧
      InformationModel.BehavioralAssessmentConvergesPointwise
        (fun n => source (index n)) limit ∧
      (∀ n who (history : setup.proposalRecoveryProtocol.History)
          (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
        (source n).strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
          profile n who (setup.proposalRecoveryModel.infoOf who history.trace)) ∧
      (∀ n alternative pool,
        ∑ agent ∈ Finset.univ.filter
            (fun agent => setup.proposalRecoveryAgentPool agent = pool),
          setup.proposalRecoveryComponentGain finite (source n)
            (scale n).val (scale n).property.1 (scale n).property.2
            (sourceBad n).val (sourceBad n).property.1 (sourceBad n).property.2
            (scale n).val (scale n).property.1 (scale n).property.2
            (scale n).val (scale n).property.1 (scale n).property.2
            (pins n) alternative utility excludedPayoff agent ≤ 0) ∧
      limit.IsSequentialEquilibrium setup.proposalRecoveryModel_decisionAntichain
        setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
        (setup.proposalRecoveryPayoff utility excludedPayoff) ∧
      (setup.proposalRecoveryRestriction wellFormed).ExtendsProfile
        honestLimit.strategy limit.strategy ∧
      (∀ fuel, (setup.intendedModel.runBehavioral honestLimit.strategy fuel).map
          (setup.proposalRecoveryIntendedLift wellFormed) =
        setup.proposalRecoveryModel.runBehavioral limit.strategy fuel) ∧
      (∀ n, (native n).strategy = phaseProposalReferenceStrategy setup mode runtime leaks bounds
        plan initial horizon scheduler (domain n) (rates n)) ∧
      (∀ n, (native n).IsFullyMixed) ∧
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent (N) (native n)
        ((menu).decisionInformationAntichain initial horizon scheduler)) ∧
      (∀ n observer (site : setup.proposalRecoveryModel.InformationSite observer),
        0 < setup.proposalRecoveryModel.informationMass
          (source (index n)).strategy observer site →
          (∑ history : setup.proposalRecoveryModel.InformationHistory observer site.1 with
            (∃ owner : Player, observer ≠ owner ∧
              setup.GeneratedPreparationHistory owner history.val),
            ((source (index n)).belief observer site history).toReal) ≤
              (scale (index n)).val) ∧
      (∀ n observer (site : (N).InformationSite observer),
        0 < (N).informationMass (native (index n)).strategy observer site →
          (∑ history : (N).InformationHistory observer site.1 with
            (∃ owner : Player, observer ≠ owner ∧
              PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds initial horizon
                scheduler owner history.val),
            ((native (index n)).belief observer site history).toReal) ≤
              (scale (index n)).val) ∧
      ∀ n,
        let nativeReadout := fun state : (app).ProtocolState =>
          ((phaseSourceReadout setup mode runtime leaks state).map (initialState setup.program),
            state.map (fun current => current.execution.application.current.excluded),
            phaseSourceReadout setup mode runtime leaks state,
            fun who => phaseExclusionBase setup mode runtime leaks utility excludedPayoff state who)
        let sourceReadout := fun history : setup.proposalRecoveryProtocol.History =>
          ((setup.protocolReadout (setup.commitRecoverySourceState history.state)).map
              (initialState setup.program),
            history.state.map CommitRecoveryState.excluded,
            setup.protocolReadout (setup.commitRecoverySourceState history.state),
            fun who => setup.commitRecoveryPayoff utility excludedPayoff who
              ⟨history.state, setup.proposalRecoveryEraseTrace history.trace⟩)
        PMF.WithinTV (error (index n))
          (((N).runBehavioral (native (index n)).strategy (2 * horizon + 1)).map
            (fun history : (E).History => nativeReadout history.state))
          ((setup.proposalRecoveryModel.runBehavioral (source (index n)).strategy
            sourceHorizon).map sourceReadout) := by
  classical
  obtain ⟨scale, sourceBad, nativeBad, positive, scaleLimit, sourceBadLimit, nativeBadLimit,
    posterior⟩ := exists_phaseProposal_common_perturbations setup mode runtime leaks bounds plan
      prior complete covered maximal finite wellFormed.initialValues activationGap processingGap
        gaps margin capacity reach reachPositive utility excludedPayoff
  have scalePositive (n : Nat) : 0 < (scale n).val := (positive n).1
  have scaleSmall (n : Nat) : (scale n).val < 1 :=
    (positive n).2.2.1.trans_lt (by norm_num)
  have badPositive (n : Nat) : 0 < (sourceBad n).val := (positive n).2.2.2.1
  have badSmall (n : Nat) : (sourceBad n).val < 1 :=
    (positive n).2.2.2.2.1.trans_lt (scaleSmall n)
  have sourceBadRate (n : Nat) : (sourceBad n).val ≤ relativeTremble reach n :=
    (positive n).2.2.2.2.1.trans (positive n).2.1
  obtain ⟨weights, source, limit, index, mixed, bayes, increasing, converges, prescribed, gains,
      rational, extension, initialized, _readout⟩ :=
    setup.exists_proposalRecovery_sequentialEquilibrium_construction finite wellFormed honest
      honestLimit honestMixed honestBayes honestConverges reach reachPositive reachBound
      (fun n => (scale n).val) (fun n => (sourceBad n).val)
      (fun n => (scale n).val) (fun n => (scale n).val)
      scalePositive scaleSmall badPositive badSmall scalePositive scaleSmall
      scalePositive scaleSmall (fun n => (positive n).2.1) sourceBadRate
      (fun n => (positive n).2.1) (fun n => (positive n).2.1)
      utility excludedPayoff below equilibrium
  let rates : ℕ → PhaseProposalRates := fun n =>
    ⟨nativeBad n, scale n, scale n, scale n⟩
  let pins := fun n => setup.proposalRecoveryHonestPoolPins wellFormed (honest n).strategy
  let domain := fun n => setup.proposalRecoveryPooledDomainLaw finite
    (scale n).val (scale n).property.1 (scale n).property.2 (pins n) (weights n)
  let profile := fun n => setup.proposalRecoveryNormalizedTrembledProfile
    (scale n).val (scale n).property.1 (scale n).property.2
    (sourceBad n).val (sourceBad n).property.1 (sourceBad n).property.2
    (scale n).val (scale n).property.1 (scale n).property.2 (domain n)
  let strategy := fun n => phaseProposalReferenceStrategy setup mode runtime leaks bounds plan
    initial horizon scheduler (domain n) (rates n)
  have full (n : Nat) : ∀ who (site : (N).InformationSite who)
      (choice : (N).Choice who site.1), choice ∈ (strategy n who site.1).support :=
    phaseProposalReferenceStrategy_fullSupport setup mode runtime leaks bounds plan
      initial horizon scheduler (domain n) (rates n) (scalePositive n)
  let native : ℕ → (N).BehavioralAssessment := fun n =>
    (N).bayesAssessment (strategy n) (full n)
      ((menu).decisionInformationAntichain initial horizon scheduler)
  have nativeStrategy (n : Nat) : (native n).strategy = strategy n := rfl
  have nativeMixed (n : Nat) : (native n).IsFullyMixed :=
    (N).bayesAssessment_isFullyMixed (strategy n) (full n)
      ((menu).decisionInformationAntichain initial horizon scheduler)
  have nativeBayes (n : Nat) : InformationModel.BehavioralAssessment.IsBayesConsistent
      (N) (native n) ((menu).decisionInformationAntichain initial horizon scheduler) :=
    (N).bayesAssessment_isBayesConsistent (strategy n) (full n)
      ((menu).decisionInformationAntichain initial horizon scheduler)
  have nativeRun (n : Nat) :
      (((N).runBehavioral (native n).strategy (2 * horizon + 1)).map History.state) =
        (app).finish initial horizon scheduler
          (phaseProposalReferencePolicy setup mode runtime leaks bounds plan
            (domain n) (rates n)) none := by
    rw [nativeStrategy n]
    let players := phaseProposalReferencePolicy setup mode runtime leaks bounds plan
      (domain n) (rates n)
    have admissible : ∀ who, (menu).Admissible initial horizon scheduler who (players who) := by
      intro who control _trace _active response supported
      exact phaseProposalReferencePolicy_covered setup mode runtime leaks bounds plan
        (domain n) (rates n) who (control.execution.recall who)
          (control.execution.observe (app) who) response supported
    exact (menu).run_restrict_eq_finish initial horizon scheduler players admissible
      (2 * horizon + 1) (E).initHistory (by rfl)
  have initialEq : PMF.map (PhaseRuntimeState.initial plan)
      (PMF.map encodeInputs setup.initialLaw) = initial := by
    rw [PMF.map_comp]
    rfl
  let error := fun n =>
    (((Fintype.card Player * (2 * horizon + 1) : Nat) : ℝ) * (rates n).flagBound +
      ((Fintype.card Player *
        ((Fintype.card Player + 1) * (instructionCount setup.program + 1)) : Nat) : ℝ) *
          ((scale n).val + (sourceBad n).val + (scale n).val))
  have errorLimit : Tendsto error atTop (nhds 0) := posterior.2.2.1
  have sourceTerminal (n : Nat) :
      setup.proposalRecoveryModel.runBehavioralTerminalFrom
          setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
            (source n).strategy setup.proposalRecoveryProtocol.initHistory =
        setup.proposalRecoveryModel.runBehavioralTerminalFrom
          setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
            (profile n) setup.proposalRecoveryProtocol.initHistory := by
    apply setup.proposalRecoveryModel.runBehavioralTerminalFrom_congr
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
        setup.proposalRecoveryProtocol.initHistory
    intro later _ running who
    exact prescribed n who later running
  refine ⟨scale, sourceBad, nativeBad, weights, source, limit, native, index, ?_⟩
  change StrictMono index ∧ _
  refine ⟨increasing, positive, scaleLimit.comp increasing.tendsto_atTop,
    sourceBadLimit.comp increasing.tendsto_atTop,
    nativeBadLimit.comp increasing.tendsto_atTop,
    errorLimit.comp increasing.tendsto_atTop,
    mixed, bayes, converges, prescribed, gains, rational, extension, initialized,
    nativeStrategy, nativeMixed, nativeBayes, ?_, ?_, ?_⟩
  · intro n observer site massPositive
    exact posterior.1 (index n) (pins (index n)) (weights (index n)) (source (index n))
      (prescribed (index n)) (bayes (index n)) observer site massPositive
  · intro n observer site massPositive
    exact posterior.2.1 (index n) (pins (index n)) (weights (index n)) (native (index n))
      (nativeStrategy (index n)) (nativeBayes (index n)) observer site massPositive
  · intro n nativeReadout sourceReadout
    have law := posterior.2.2.2 pins weights (index n)
    rw [initialEq, ← sourceTerminal (index n),
      InformationModel.runBehavioralTerminalFrom_initHistory
        setup.proposalRecoveryModel setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
          (source (index n)).strategy setup.proposalRecoveryProtocol_bounded] at law
    have typedLaw : PMF.WithinTV (error (index n))
        (((app).finish initial horizon scheduler
          (phaseProposalReferencePolicy setup mode runtime leaks bounds plan
            (domain (index n)) (rates (index n))) none).map nativeReadout)
        ((setup.proposalRecoveryModel.runBehavioral (source (index n)).strategy
          sourceHorizon).map sourceReadout) := law
    have projected := congrArg (PMF.map nativeReadout) (nativeRun (index n))
    rw [PMF.map_comp] at projected
    rw [← projected] at typedLaw
    exact typedLaw

end Vegas
