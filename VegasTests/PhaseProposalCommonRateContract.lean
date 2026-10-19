/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalCommonPerturbations

/-! # One concrete sequence for both preparation posteriors and initialized laws -/

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

open Classical in
/-- Both bad rates are chosen after their actual response floors and before
any pooled weights. The resulting uniform foreign posteriors and the original
initialized joint-law error vanish along the same concrete sequence. -/
example
    [Fintype setup.proposalRecoveryProtocol.History]
    [(app).FiniteNature initial scheduler]
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (finite : setup.program.FiniteBindingTypes)
    (initialValues : ∀ theta ∈ setup.initialLaw.support,
      ∀ {name : VarId} {owner : Player} {payload : L.Ty}
        (cell : HasVar setup.context name (.commitment owner payload)),
        ∃ value, theta.get cell = .success value)
    (activationGap processingGap : Nat)
    (gaps : ∀ tape ∈ prior.support,
      tape.BoundedGaps (ReservedEpoch.completionCycles runtime) activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : horizon ≤ bounds.candidateCount)
    (reach : ℕ → ℝ) (reachPositive : ∀ n, 0 < reach n)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    ∃ scale sourceBad nativeBad : ℕ → Set.Icc (0 : ℝ) 1,
      (∀ n, 0 < (scale n).val ∧ (scale n).val ≤ relativeTremble reach n ∧
        (scale n).val ≤ 1 / 4 ∧
        0 < (sourceBad n).val ∧ (sourceBad n).val ≤ (scale n).val ∧
        0 < (nativeBad n).val ∧ (nativeBad n).val ≤ (scale n).val) ∧
      Tendsto (fun n => (scale n).val) atTop (nhds 0) ∧
      Tendsto (fun n => (sourceBad n).val) atTop (nhds 0) ∧
      Tendsto (fun n => (nativeBad n).val) atTop (nhds 0) ∧
      let rates := fun n => (⟨nativeBad n, scale n, scale n, scale n⟩ : PhaseProposalRates)
      let domain := fun n pins weights => setup.proposalRecoveryPooledDomainLaw finite
        (scale n).val (scale n).property.1 (scale n).property.2 pins weights
      let sourceProfile := fun n pins weights => setup.proposalRecoveryNormalizedTrembledProfile
        (scale n).val (scale n).property.1 (scale n).property.2
        (sourceBad n).val (sourceBad n).property.1 (sourceBad n).property.2
        (scale n).val (scale n).property.1 (scale n).property.2 (domain n pins weights)
      (∀ n pins weights (assessment : setup.proposalRecoveryModel.BehavioralAssessment),
        (∀ who (history : setup.proposalRecoveryProtocol.History)
          (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
          assessment.strategy who (setup.proposalRecoveryModel.infoOf who history.trace) =
            sourceProfile n pins weights who
              (setup.proposalRecoveryModel.infoOf who history.trace)) →
        InformationModel.BehavioralAssessment.IsBayesConsistent setup.proposalRecoveryModel
          assessment setup.proposalRecoveryModel_decisionAntichain →
        ∀ observer (site : setup.proposalRecoveryModel.InformationSite observer),
          0 < setup.proposalRecoveryModel.informationMass assessment.strategy observer site →
          (∑ history : setup.proposalRecoveryModel.InformationHistory observer site.1 with
            (∃ owner : Player, observer ≠ owner ∧
              setup.GeneratedPreparationHistory owner history.val),
            (assessment.belief observer site history).toReal) ≤ (scale n).val) ∧
      (∀ n pins weights (assessment : (N).BehavioralAssessment),
        assessment.strategy = phaseProposalReferenceStrategy setup mode runtime leaks bounds plan
          initial horizon scheduler (domain n pins weights) (rates n) →
        InformationModel.BehavioralAssessment.IsBayesConsistent (N) assessment
          ((menu).decisionInformationAntichain initial horizon scheduler) →
        ∀ observer (site : (N).InformationSite observer),
          0 < (N).informationMass assessment.strategy observer site →
          (∑ history : (N).InformationHistory observer site.1 with
            (∃ owner : Player, observer ≠ owner ∧
              PhaseProposal.GeneratedUnusableBindingHistory runtime leaks bounds initial horizon
                scheduler owner history.val),
            (assessment.belief observer site history).toReal) ≤ (scale n).val) ∧
      let error := fun n =>
        (((Fintype.card Player * (2 * horizon + 1) : Nat) : ℝ) * (rates n).flagBound +
          ((Fintype.card Player *
            ((Fintype.card Player + 1) * (instructionCount setup.program + 1)) : Nat) : ℝ) *
              ((scale n).val + (sourceBad n).val + (scale n).val))
      Tendsto error atTop (nhds 0) ∧
      ∀ (pins : ℕ → (pool : setup.ProposalRecoveryValuePool) →
          Option (PMF (setup.ProposalRecoveryPoolPart pool)))
        (weights : ℕ → (pool : setup.ProposalRecoveryValuePool) →
          PMF (setup.ProposalRecoveryPoolPart pool)) (n : Nat),
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
        PMF.WithinTV (error n)
          (((app).finish (PMF.map (PhaseRuntimeState.initial plan)
            (PMF.map encodeInputs setup.initialLaw)) horizon scheduler
              (phaseProposalReferencePolicy setup mode runtime leaks bounds plan
                (domain n (pins n) (weights n)) (rates n)) none).map nativeReadout)
          ((setup.proposalRecoveryModel.runBehavioralTerminalFrom
            setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
              (sourceProfile n (pins n) (weights n))
                setup.proposalRecoveryProtocol.initHistory).map sourceReadout) := by
  exact exists_phaseProposal_common_perturbations setup mode runtime leaks bounds plan prior
    complete covered maximal finite initialValues activationGap processingGap gaps margin capacity
      reach reachPositive utility excludedPayoff

end Vegas
