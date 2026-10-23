/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalInitializedLawError
import Vegas.Game.PhaseProposalPreparationPosterior
import Vegas.Game.ProposalRecoveryForeignPreparationPosterior
import GameTheory.Math.Probability.RelativeTremble

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
theorem exists_phaseProposal_common_perturbations
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
  classical
  let delta : ℕ → ℝ := fun n => relativeTremble reach n / 2
  have deltaPositive (n : Nat) : 0 < delta n :=
    div_pos (relativeTremble_pos reach reachPositive n) (by norm_num)
  have deltaBound (n : Nat) : delta n ≤ 1 / 4 := by
    have small : relativeTremble reach n ≤ 1 / 2 := by
      apply (relativeTremble_le_rate reach n).trans
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1 + 1)).mpr
      have nonnegative := Nat.cast_nonneg (α := ℝ) n
      nlinarith
    dsimp only [delta]
    linarith
  have deltaRelative (n : Nat) : delta n ≤ relativeTremble reach n := by
    have positive := relativeTremble_pos reach reachPositive n
    dsimp only [delta]
    linarith
  let scale : ℕ → Set.Icc (0 : ℝ) 1 := fun n =>
    ⟨delta n, (deltaPositive n).le, (deltaBound n).trans (by norm_num)⟩
  have scalePositive (n : Nat) : 0 < (scale n).val := deltaPositive n
  have scaleSmall (n : Nat) : (scale n).val < 1 := (deltaBound n).trans_lt (by norm_num)
  have scaleLimit : Tendsto (fun n => (scale n).val) atTop (nhds 0) := by
    simpa only [scale, delta, zero_div] using
      (relativeTremble_tendsto reach reachPositive).div_const (2 : ℝ)
  obtain ⟨sourceChance, sourceLength, sourceChancePositive, sourceChanceBounded,
    sourceFloor⟩ := setup.exists_proposalRecovery_foreignPreparation_posterior_bound finite
  obtain ⟨nativeChance, nativeLength, nativeChancePositive, nativeChanceBounded,
    nativeFloor⟩ := exists_phaseProposal_foreignPreparation_posterior_bound setup mode runtime
      leaks bounds plan horizon scheduler complete covered maximal finite
  let baseRates : ℕ → PhaseProposalRates := fun n =>
    ⟨scale n, scale n, scale n, scale n⟩
  have sourceLower (n : Nat) := sourceFloor (scale n).val (scalePositive n)
    (scale n).property.2 (scale n) (scale n)
      (scalePositive n) (scaleSmall n) (scalePositive n) (scaleSmall n)
  have nativeLower (n : Nat) := nativeFloor (scale n).val (scalePositive n)
    (scale n).property.2 (baseRates n) (scalePositive n) (scaleSmall n)
      (scalePositive n) (scalePositive n)
  choose sourceFloorValue sourceFloorPositive sourceFloorBounded sourcePosterior
    using sourceLower
  choose nativeFloorValue nativeFloorPositive nativeFloorBounded nativePosterior
    using nativeLower
  have selectRate (chance lower : ℝ) (length count : Nat)
      (chancePositive : 0 < chance) (chanceBounded : chance ≤ 1)
      (lowerPositive : 0 < lower) (lowerBounded : lower ≤ 1) (n : Nat) :
      ∃ bad : Set.Icc (0 : ℝ) 1,
        0 < bad.val ∧ bad.val ≤ (scale n).val ∧
          (Fintype.card Player : ℝ) *
            ((count : ℝ) * bad.val / (chance * lower ^ length)) ≤ (scale n).val := by
    let size : ℝ := (Fintype.card Player : ℝ) * count
    have sizeNonnegative : 0 ≤ size := by positivity
    have denominatorPositive : 0 < 1 + size := by positivity
    have powerPositive : 0 < lower ^ length := pow_pos lowerPositive _
    have productBounded : chance * lower ^ length ≤ 1 := by
      calc
        _ ≤ 1 * lower ^ length :=
          mul_le_mul_of_nonneg_right chanceBounded (pow_nonneg lowerPositive.le _)
        _ = lower ^ length := one_mul _
        _ ≤ 1 := pow_le_one₀ lowerPositive.le lowerBounded
    let bad : ℝ := (scale n).val * chance * lower ^ length / (1 + size)
    have badPositive : 0 < bad :=
      div_pos (mul_pos (mul_pos (scalePositive n) chancePositive) powerPositive)
        denominatorPositive
    have badBounded : bad ≤ (scale n).val := by
      apply (div_le_iff₀ denominatorPositive).mpr
      calc
        _ = (scale n).val * (chance * lower ^ length) := by ring
        _ ≤ (scale n).val := mul_le_of_le_one_right (scalePositive n).le productBounded
        _ ≤ (scale n).val * (1 + size) := by
          nlinarith [mul_nonneg (scalePositive n).le sizeNonnegative]
    refine ⟨⟨bad, badPositive.le, badBounded.trans (scale n).property.2⟩,
      badPositive, badBounded, ?_⟩
    have exactRatio : (Fintype.card Player : ℝ) *
        ((count : ℝ) * bad / (chance * lower ^ length)) =
          (scale n).val * size / (1 + size) := by
      dsimp only [bad, size]
      field_simp [ne_of_gt chancePositive, ne_of_gt powerPositive,
        ne_of_gt denominatorPositive]
    rw [exactRatio]
    apply (div_le_iff₀ denominatorPositive).mpr
    nlinarith [scalePositive n]
  have selectedSource (n : Nat) := selectRate sourceChance (sourceFloorValue n) sourceLength
    (Fintype.card setup.proposalRecoveryProtocol.History) sourceChancePositive sourceChanceBounded
      (sourceFloorPositive n) (sourceFloorBounded n) n
  have selectedNative (n : Nat) := selectRate nativeChance (nativeFloorValue n) nativeLength
    (Fintype.card (E).History) nativeChancePositive nativeChanceBounded
      (nativeFloorPositive n) (nativeFloorBounded n) n
  choose sourceBad sourceBadPositive sourceBadBounded sourceRatio using selectedSource
  choose nativeBad nativeBadPositive nativeBadBounded nativeRatio using selectedNative
  have sourceBadHalf (n : Nat) : (sourceBad n).val ≤ 1 / 2 :=
    (sourceBadBounded n).trans ((deltaBound n).trans (by norm_num))
  have nativeBadHalf (n : Nat) : (nativeBad n).val ≤ 1 / 2 :=
    (nativeBadBounded n).trans ((deltaBound n).trans (by norm_num))
  have sourceBadLimit : Tendsto (fun n => (sourceBad n).val) atTop (nhds 0) :=
    squeeze_zero (fun n => (sourceBadPositive n).le) sourceBadBounded scaleLimit
  have nativeBadLimit : Tendsto (fun n => (nativeBad n).val) atTop (nhds 0) :=
    squeeze_zero (fun n => (nativeBadPositive n).le) nativeBadBounded scaleLimit
  refine ⟨scale, sourceBad, nativeBad,
    (fun n => ⟨scalePositive n, deltaRelative n, deltaBound n, sourceBadPositive n,
      sourceBadBounded n, nativeBadPositive n, nativeBadBounded n⟩),
    scaleLimit, sourceBadLimit, nativeBadLimit, ?_⟩
  intro rates domain sourceProfile
  refine ⟨?_, ?_, ?_⟩
  · intro n pins weights assessment prescribed bayes observer site positive
    exact (sourcePosterior n (sourceBad n) (sourceBadPositive n) (sourceBadHalf n)
      pins weights assessment prescribed bayes observer site positive).trans (sourceRatio n)
  · intro n pins weights assessment prescribed bayes observer site positive
    exact (nativePosterior n (nativeBad n) (nativeBadPositive n) (nativeBadHalf n)
      pins weights assessment prescribed bayes observer site positive).trans (nativeRatio n)
  · intro error
    have flagLimit : Tendsto (fun n => (rates n).flagBound) atTop (nhds 0) := by
      simpa only [rates, PhaseProposalRates.flagBound, zero_add] using
        (((scaleLimit.add nativeBadLimit).add scaleLimit).add scaleLimit)
    have sourceFlagLimit : Tendsto
        (fun n => (scale n).val + (sourceBad n).val + (scale n).val) atTop (nhds 0) := by
      simpa only [zero_add] using (scaleLimit.add sourceBadLimit).add scaleLimit
    let nativeCount : ℝ := (Fintype.card Player * (2 * horizon + 1) : Nat)
    let sourceCount : ℝ := (Fintype.card Player *
      ((Fintype.card Player + 1) * (instructionCount setup.program + 1)) : Nat)
    have errorLimit : Tendsto error atTop (nhds 0) := by
      have nativeProduct : Tendsto (fun n => nativeCount * (rates n).flagBound)
          atTop (nhds 0) := by
        simpa only [mul_zero] using
          ((tendsto_const_nhds : Tendsto (fun _ : Nat => nativeCount)
            atTop (nhds nativeCount)).mul flagLimit)
      have sourceProduct : Tendsto (fun n => sourceCount *
          ((scale n).val + (sourceBad n).val + (scale n).val)) atTop (nhds 0) := by
        simpa only [mul_zero] using
          ((tendsto_const_nhds : Tendsto (fun _ : Nat => sourceCount)
            atTop (nhds sourceCount)).mul sourceFlagLimit)
      simpa only [error, nativeCount, sourceCount, zero_add] using
        nativeProduct.add sourceProduct
    refine ⟨errorLimit, ?_⟩
    intro pins weights n nativeReadout sourceReadout
    exact phaseProposal_initialized_joint_withinTV setup mode runtime leaks bounds plan
      complete covered maximal initialValues (domain n (pins n) (weights n))
        (setup.proposalRecoveryPooledDomainLaw_fullSupport finite (scale n).val
          (scalePositive n) (scale n).property.2 (pins n) (weights n))
        prior activationGap processingGap gaps margin capacity (rates n)
        (scalePositive n) (scaleSmall n) (scalePositive n) (nativeBadPositive n)
        ((nativeBadHalf n).trans_lt (by norm_num))
        (scale n).val (scale n).property.1 (scale n).property.2
        (sourceBad n).val (sourceBad n).property.1 (sourceBad n).property.2
        (scale n).val (scale n).property.1 (scale n).property.2 utility excludedPayoff

end Vegas
