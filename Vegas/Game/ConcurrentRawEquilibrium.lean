/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ConcurrentRawSequentialPreservation
import Vegas.Game.PhaseProposalConsistentSequence
import Vegas.Game.ProposalRecoveryInitializedLaw
import Vegas.Source.ProposalRecoveryFiniteness
import Vegas.Pending.ReservedEpochFinite
import GameTheoryExtensions.Analysis.Protocol.LocalSimulationLimit
import GameTheoryExtensions.Analysis.Protocol.SuccessRanking

/-! # Raw concurrent equilibrium from local gain comparisons

The remaining analytic premise compares local gains along the actual prescribed
source and native sequences. The composition constructs the counted equilibrium,
its initialized joint law and its raw audited extension. It does not discharge
the local comparison premise or assert concurrent preservation unconditionally.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
  GameTheory.Enforcement Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (implementation : ReservedConcurrentImplementation setup)
  (payoffs : ConcurrentPayoffs setup) (countAudit : ConcurrentCountAudit setup)

local notation "app" => implementation.application
local notation "menu" => PhaseCount.onePacketMenu implementation.runtime
  implementation.leaks implementation.bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu implementation.runtime implementation.leaks implementation.bounds)
    implementation.initial implementation.horizon implementation.scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu implementation.runtime implementation.leaks implementation.bounds)
    implementation.initial implementation.horizon implementation.scheduler
local notation "S" => setup.proposalRecoveryModel
local notation "Hs" => (Fintype.card Player + 1) * (instructionCount setup.program + 1)
local notation "Hn" => 2 * implementation.horizon + 1

open Classical in
/-- Actual prescribed local comparisons suffice for the complete fixed raw
preservation contract. All sequence premises below are supplied by the existing
common source/native construction; none assumes an equilibrium, initialized law
or conditional source sampler on the native side. -/
theorem concurrentRawSequentialPreservation_of_local_comparisons
    (comparisons :
      ∀ [setup.FiniteInitialLaw] [Fintype setup.proposalRecoveryProtocol.History]
        [(app).FiniteNature implementation.initial implementation.scheduler],
      ∀ (scale sourceBad nativeBad : ℕ → Set.Icc (0 : ℝ) 1)
        (values : ℕ → ∀ who (key : setup.ProposalRecoveryComponent who),
          PMF (setup.CommitRecoveryValueChoice who key.1))
        (source : ℕ → (S).BehavioralAssessment) (native : ℕ → (N).BehavioralAssessment),
        (∀ n, 0 < (scale n).val ∧ (scale n).val ≤ 1 / 4 ∧
          0 < (sourceBad n).val ∧ (sourceBad n).val ≤ (scale n).val ∧
          0 < (nativeBad n).val ∧ (nativeBad n).val ≤ (scale n).val) →
        Tendsto (fun n => (scale n).val) atTop (nhds 0) →
        (∀ n who key, FullSupport (values n who key)) →
        (∀ n who (history : setup.proposalRecoveryProtocol.History)
          (_running : ¬ setup.proposalRecoveryProtocol.terminal history.state),
          (source n).strategy who ((S).infoOf who history.trace) =
            setup.proposalRecoveryNormalizedTrembledProfile
              (scale n).val (scale n).property.1 (scale n).property.2
              (sourceBad n).val (sourceBad n).property.1 (sourceBad n).property.2
              (scale n).val (scale n).property.1 (scale n).property.2
              (values n) who ((S).infoOf who history.trace)) →
        (∀ n, (source n).IsFullyMixed) →
        (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent S (source n)
          setup.proposalRecoveryModel_decisionAntichain) →
        (∀ n, (native n).strategy = phaseProposalReferenceStrategy setup .concurrent
          implementation.runtime implementation.leaks implementation.bounds implementation.plan
          implementation.initial implementation.horizon implementation.scheduler (values n)
          ⟨nativeBad n, scale n, scale n, scale n⟩) →
        (∀ n, (native n).IsFullyMixed) →
        (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent N (native n)
          ((menu).decisionInformationAntichain implementation.initial implementation.horizon
            implementation.scheduler)) →
        (∀ n who (site : (S).InformationSite who),
          0 < (S).informationMass (source n).strategy who site →
          (∑ history : (S).InformationHistory who site.1 with
            (∃ owner : Player, who ≠ owner ∧
              setup.GeneratedPreparationHistory owner history.val),
            ((source n).belief who site history).toReal) ≤ (scale n).val) →
        (∀ n who (site : (N).InformationSite who),
          0 < (N).informationMass (native n).strategy who site →
          (∑ history : (N).InformationHistory who site.1 with
            (∃ owner : Player, who ≠ owner ∧
              PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
                implementation.leaks implementation.bounds implementation.initial
                implementation.horizon implementation.scheduler owner history.val),
            ((native n).belief who site history).toReal) ≤ (scale n).val) →
        ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
          ∀ n who (site : (N).InformationSite who) (law : PMF ((N).Choice who site.1)),
            (N).localGain Hn (fun history => history.state) (implementation.base payoffs)
                (native n) site law ≤ error n ∨
            ∃ (sourceSite : (S).InformationSite who)
              (sourceLaw : PMF ((S).Choice who sourceSite.1)),
              (N).localGain Hn (fun history => history.state) (implementation.base payoffs)
                  (native n) site law ≤
                (S).localGain Hs id
                  (fun history owner => setup.proposalRecoveryPayoff payoffs.utility
                    payoffs.excludedPayoff owner history)
                  (source n) sourceSite sourceLaw + error n) :
    ConcurrentRawSequentialPreservation setup implementation payoffs countAudit := by
  classical
  intro valid honestLimit honestEquilibrium
  let : setup.FiniteInitialLaw := valid.operational.finiteInitial
  let : Finite setup.proposalRecoveryProtocol.History :=
    setup.proposalRecovery_finite_history valid.operational.finiteBindings
  let := Fintype.ofFinite setup.proposalRecoveryProtocol.History
  let : implementation.leaks.FiniteSupport := by
    rw [valid.operational.completePending]
    infer_instance
  have finiteInitial : implementation.initial.support.Finite := by
    simpa only [ReservedConcurrentImplementation.initial, PMF.support_map] using
      setup.initialLaw_support_finite.image
        (fun theta => PhaseRuntimeState.initial implementation.plan (encodeInputs theta))
  let nativeFiniteNature : (app).FiniteNature implementation.initial
      implementation.scheduler := by
    simpa only [ReservedConcurrentImplementation.application,
      ReservedConcurrentImplementation.scheduler] using
      ReservedEpoch.implementation_finiteNature implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) implementation.prior
        implementation.initial finiteInitial
  let _ : (phaseApplication implementation.runtime implementation.leaks).FiniteNature
      (PMF.map (fun theta => PhaseRuntimeState.initial implementation.plan (encodeInputs theta))
        setup.initialLaw)
      (ReservedEpoch.implementation implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime) implementation.prior).scheduler :=
    nativeFiniteNature
  let restriction := setup.proposalRecoveryRestriction valid.operational.wellFormed
  have : Finite setup.intendedProtocol.History :=
    Finite.of_injective restriction.history restriction.history.injective
  let := Fintype.ofFinite (Σ who, setup.intendedModel.InformationSite who)
  obtain ⟨honest, approximates, honestConverges⟩ := honestEquilibrium.2
  let mass (n : ℕ) (entry : Σ who, setup.intendedModel.InformationSite who) : ℝ :=
    (setup.intendedModel.informationMass (honest n).strategy entry.1 entry.2).toReal
  have massPositive (n : ℕ) (entry : Σ who, setup.intendedModel.InformationSite who) :
      0 < mass n entry :=
    ENNReal.toReal_pos
      (setup.intendedModel.informationMass_pos_of_fullSupport _
        (approximates n).1 entry.1 entry.2).ne'
      (ne_top_of_le_ne_top ENNReal.one_ne_top
        (setup.intendedModel.informationMass_le_one _ entry.1 entry.2
          (setup.intended_decision_antichain entry.1 entry.2)))
  let reach (n : ℕ) : ℝ := ∏ entry, min (1 : ℝ) (mass n entry)
  have reachPositive (n : ℕ) : 0 < reach n :=
    Finset.prod_pos fun entry _ => lt_min zero_lt_one (massPositive n entry)
  have reachBound (n : ℕ) (entry : Σ who, setup.intendedModel.InformationSite who) :
      reach n ≤ mass n entry := by
    have bound := Finset.prod_le_prod_of_subset_of_le_one₀
      (s := {entry}) (t := Finset.univ) (f := fun other => min (1 : ℝ) (mass n other))
      (Finset.subset_univ _) (fun other _ => (lt_min zero_lt_one (massPositive n other)).le)
      (fun other _ _ => min_le_left _ _)
    have single : reach n ≤ min (1 : ℝ) (mass n entry) := by
      simpa only [Finset.prod_singleton] using bound
    exact single.trans (min_le_right _ _)
  obtain ⟨scale, sourceBad, nativeBad, weights, source, limit, native, index, coherent⟩ :=
    exists_phaseProposal_consistent_sequence setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan implementation.prior
      valid.operational.completePending valid.operational.outputValues
      valid.operational.maximalPhases valid.operational.finiteBindings
      valid.operational.wellFormed implementation.activationGap implementation.processingGap
      valid.operational.boundedGaps valid.operational.timely valid.operational.candidateReserve
      honest honestLimit (fun n => (approximates n).1) (fun n => (approximates n).2)
      honestConverges reach reachPositive (fun n who site => reachBound n ⟨who, site⟩)
      payoffs.utility payoffs.excludedPayoff valid.payoffs.excluded_le honestEquilibrium
  let rates := fun n => (⟨nativeBad n, scale n, scale n, scale n⟩ : PhaseProposalRates)
  let pins := fun n => setup.proposalRecoveryHonestPoolPins
    valid.operational.wellFormed (honest n).strategy
  let domain := fun n => setup.proposalRecoveryPooledDomainLaw
    valid.operational.finiteBindings (scale n).val (scale n).property.1 (scale n).property.2
      (pins n) (weights n)
  let lawError := fun n =>
    ((Fintype.card Player * Hn : Nat) : ℝ) * (rates n).flagBound +
      ((Fintype.card Player * Hs : Nat) : ℝ) *
        ((scale n).val + (sourceBad n).val + (scale n).val)
  rcases coherent with ⟨_increasing, positive, scaleLimit, _sourceBadLimit, _nativeBadLimit,
    lawErrorLimit, sourceMixed, sourceBayes, sourceConverges, sourcePrescribed, _pooled,
    sourceEquilibrium, extension, _initialized, nativePrescribed, nativeMixed, nativeBayes,
    sourcePosterior, nativePosterior, initializedClose⟩
  obtain ⟨error, errorLimit, localComparisons⟩ := comparisons
    (fun n => scale (index n)) (fun n => sourceBad (index n))
    (fun n => nativeBad (index n)) (fun n => domain (index n))
    (fun n => source (index n)) (fun n => native (index n))
    (fun n => ⟨(positive (index n)).1, (positive (index n)).2.2.1,
      (positive (index n)).2.2.2⟩) scaleLimit
    (fun n who key => setup.proposalRecoveryPooledDomainLaw_fullSupport
      valid.operational.finiteBindings _ (positive (index n)).1 _ _ _ who key)
    (fun n => sourcePrescribed (index n)) (fun n => sourceMixed (index n))
    (fun n => sourceBayes (index n)) (fun n => nativePrescribed (index n))
    (fun n => nativeMixed (index n)) (fun n => nativeBayes (index n))
    sourcePosterior nativePosterior
  let Outcome := Option (State L setup.context) × Option (Finset Player) ×
    Option (State L setup.program.terminalCtx) × (Player → ℝ)
  let sourceObserve : setup.proposalRecoveryProtocol.History → Outcome := fun history =>
    ((setup.protocolReadout (setup.commitRecoverySourceState history.state)).map
        (initialState setup.program),
      history.state.map CommitRecoveryState.excluded,
      setup.protocolReadout (setup.commitRecoverySourceState history.state),
      fun who => setup.proposalRecoveryPayoff payoffs.utility payoffs.excludedPayoff who history)
  let targetObserve : (E).History → Outcome := fun history =>
    ((phaseSourceReadout setup .concurrent implementation.runtime implementation.leaks
        history.state).map (initialState setup.program),
      history.state.map (fun current => current.execution.application.current.excluded),
      phaseSourceReadout setup .concurrent implementation.runtime implementation.leaks
        history.state,
      implementation.base payoffs history.state)
  let utility : Outcome → Player → ℝ := fun outcome who => outcome.2.2.2 who
  have sourceRational :=
    (limit.isSequentialEquilibrium_iff_truncated_of_bounded S
      setup.proposalRecoveryModel_decisionAntichain
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
      setup.proposalRecoveryProtocol_bounded
      (setup.proposalRecoveryPayoff payoffs.utility payoffs.excludedPayoff)).mp sourceEquilibrium
  obtain ⟨counted, countedEquilibrium, countedLaw, _subsequence⟩ :=
    InformationModel.exists_sequentialEquilibrium_limit_of_local_comparisons_of_lawError
      sourceObserve targetObserve Hs Hn
      ((menu).bounded implementation.initial implementation.horizon implementation.scheduler)
      ((menu).decisionRecall implementation.initial implementation.horizon implementation.scheduler)
      utility limit (fun n => source (index n)) sourceConverges sourceRational.1
      (fun n => native (index n)) (fun n => nativeMixed (index n))
      (fun n => nativeBayes (index n)) error errorLimit
      (by
        intro n who site law
        rcases localComparisons n who site law with small | ⟨sourceSite, sourceLaw, bound⟩
        · left
          simpa only [InformationModel.localGain, InformationModel.assessmentComparisonWith,
            expect_map, Function.comp_def, targetObserve, utility] using small
        · right
          refine ⟨PMF.pure (sourceSite,
            ((source (index n)).strategy who).withLaw sourceSite.1 sourceLaw), ?_⟩
          simpa only [expect_pure, InformationModel.localGain,
            InformationModel.assessmentComparisonWith, expect_map, Function.comp_def,
            sourceObserve, targetObserve, utility, id_eq] using bound)
      (fun n => lawError (index n)) lawErrorLimit
      (fun n outcome => (initializedClose n).apply outcome)
  have countedSE :=
    (counted.isSequentialEquilibrium_iff_truncated_of_bounded N
      ((menu).decisionInformationAntichain implementation.initial implementation.horizon
        implementation.scheduler)
      ((menu).bounded implementation.initial implementation.horizon
        implementation.scheduler).wellFoundedHistories
      ((menu).bounded implementation.initial implementation.horizon implementation.scheduler)
      (fun who history => implementation.base payoffs history.state who)).mpr countedEquilibrium
  have countedClear (history : (E).History)
      (supported : history ∈ ((N).runBehavioral counted.strategy Hn).support) (who : Player) :
      ¬ PhaseExcluded setup .concurrent implementation.runtime implementation.leaks
        who history.state := by
    have projected : targetObserve history ∈
        (((N).runBehavioral counted.strategy Hn).map targetObserve).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨history, supported, rfl⟩
    rw [countedLaw] at projected
    obtain ⟨original, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp projected
    have clear := setup.proposalRecovery_run_clear valid.operational.wellFormed
      honestLimit.strategy limit.strategy extension Hs original reached
    have exclusions := congrArg (fun outcome : Outcome => outcome.2.1) same
    change original.state.map CommitRecoveryState.excluded =
      history.state.map (fun control => control.execution.application.current.excluded)
      at exclusions
    cases nativeState : history.state with
    | none => simp only [PhaseExcluded, not_false_eq_true]
    | some control =>
        cases sourceState : original.state with
        | none =>
            have impossible : (none : Option (Finset Player)) =
                some control.execution.application.current.excluded := by
              simpa only [sourceState, nativeState, Option.map_none, Option.map_some]
                using exclusions
            cases impossible
        | some current =>
            have empty : current.excluded = ∅ := by
              simpa only [Setup.CommitRecoveryClear, sourceState, Option.elim_some] using clear
            have equal : current.excluded = control.execution.application.current.excluded := by
              simpa only [sourceState, nativeState,
                Option.map_some, Option.some.injEq] using exclusions
            simp only [PhaseExcluded, ← equal, empty, Finset.notMem_empty, not_false_eq_true]
  let countedCertificate :=
    ((menu).bounded implementation.initial implementation.horizon
      implementation.scheduler).wellFoundedHistories
  have countedTerminal : (N).runBehavioralTerminalFrom countedCertificate counted.strategy
      (E).initHistory = (N).runBehavioral counted.strategy Hn :=
    (N).runBehavioralTerminalFrom_initHistory countedCertificate counted.strategy
      ((menu).bounded implementation.initial implementation.horizon implementation.scheduler)
  have intendedBounded : setup.intendedProtocol.BoundedHorizon Hs := by
    intro state trace enough
    apply setup.intended_bounded state trace
    have fuelBound : instructionCount setup.program + 1 ≤ Hs := by
      nlinarith [Nat.zero_le (Fintype.card Player)]
    exact fuelBound.trans enough
  have sourceJoint := setup.proposalRecovery_initialized_joint valid.operational.wellFormed
    payoffs.utility payoffs.excludedPayoff honestLimit.strategy limit.strategy extension Hs
  have countedObservation :
      ((N).runBehavioralTerminalFrom countedCertificate counted.strategy (E).initHistory).map
        (fun final => ConcurrentTerminalObservation.read setup
          (phaseSourceReadout setup .concurrent implementation.runtime implementation.leaks
            final.state) (implementation.base payoffs final.state)) =
        payoffs.jointLaw honestLimit := by
    let project := fun outcome : Outcome =>
      ConcurrentTerminalObservation.read setup outcome.2.2.1 outcome.2.2.2
    have countedProjected := congrArg (PMF.map project) countedLaw
    have sourceProjected := congrArg (PMF.map fun pair :
        Option (State L setup.program.terminalCtx) × (Player → ℝ) =>
      ConcurrentTerminalObservation.read setup pair.1 pair.2) sourceJoint
    rw [countedTerminal]
    unfold ConcurrentPayoffs.jointLaw
    rw [setup.intendedModel.runBehavioralTerminalFrom_initHistory
      setup.intended_bounded.wellFoundedHistories honestLimit.strategy intendedBounded]
    simp only [PMF.map_comp, Function.comp_def, project, sourceObserve, targetObserve]
      at countedProjected sourceProjected
    exact countedProjected.trans sourceProjected.symm
  obtain ⟨raw, rawSE, _profile, _beliefs, historyLaw, settlementLaw, noCharges⟩ :=
    PhaseCount.onePacket_raw_sequentialEquilibrium implementation.runtime implementation.leaks
      implementation.bounds implementation.initial implementation.horizon implementation.scheduler
      countAudit.service countAudit.observationRate countAudit.deliveryRate
      valid.audit.delivery_nonnegative valid.audit.coverage (implementation.base payoffs)
      (fun who => min 0 (min (payoffs.excludedPayoff who) (payoffs.lowerUtility who)))
      (fun who => max 0 (max (payoffs.excludedPayoff who) (payoffs.upperUtility who)))
      countAudit.deposit
      (fun state who => (phaseExclusionBase_mem_Icc setup .concurrent implementation.runtime
        implementation.leaks payoffs.utility payoffs.excludedPayoff payoffs.lowerUtility
        payoffs.upperUtility valid.payoffs.lower_le valid.payoffs.le_upper state who).1)
      (fun state who => (phaseExclusionBase_mem_Icc setup .concurrent implementation.runtime
        implementation.leaks payoffs.utility payoffs.excludedPayoff payoffs.lowerUtility
        payoffs.upperUtility valid.payoffs.lower_le valid.payoffs.le_upper state who).2)
      valid.audit.deposit_nonnegative valid.audit.sufficient counted countedSE
  refine ⟨raw, rawSE, ?_, ?_, noCharges⟩
  · have projected := congrArg (PMF.map fun pair :
        (implementation.rawMenu.protocol implementation.initial implementation.horizon
          implementation.scheduler).History × (Player → ℝ) =>
      ConcurrentTerminalObservation.read setup
        (phaseSourceReadout setup .concurrent implementation.runtime implementation.leaks
          pair.1.state) pair.2) settlementLaw
    have sameState (history : (E).History) :
        ((PhaseCount.onePacketRestriction implementation.runtime implementation.leaks
          implementation.bounds implementation.initial implementation.horizon
          implementation.scheduler).history history).state = history.state := rfl
    have projectedLaw :
        ((N).runBehavioralTerminalFrom countedCertificate counted.strategy (E).initHistory).map
          (fun final => ConcurrentTerminalObservation.read setup
            (phaseSourceReadout setup .concurrent implementation.runtime implementation.leaks
              final.state) (implementation.base payoffs final.state)) =
          implementation.jointLaw payoffs countAudit raw := by
      simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def,
        ReservedConcurrentImplementation.jointLaw, ReservedConcurrentImplementation.terminalLaw,
        ReservedConcurrentImplementation.audit, sameState] using projected
    exact countedObservation.symm.trans projectedLaw
  · intro final supported who
    have mapped : final ∈
        (((N).runBehavioralTerminalFrom countedCertificate counted.strategy (E).initHistory).map
          (PhaseCount.onePacketRestriction implementation.runtime implementation.leaks
            implementation.bounds implementation.initial implementation.horizon
            implementation.scheduler).history).support :=
      Eq.mpr (congrArg (fun law : PMF
        (implementation.rawMenu.protocol implementation.initial implementation.horizon
          implementation.scheduler).History => final ∈ law.support) historyLaw) supported
    obtain ⟨original, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp mapped
    have reached' : original ∈ ((N).runBehavioral counted.strategy Hn).support :=
      countedTerminal ▸ reached
    exact countedClear original reached' who

end Vegas
