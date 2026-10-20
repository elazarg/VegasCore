/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ConcurrentRawSequentialPreservation
import Vegas.Game.PhaseProposalConsistentSequence
import Vegas.Game.PhaseProposalCurrentBindingGain
import Vegas.Game.PhaseProposalPublicationGain
import Vegas.Game.PhaseProposalCleanBindingGain
import Vegas.Game.ProposalRecoveryInitializedLaw
import Vegas.Source.ProposalRecoveryFiniteness
import Vegas.Pending.ReservedEpochFinite
import GameTheoryExtensions.Analysis.Protocol.LocalSimulationLimit
import GameTheoryExtensions.Analysis.Protocol.SuccessRanking

/-! # Raw concurrent equilibrium from local gain comparisons

Native decisions are classified at their original complete information and
compared with legal source deviations along one shared sequence. The limit
retains the initialized joint law through the raw audited extension.
-/

noncomputable section

namespace Vegas


open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
  GameTheory.Enforcement Filter

attribute [local implicit_reducible] ReservedConcurrentImplementation.initial
  ReservedConcurrentImplementation.scheduler PhaseCount.onePacketMenu
  EventGraph.withMode Setup.eventGraph toEventGraph InformationModel.InformationSite
  ReactiveApplication.ResponseMenu.protocol


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

private theorem concurrent_payoff_bound (bounded : payoffs.Bounded) :
    let bound := ∑ who, (|payoffs.lowerUtility who| + |payoffs.upperUtility who| +
      |payoffs.excludedPayoff who|)
    0 ≤ bound ∧ (∀ terminal who, |payoffs.utility terminal who| ≤ bound) ∧
      (∀ who, |payoffs.excludedPayoff who| ≤ bound) := by
  classical
  intro bound
  have component (who : Player) :
      |payoffs.lowerUtility who| + |payoffs.upperUtility who| +
        |payoffs.excludedPayoff who| ≤ bound :=
    Finset.single_le_sum (f := fun owner : Player =>
      |payoffs.lowerUtility owner| + |payoffs.upperUtility owner| +
        |payoffs.excludedPayoff owner|) (fun owner _ =>
      add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
        (Finset.mem_univ who)
  refine ⟨Finset.sum_nonneg (fun owner _ =>
    add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)), ?_, ?_⟩
  · intro terminal who
    apply abs_le.mpr
    have lower := bounded.lower_le terminal who
    have upper := bounded.le_upper terminal who
    have total := component who
    constructor
    · linarith [neg_abs_le (payoffs.lowerUtility who),
        abs_nonneg (payoffs.upperUtility who), abs_nonneg (payoffs.excludedPayoff who)]
    · linarith [le_abs_self (payoffs.upperUtility who),
        abs_nonneg (payoffs.lowerUtility who), abs_nonneg (payoffs.excludedPayoff who)]
  · intro who
    linarith [component who, abs_nonneg (payoffs.lowerUtility who),
      abs_nonneg (payoffs.upperUtility who)]

private theorem concurrent_error_le_scale
    (bound : ℝ) (nonnegative : 0 ≤ bound) (nativeCount sourceCount : ℕ)
    (scale sourceBad nativeBad : Set.Icc (0 : ℝ) 1)
    (sourceSmall : sourceBad.val ≤ scale.val) (nativeSmall : nativeBad.val ≤ scale.val)
    (nativePast sourcePast : ℝ) (nativePastSmall : nativePast ≤ scale.val)
    (sourcePastSmall : sourcePast ≤ scale.val) :
    2 * bound * (nativePast + (2 * nativeCount + 1) *
        (⟨nativeBad, scale, scale, scale⟩ : PhaseProposalRates).flagBound) +
        4 * bound * (sourcePast + sourceCount * (2 * scale.val + sourceBad.val)) ≤
      bound * (14 + 16 * nativeCount + 12 * sourceCount) * scale.val := by
  have nativeFlags : (⟨nativeBad, scale, scale, scale⟩ : PhaseProposalRates).flagBound ≤
      4 * scale.val := by
    dsimp only [PhaseProposalRates.flagBound]
    linarith
  have sourceFlags : 2 * scale.val + sourceBad.val ≤ 3 * scale.val := by linarith
  have nativeLoss := mul_le_mul_of_nonneg_left
    (add_le_add nativePastSmall
      (mul_le_mul_of_nonneg_left nativeFlags (by positivity :
        (0 : ℝ) ≤ 2 * nativeCount + 1))) (by positivity : 0 ≤ 2 * bound)
  have sourceLoss := mul_le_mul_of_nonneg_left
    (add_le_add sourcePastSmall
      (mul_le_mul_of_nonneg_left sourceFlags (by positivity : (0 : ℝ) ≤ sourceCount)))
    (by positivity : 0 ≤ 4 * bound)
  nlinarith [nativeLoss, sourceLoss]

open Classical in
/-- Each actual native local deviation has negligible gain or is bounded by a
legal local deviation at the same finite-index source assessment. -/
theorem concurrentRaw_local_gain_le
    [setup.FiniteInitialLaw] [Fintype setup.proposalRecoveryProtocol.History]
    [(app).FiniteNature implementation.initial implementation.scheduler]
    (operational : implementation.Operational) (bounded : payoffs.Bounded)
    (qualified : PhaseProposalQualifiedBinding.QualifiedBindingLaw setup implementation)
    (scale sourceBad nativeBad : Set.Icc (0 : ℝ) 1)
    (positive : 0 < scale.val ∧ scale.val ≤ 1 / 4 ∧
      0 < sourceBad.val ∧ sourceBad.val ≤ scale.val ∧
      0 < nativeBad.val ∧ nativeBad.val ≤ scale.val)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (source : (S).BehavioralAssessment) (native : (N).BehavioralAssessment)
    (sourcePrescribed : ∀ who (history : setup.proposalRecoveryProtocol.History),
      ¬ setup.proposalRecoveryProtocol.terminal history.state →
      source.strategy who ((S).infoOf who history.trace) =
        setup.proposalRecoveryNormalizedTrembledProfile
          scale.val scale.property.1 scale.property.2
          sourceBad.val sourceBad.property.1 sourceBad.property.2
          scale.val scale.property.1 scale.property.2 values who
            ((S).infoOf who history.trace))
    (sourceMixed : source.IsFullyMixed)
    (sourceBayes : InformationModel.BehavioralAssessment.IsBayesConsistent S source
      setup.proposalRecoveryModel_decisionAntichain)
    (nativePrescribed : native.strategy = phaseProposalReferenceStrategy setup .concurrent
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
      implementation.initial implementation.horizon implementation.scheduler values
      ⟨nativeBad, scale, scale, scale⟩)
    (nativeMixed : native.IsFullyMixed)
    (nativeBayes : InformationModel.BehavioralAssessment.IsBayesConsistent N native
      ((menu).decisionInformationAntichain implementation.initial implementation.horizon
        implementation.scheduler))
    (sourcePosterior : ∀ who (site : (S).InformationSite who),
      0 < (S).informationMass source.strategy who site →
      (∑ history : (S).InformationHistory who site.1 with
        (∃ owner : Player, who ≠ owner ∧
          setup.GeneratedPreparationHistory owner history.val),
        (source.belief who site history).toReal) ≤ scale.val)
    (nativePosterior : ∀ who (site : (N).InformationSite who),
      0 < (N).informationMass native.strategy who site →
      (∑ history : (N).InformationHistory who site.1 with
        (∃ owner : Player, who ≠ owner ∧
          PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
            implementation.leaks implementation.bounds implementation.initial
            implementation.horizon implementation.scheduler owner history.val),
        (native.belief who site history).toReal) ≤ scale.val)
    (who : Player) (site : (N).InformationSite who) (law : PMF ((N).Choice who site.1)) :
    let bound := ∑ owner, (|payoffs.lowerUtility owner| + |payoffs.upperUtility owner| +
      |payoffs.excludedPayoff owner|)
    let error := bound * (14 + 16 * (Fintype.card Player * Hn : ℕ) +
      12 * (Fintype.card Player * Hs : ℕ)) * scale.val
    (N).localGain Hn (fun history => history.state) (implementation.base payoffs)
        native site law ≤ error ∨
      ∃ (sourceSite : (S).InformationSite who)
        (sourceLaw : PMF ((S).Choice who sourceSite.1)),
        (N).localGain Hn (fun history => history.state) (implementation.base payoffs)
            native site law ≤
          (S).localGain Hs id
            (fun history owner => setup.proposalRecoveryPayoff payoffs.utility
              payoffs.excludedPayoff owner history) source sourceSite sourceLaw + error := by
  classical
  intro bound error
  obtain ⟨nonnegative, utilityBound, excludedBound⟩ :=
    concurrent_payoff_bound setup payoffs bounded
  change 0 ≤ bound at nonnegative
  have scaleNonnegative := scale.property.1
  have sourceNonnegative := sourceBad.property.1
  let rates : PhaseProposalRates := ⟨nativeBad, scale, scale, scale⟩
  let nativePast := ∑ history : (N).InformationHistory who site.1 with
    (∃ owner : Player, who ≠ owner ∧
      PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
        implementation.leaks implementation.bounds implementation.initial implementation.horizon
        implementation.scheduler owner history.val), (native.belief who site history).toReal
  have nativePastSmall : nativePast ≤ scale.val := nativePosterior who site
    ((N).informationMass_pos_of_fullSupport _ nativeMixed who site)
  have scaleBelow : scale.val < 1 := lt_of_le_of_lt positive.2.1 (by norm_num)
  have sourceBelow : sourceBad.val < 1 := positive.2.2.2.1.trans_lt scaleBelow
  have nativeBelow : nativeBad.val < 1 := positive.2.2.2.2.2.trans_lt scaleBelow
  have negligible : 2 * bound *
      (nativePast + (2 * (Fintype.card Player * Hn : ℕ) + 1) * rates.flagBound) ≤ error := by
    have estimate := concurrent_error_le_scale bound nonnegative
      (Fintype.card Player * Hn) (Fintype.card Player * Hs) scale sourceBad nativeBad
      positive.2.2.2.1 positive.2.2.2.2.2 nativePast 0 nativePastSmall scale.property.1
    have extra : (0 : ℝ) ≤ 4 * bound *
        (0 + (Fintype.card Player * Hs : ℕ) * (2 * scale.val + sourceBad.val)) := by
      positivity
    change _ ≤ error at estimate
    dsimp only [rates]
    linarith
  have errorNonnegative : 0 ≤ error := by dsimp only [error]; positivity
  obtain ⟨history, _running, action, offered⟩ := site.property
  obtain ⟨past, view, information⟩ : ∃ past view, site.1 = some (past, view) := by
    cases observed : site.1 with
    | none =>
        have impossible := offered
        change some action ∈ (N).menu who site.1 at impossible
        simp only [observed, ReactiveApplication.ResponseMenu.information,
          Set.mem_singleton_iff] at impossible
        cases impossible
    | some pair => exact ⟨pair.1, pair.2, rfl⟩
  have actual : ∃ control : (app).Control, history.val.state = some control ∧
      control.actor = some who ∧ control.execution.recall who = past ∧
        control.execution.observe app who = view := by
    have observed := ((menu).info implementation.initial implementation.horizon
      implementation.scheduler who history.val.trace).symm.trans
        (history.property.trans information)
    cases current : history.val.state with
    | none => rw [current] at observed; cases observed
    | some control =>
        rw [current] at observed
        change (if control.actor = some who then
          some (control.execution.recall who, control.execution.observe app who) else none) =
            some (past, view) at observed
        split at observed
        · rename_i active
          exact ⟨control, rfl, active, (Prod.mk.inj (Option.some.inj observed)).1,
            (Prod.mk.inj (Option.some.inj observed)).2⟩
        · cases observed
  obtain ⟨control, current, active, recalled, observed⟩ := actual
  have counted : (E).Trace (some control) := current ▸ history.val.trace
  have initialEq : (setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan) = implementation.initial :=
    PMF.map_comp _ _ _
  have nestedCounted := initialEq.symm ▸ counted
  have callback : (E).Trace (some ⟨control.remaining, some who, control.execution⟩) := by
    simpa only [← active] using counted
  have nestedCallback := initialEq.symm ▸ callback
  let _ : (phaseApplication implementation.runtime implementation.leaks).FiniteNature
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      implementation.scheduler := by rw [initialEq]; infer_instance
  let _ : Fintype (((menu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
      (ReservedEpoch.executionHorizon implementation.runtime)
      (ReservedEpoch.implementation implementation.runtime implementation.leaks
        (ReservedEpoch.packetCapacity implementation.runtime)
          implementation.prior).scheduler).History)
      := by
    rw [PMF.map_comp]
    change Fintype (E).History
    infer_instance
  have silent (singleton : (menu).actions who past view = {⟨none⟩}) :
      (N).localGain Hn (fun final => final.state) (implementation.base payoffs)
        native site law = 0 := by
    have unique : ∀ first second : (N).Choice who site.1, first = second := by
      intro first second
      apply Subtype.ext
      have firstLegal := first.property
      have secondLegal := second.property
      simp only [information] at firstLegal secondLegal
      obtain ⟨firstAction, firstOffered, firstEq⟩ := firstLegal
      obtain ⟨secondAction, secondOffered, secondEq⟩ := secondLegal
      rw [singleton] at firstOffered secondOffered
      exact firstEq.trans ((congrArg some ((Finset.mem_singleton.mp firstOffered).trans
        (Finset.mem_singleton.mp secondOffered).symm)).trans secondEq.symm)
    let : Subsingleton ((N).Choice who site.1) := ⟨unique⟩
    let choice := (native.strategy who site.1).support_nonempty.choose
    have same : law = native.strategy who site.1 :=
      (eq_pure_of_subsingleton law choice).trans
        (eq_pure_of_subsingleton (native.strategy who site.1) choice).symm
    rw [same, (N).localGain_self]
  by_cases absent : ∀ coordinate, ¬control.execution.application.SeedRequest who coordinate
  · left
    have singleton := PhaseCount.onePacketActions_eq_singleton_of_no_request
      implementation.runtime implementation.leaks implementation.bounds implementation.plan
      (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
      control.remaining who control.execution nestedCallback absent
    rw [recalled, observed] at singleton
    rw [silent singleton]
    exact errorNonnegative
  obtain ⟨coordinate, requested⟩ := not_forall.mp absent
  have request : control.execution.application.SeedRequest who coordinate := not_not.mp requested
  have sameAttempt := request.1
  cases coordinate with
  | mk attempt event =>
    dsimp only at sameAttempt
    subst attempt
    have rawTrace := (menu).toRawTrace _ implementation.horizon implementation.scheduler
      nestedCounted
    obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history implementation.runtime
      implementation.leaks implementation.plan (setup.initialLaw.map encodeInputs)
        implementation.horizon implementation.scheduler rawTrace
    have publicRequest : PhaseRuntimeState.requests view.application.2 who
        ⟨view.application.2.attempt, event⟩ := by
      rw [← observed]
      exact (control.execution.application.requests_publicView valid who _).mpr request
    by_cases sent : ∃ message ∈ (app).outputs (control.execution.recall who),
        PhaseSeedScheduler.ownPacket ⟨control.execution.application.attempt, event⟩
          who message = true
    · left
      have singleton := PhaseCount.onePacketActions_eq_singleton_of_sent implementation.runtime
        implementation.leaks implementation.bounds implementation.plan
        (serviceGraph_revealRelaxedOrdered setup .concurrent) (setup.initialLaw.map encodeInputs)
        implementation.horizon implementation.scheduler control.remaining who control.execution
        nestedCallback _ request sent
      rw [recalled, observed] at singleton
      rw [silent singleton]
      exact errorNonnegative
    have unsent : ∀ message ∈ (app).outputs past,
        PhaseCount.event? message.payload ≠ some ⟨view.application.2.attempt, event⟩ := by
      intro message output named
      rw [← recalled] at output
      have recalledInputs := (app).history_inputRecall _ implementation.horizon
        implementation.scheduler rawTrace who
      rw [← recalledInputs] at output
      have ownerEq : message.sender = who := of_decide_eq_true (List.mem_filter.mp output).2
      obtain ⟨actualEvent, actualNamed, coordinateEq⟩ := Option.map_eq_some_iff.mp named
      have coordinates := CommitAttemptEvent.mk.inj coordinateEq
      apply sent
      refine ⟨message, ?_, ?_⟩
      · rw [← recalledInputs]; exact output
      · apply decide_eq_true
        exact ⟨ownerEq, coordinates.1.trans (by rw [← observed]; rfl),
          coordinates.2 ▸ actualNamed⟩
    cases node : nodeView (serviceGraph setup .concurrent) event with
    | bind actor payload binding code =>
      have ownerEq : actor = who := Option.some.inj
        (((serviceGraph setup .concurrent).actor?_of_outputLayout_binding binding).symm.trans
          request.2.2.2.1)
      subst actor
      by_cases branch : phaseProposalSavedBindingFailure setup .concurrent
          implementation.runtime implementation.leaks who event view ∨
        phaseProposalCurrentBindingFailure setup .concurrent implementation.runtime
          implementation.leaks who event view ∨
        (view.application.2.excluded \
          ((view.application.2.retired.map fun record =>
              record.2.sourceFailureFootprint.2).foldr (fun first rest => first ∪ rest) ∅ ∪
            view.application.2.native.sourceFailureFootprint.1
              view.application.2.attempt.phase)).Nonempty
      · left
        have debt := fun [finite : Fintype (((menu).protocol
          ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
          (ReservedEpoch.executionHorizon implementation.runtime)
          (ReservedEpoch.implementation implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime)
              implementation.prior).scheduler).History)] =>
          phaseProposal_current_binding_gain_le setup .concurrent
          implementation.runtime implementation.leaks implementation.bounds implementation.plan
          implementation.prior operational.completePending operational.outputValues
          operational.maximalPhases operational.wellFormed implementation.activationGap
          implementation.processingGap operational.boundedGaps operational.timely
          operational.candidateReserve values fullValues rates positive.1 scaleBelow positive.1
          positive.2.2.2.2.1 nativeBelow
        rw [PMF.map_comp] at debt
        exact (debt (finite := inferInstanceAs (Fintype (E).History)) native nativePrescribed
          who site past view information event payload binding
          publicRequest branch payoffs.utility payoffs.excludedPayoff bound nonnegative
          utilityBound (excludedBound who) (bounded.excluded_nonpositive who)
          (fun terminal => bounded.excluded_le terminal who) law).trans negligible
      have regular := not_or.mp branch
      have remaining := not_or.mp regular.2
      have comparison := phaseProposal_clean_binding_gain_le setup implementation payoffs
        operational bounded qualified
        scale sourceBad nativeBad positive.1 scaleBelow positive.2.2.1 sourceBelow
        positive.2.2.2.2.1 nativeBelow values fullValues source sourcePrescribed sourceMixed
        sourceBayes native nativePrescribed nativeMixed nativeBayes who site past view information
        event payload binding publicRequest unsent regular.1 remaining.1 remaining.2
        bound nonnegative utilityBound excludedBound law
      rcases comparison with small | ⟨sourceSite, sourceLaw, reached, comparison⟩
      · left
        exact small.trans negligible
      · right
        refine ⟨sourceSite, sourceLaw, ?_⟩
        have estimate := concurrent_error_le_scale bound nonnegative
          (Fintype.card Player * Hn) (Fintype.card Player * Hs) scale sourceBad nativeBad
          positive.2.2.2.1 positive.2.2.2.2.2 nativePast _ nativePastSmall
          (sourcePosterior who sourceSite reached)
        change _ ≤ error at estimate
        linarith
    | resolve actor payload publication checks outputEq codeEq =>
      left
      have actualActor : (serviceGraph setup .concurrent).actor? event = some actor := by
        change (((serviceGraph setup .concurrent).nodes event).actor) = _
        rw [← EventCode.actor_cast outputEq ((serviceGraph setup .concurrent).nodes event), codeEq]
        rfl
      have ownerEq : actor = who := Option.some.inj (actualActor.symm.trans request.2.2.2.1)
      subst actor
      have publicationGain := fun [finite : Fintype (((menu).protocol
          ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
          (ReservedEpoch.executionHorizon implementation.runtime)
          (ReservedEpoch.implementation implementation.runtime implementation.leaks
            (ReservedEpoch.packetCapacity implementation.runtime)
              implementation.prior).scheduler).History)] =>
          phaseProposal_publication_gain_le setup .concurrent
        implementation.runtime implementation.leaks implementation.bounds implementation.plan
        implementation.prior operational.completePending operational.outputValues
        operational.maximalPhases operational.wellFormed implementation.activationGap
        implementation.processingGap operational.boundedGaps operational.timely
        operational.candidateReserve values fullValues rates positive.1 scaleBelow positive.1
        positive.2.2.2.2.1 nativeBelow
      rw [PMF.map_comp] at publicationGain
      exact (publicationGain (finite := inferInstanceAs (Fintype (E).History))
        native nativePrescribed who site past view information event payload
        outputEq publicRequest payoffs.utility payoffs.excludedPayoff bound nonnegative
        utilityBound (excludedBound who) (bounded.excluded_nonpositive who)
        (fun terminal => bounded.excluded_le terminal who) law).trans negligible
    | sample payload sampleLaw outputEq codeEq =>
      have actualActor : (serviceGraph setup .concurrent).actor? event = none := by
        change (((serviceGraph setup .concurrent).nodes event).actor) = _
        rw [← EventCode.actor_cast outputEq ((serviceGraph setup .concurrent).nodes event), codeEq]
        rfl
      have impossible := request.2.2.2.1
      rw [actualActor] at impossible
      cases impossible

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

/-- Exact qualified binding transport suffices for preservation of every
intended equilibrium and its initialized joint outcome and audited payoff law. -/
theorem concurrentRawSequentialPreservation_of_qualified_binding_law
    (qualified : PhaseProposalQualifiedBinding.QualifiedBindingLaw setup implementation) :
    ConcurrentRawSequentialPreservation setup implementation payoffs countAudit := by
  classical
  intro valid
  apply (concurrentRawSequentialPreservation_of_local_comparisons setup implementation payoffs
    countAudit ?_) valid
  intro finiteInitial finiteSource finiteNature scale sourceBad nativeBad values source native
    positive scaleLimit fullValues sourcePrescribed sourceMixed sourceBayes nativePrescribed
    nativeMixed nativeBayes sourcePosterior nativePosterior
  let bound := ∑ who, (|payoffs.lowerUtility who| + |payoffs.upperUtility who| +
    |payoffs.excludedPayoff who|)
  let coefficient : ℝ := bound * (14 + 16 * (Fintype.card Player * Hn : ℕ) +
    12 * (Fintype.card Player * Hs : ℕ))
  refine ⟨fun n => coefficient * (scale n).val, ?_, ?_⟩
  · simpa only [mul_zero] using tendsto_const_nhds.mul scaleLimit
  · intro n who site law
    simpa only [bound, coefficient] using concurrentRaw_local_gain_le setup implementation
      payoffs valid.operational valid.payoffs qualified (scale n) (sourceBad n) (nativeBad n)
        (positive n) (values n) (fullValues n) (source n) (native n) (sourcePrescribed n)
        (sourceMixed n) (sourceBayes n) (nativePrescribed n) (nativeMixed n) (nativeBayes n)
        (sourcePosterior n) (nativePosterior n) who site law

end Vegas
