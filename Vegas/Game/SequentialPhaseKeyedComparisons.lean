/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseKeyedGains
import Vegas.Game.SequentialPhaseKeyedPureChoices
import Vegas.Game.SequentialPhaseNativeValueError
import Vegas.Game.RecoveryKeyedCommitmentComparisons
import Vegas.Game.RecoveryIrregularBeliefBounds
import Vegas.Game.RecoveryUnintendedValue
import Vegas.Game.RecoveryLatePureChoices
import Vegas.Game.RecoveryNonLateChoices
import GameTheoryExtensions.Analysis.Protocol.GainComparison

/-! # Pure keyed deviations in the original phase game -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (phaseInitialLaw setup) scheduler]

local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup leaks scheduler
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup)
    (RecoveryLeaks)
  (RecoveryScheduler)
local notation "R" => recoveryModel setup leaks bounds horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) (RecoveryLeaks) bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) (RecoveryLeaks)
local notation "N" => onePacketModel setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol (RMenu) RecoveryPrior horizon
  (RecoveryScheduler)
local notation "NP" => onePacketProtocol setup (RecoveryLeaks) bounds horizon (NativeScheduler)
local notation "RawNative" => ReactiveApplication.protocol (application setup (RecoveryLeaks))
  (PMF.map RecoveryState.native (RecoveryPrior)) horizon (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant (app := application setup
    (RecoveryLeaks))
  (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

local notation "P" => phaseApplication (runtime setup) leaks
local notation "M" => model setup leaks bounds horizon scheduler
local notation "projectInfo" => PhaseRecoveryProjection.information (runtime setup) leaks
    (RecoveryLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

variable {Public : Type*} {signal : State L setup.context → Public}

open Classical in
/-- Every original phase pure keyed deviation is harmless up to a uniform
vanishing error or bounded by an actual lottery of intended source gains. -/
theorem keyed_local_comparisons [Finite setup.intendedProtocol.History]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup (RecoveryLeaks) bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds horizon scheduler bounds.candidateCount p))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : PhaseService.Opportunity (runtime setup) leaks (phaseInitialLaw setup) horizon
      scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks (phaseInitialLaw setup)
      horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (rawCertificate : (RawNative).WellFoundedHistories)
    (certificate : (NP).WellFoundedHistories)
    (completes : PhaseService.CompletesPlay (runtime setup) leaks (phaseInitialLaw setup)
      horizon scheduler)
    (phaseAssessments : ℕ → (M).BehavioralAssessment)
    (fallback : ℕ → ∀ who, (M).Policy who)
    (assembled : ∀ n, (phaseAssessments n).strategy =
      componentStrategy setup leaks bounds horizon scheduler (fallback n) (sequence n) (scale n)
        (positive n).le (le_one n) (weights n))
    (mixed : ∀ n, (phaseAssessments n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (M) (phaseAssessments n)
      ((menu setup leaks bounds).decisionInformationAntichain (phaseInitialLaw setup) horizon
          scheduler))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (nonnegative : 0 ≤ payoffBound)
    (payoffBounded : ∀ history :
      ((menu setup leaks bounds).protocol (phaseInitialLaw setup) horizon scheduler).History,
      ∀ who, |phaseExclusionBase setup .sequential (runtime setup) leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
          history.state who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound)
    (slots_pos : 0 < bounds.candidateCount)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (upper : Player → ℝ) (le_upper : ∀ outcome who, utility outcome who ≤ upper who)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (pooled : ∀ n
      (alternative : ∀ p,
        PMF (Part setup leaks bounds horizon scheduler bounds.candidateCount p)) p,
      ∑ agent ∈ Finset.univ.filter
        (fun agent => pool setup leaks bounds horizon scheduler agent = p),
        (if decision : (M).IsDecisionInfo agent.1 agent.2.1 then
          localGain (2 * horizon + 1) (fun final => final.state)
            (phaseExclusionBase setup .sequential (runtime setup) leaks
              (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
            (phaseAssessments n) (who := agent.1) ⟨agent.2.1, decision⟩
            ((alternative (pool setup leaks bounds horizon scheduler agent)).bind
              (component setup leaks bounds horizon scheduler (sequence n) (scale n)
                (positive n).le (le_one n) agent)) else 0) ≤ 0) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (M).InformationSite who) (clear : ClearInput setup leaks site.1),
      ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
        (KeyedAgent setup leaks bounds horizon scheduler) ((M).agentAt site) →
      ¬ RecoveryOnePacket.OwingAgent setup (RecoveryLeaks) bounds RecoveryPrior horizon
          (RecoveryScheduler)
        (projectedAgent setup leaks bounds horizon scheduler ((M).agentAt site) clear) →
      ∀ choice : (M).Choice who site.1,
      GainComparison
        (localGain (2 * horizon + 1) (fun final => final.state)
          (phaseExclusionBase setup .sequential (runtime setup) leaks
            (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
          (phaseAssessments n) site (PMF.pure choice))
        (intendedSiteGain setup parameter utility excludedPayoff (sequence n) (who := who))
        (error n) := by
  obtain ⟨memberError, memberLimit, members⟩ := keyed_component_mixture_gain_bounds setup leaks
    bounds horizon scheduler wellFormed independent observable sequence sourceMixed scale positive
    le_one scaleEq covers coversInputs capacity weights opportunity inclusion timely rawCertificate
    certificate completes phaseAssessments fallback assembled mixed bayes parameter utility
    excludedPayoff nonnegative payoffBounded excludedBounded slots_pos readoutBounded upper le_upper
    below pooled
  obtain ⟨score, affineError, affineLimit, scoreUnit, affineValues⟩ := keyed_component_value_bounds
    setup leaks bounds horizon scheduler wellFormed independent observable sequence sourceMixed
    scale positive le_one scaleEq covers coversInputs capacity weights opportunity inclusion timely
    rawCertificate certificate completes phaseAssessments fallback assembled mixed bayes parameter
    utility excludedPayoff nonnegative payoffBounded excludedBounded slots_pos readoutBounded upper
    le_upper below
  obtain ⟨valueError, valueLimit, comparisonValues⟩ := localValue_native_comparison_error_vanishes
    setup leaks bounds horizon scheduler wellFormed independent observable sequence sourceMixed
    scale positive le_one scaleEq covers coversInputs capacity weights opportunity inclusion timely
    rawCertificate certificate completes phaseAssessments fallback assembled mixed bayes parameter
    utility excludedPayoff nonnegative payoffBounded excludedBounded
  obtain ⟨nativeError, nativeLimit, nativeCommitments⟩ :=
    RecoveryOnePacket.nativeComparison_keyed_commitment_comparisons_of_counted_service setup
      (RecoveryLeaks) bounds horizon (RecoveryScheduler) wellFormed independent observable covers
          coversInputs
      capacity slots_pos sequence sourceMixed sourceBayes scale positive le_one scaleEq
      (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n))
      (fun control trace clear => PhaseService.Opportunity.clear_native_counted setup leaks bounds
        horizon scheduler delay opportunity trace clear)
      (fun control trace clear => PhaseService.ProtectedInclusion.clear_native_counted setup leaks
        bounds horizon scheduler bound inclusion trace clear) timely
      (fun control trace clear ended => PhaseService.CompletesPlay.clear_native_counted setup leaks
        bounds horizon scheduler completes trace clear ended)
      parameter utility excludedPayoff nonnegative readoutBounded excludedBounded
  obtain ⟨irregularError, irregularLimit, irregular⟩ :=
    RecoveryOnePacket.nativeComparison_irregular_bounds setup (RecoveryLeaks) bounds horizon
      (RecoveryScheduler) wellFormed independent observable sequence sourceMixed scale positive
          le_one
      scaleEq covers coversInputs capacity
      (fun n => recoveryComparisonWeights setup leaks bounds horizon scheduler (weights n))
  have scaleLimit : Tendsto scale atTop (nhds 0) := by
    have identity : scale = fun n => trembleScale
        (combinedFloor setup (RecoveryLeaks) bounds horizon NativeScheduler (sequence n))
        (2 * horizon + 2) n := funext scaleEq
    rw [identity]
    exact tendsto_trembleScale _
      (fun n => combinedFloor_pos setup (RecoveryLeaks) bounds horizon NativeScheduler (sequence n))
      (fun n => combinedFloor_le_one setup (RecoveryLeaks) bounds horizon NativeScheduler (sequence
          n))
  let error := fun n => |nativeError n| + |memberError n| + 2 * |valueError n| +
    |affineError n| + 2 * payoffBound * |irregularError n| + 6 * scale n * payoffBound
  have errorLimit : Tendsto error atTop (nhds 0) := by
    simpa only [error, abs_zero, zero_mul, mul_zero, add_zero, zero_add] using
      (((((nativeLimit.abs.add memberLimit.abs).add (valueLimit.abs.const_mul 2)).add
        affineLimit.abs).add (irregularLimit.abs.const_mul (2 * payoffBound))).add
          ((scaleLimit.const_mul 6).mul_const payoffBound))
  refine ⟨error, errorLimit, ?_⟩
  intro n who site clear keyed notOwing choice
  have positiveTerms : 0 ≤ 2 * payoffBound * |irregularError n| ∧
      0 ≤ 6 * scale n * payoffBound := by
    have := (positive n).le
    constructor <;> positivity
  obtain ⟨past, view, event, _key, atSite, turn, _siteKey⟩ :=
    keyed_information setup leaks bounds horizon scheduler site keyed.1
  have viewClear : view.application.2.excluded = ∅ := by
    rw [atSite] at clear
    exact clear
  obtain ⟨nativeSite, lifted, input, nativeNotFree, nativeNotOwing, values⟩ :=
    comparisonValues n who site past view atSite viewClear keyed.2 notOwing event turn
  have nativeKeyed : ownedKeyed (Vegas.FreeAgent setup (RecoveryLeaks) bounds horizon
      (NativeScheduler))
      (LateDeliveryAgent setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
          (NativeScheduler))
      ((N).agentAt nativeSite) := by
    refine ⟨?_, nativeNotFree⟩
    change LateDelivery setup (RecoveryLeaks) who nativeSite.1
    rw [input]
    exact keyed.1
  obtain ⟨nativePast, nativeView, nativeEvent, nativeAt, nativePending, _old⟩ := nativeKeyed.1
  let equivalent := ((choiceEquiv setup leaks bounds horizon scheduler ((M).agentAt site)
    clear).trans (Equiv.cast (congrArg (fun input => (R).Choice who input) lifted.symm))).trans
      (RecoveryOnePacket.sourceNativeChoiceEquiv setup (RecoveryLeaks) bounds horizon
          (RecoveryScheduler) who
        nativeSite.1)
  let nativeChoice := equivalent choice
  let target := nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
    positive le_one weights n
  let common := target.strategy
  let stopped := fun final : (NP).History => ¬ Clear final.state ∨
    DecodedState setup (RecoveryLeaks) (failureProfile setup.program)
      (ProtocolState.OwesFailure who setup.program) final.state
  let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
    exclusionBase setup parameter utility excludedPayoff (RecoveryLeaks) final.state who
  let nativeValue := fun law => expect (target.belief who nativeSite) (fun history =>
    expect ((N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) common who
        ((common who).withLaw nativeSite.1 law)) stopped history.1) payoff)
  let phasePayoff := phaseExclusionBase setup .sequential (runtime setup) leaks
    (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
  let actualValue := fun law => localValue (2 * horizon + 1) (fun final => final.state)
    phasePayoff (phaseAssessments n) site law
  let actualOption := fun option : LateOption bounds.candidateCount => keyedComponent setup leaks
    bounds horizon scheduler (sequence n) (scale n) (positive n).le (le_one n)
    ((M).agentAt site) option
  let nativeOption := fun option : LateOption bounds.candidateCount =>
    onePacketLate setup (RecoveryLeaks) bounds horizon (NativeScheduler) sequence scale positive
        le_one n
      ((N).agentAt nativeSite) option
  have pureNear := values (PMF.pure choice)
  dsimp only at pureNear
  simp only [PMF.pure_map] at pureNear
  change |actualValue (PMF.pure choice) - nativeValue (PMF.pure nativeChoice)| ≤ valueError n
    at pureNear
  have optionNear : ∀ option, |actualValue (actualOption option) -
      nativeValue (nativeOption option)| ≤ valueError n := by
    intro option
    have near := values (actualOption option)
    dsimp only at near
    have same := keyedComponent_native_choice setup leaks bounds horizon scheduler (sequence n)
      (scale n) (positive n).le (le_one n) site clear nativeSite lifted option
    rw [same] at near
    exact near
  have memberAt : ∀ option,
      localGain (2 * horizon + 1) (fun final => final.state) phasePayoff (phaseAssessments n) site
        (actualOption option) ≤ memberError n := by
    intro option
    exact keyed_component_gain_le_of_mixtures setup leaks bounds horizon scheduler (sequence n)
      (scale n) (positive n).le (le_one n) site keyed (phaseAssessments n)
      (fun final => final.state) phasePayoff (members n who site keyed) option
  have viaNative : ∀ option,
      localGain (2 * horizon + 1) (fun final => final.state)
          phasePayoff (phaseAssessments n) site
          (PMF.pure choice) ≤ nativeValue (PMF.pure nativeChoice) -
        nativeValue (nativeOption option) + 2 * valueError n + memberError n := by
    intro option
    have nativeNear := optionNear option
    have member := memberAt option
    rw [localGain_eq_sub] at member ⊢
    change actualValue (actualOption option) - _ ≤ _ at member
    change actualValue (PMF.pure choice) - _ ≤ _
    linarith [(abs_le.mp pureNear).2, (abs_le.mp nativeNear).1]
  have viaMain : ∀ (option : LateOption bounds.candidateCount),
      lateChoice setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon NativeScheduler
        (sequence n) who nativeSite.1 option = PMF.pure nativeChoice →
      localGain (2 * horizon + 1) (fun final => final.state)
          phasePayoff (phaseAssessments n) site
          (PMF.pure choice) ≤ 6 * scale n * payoffBound + memberError n := by
    intro option main
    have near := keyed_main_value_sub_le setup leaks bounds horizon scheduler (sequence n) (scale n)
      (positive n).le (le_one n) site clear nativeSite lifted option nativeChoice main
      (phaseAssessments n) (fun final => final.state) phasePayoff
      (fun final => payoffBounded final who)
    change |actualValue (PMF.pure (equivalent.symm nativeChoice)) -
      actualValue (actualOption option)| ≤ 6 * scale n * payoffBound at near
    have same : equivalent.symm nativeChoice = choice := equivalent.symm_apply_apply choice
    rw [same] at near
    have member := memberAt option
    rw [localGain_eq_sub] at member ⊢
    change actualValue (actualOption option) - _ ≤ _ at member
    change actualValue (PMF.pure choice) - _ ≤ _
    linarith [(abs_le.mp near).2]
  by_cases intendedChoice : IntendedCommitment setup (RecoveryLeaks) bounds horizon NativeScheduler
      nativeSite nativeChoice
  · have metadata := intendedChoice
    obtain ⟨p, v, response, material, named, serial, payload, outputEq, value, atNative, selected,
      sends, packet, _after, _offered⟩ := metadata
    have submitted : (runtime setup).submittedEvent? (RecoveryLeaks) response = some named := by
      unfold EventGraphRuntime.submittedEvent?
      simp only [sends, packet, Payload.event?]
    have atTurn := commitsAtTurn_of_notOwing wellFormed nativeSite nativeNotOwing nativeChoice
      selected submitted
    obtain ⟨option, deviation, success, successNonneg, successLe, bounded⟩ := nativeCommitments
      n who
      nativeSite nativeChoice nativeNotFree nativeNotOwing nativeKeyed atTurn intendedChoice
    dsimp only at bounded
    rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)] at bounded
    change nativeValue (PMF.pure nativeChoice) - nativeValue (nativeOption option) ≤
      success * intendedSiteGain setup parameter utility excludedPayoff (sequence n) deviation +
        nativeError n at bounded
    let baseline : setup.intendedModel.AssessmentDeviation who :=
      ⟨deviation.1, (sequence n).strategy who⟩
    have zero : intendedSiteGain setup parameter utility excludedPayoff (sequence n) baseline = 0 :=
      by simp [intendedSiteGain, baseline, InformationModel.assessmentComparisonWith,
        InformationModel.assessmentLawWith, Profile.update_eq_self]
    refine GainComparison.of_weighted
      (intendedSiteGain setup parameter utility excludedPayoff (sequence n))
      ⟨success, successNonneg, successLe⟩ deviation baseline zero ?_
    have gain := viaNative option
    have covered : nativeError n + 2 * valueError n + memberError n ≤ error n := by
      dsimp only [error]
      linarith [le_abs_self (nativeError n), le_abs_self (valueError n), le_abs_self
        (memberError n),
        abs_nonneg (affineError n), positiveTerms.1, positiveTerms.2]
    linarith only [gain, bounded, covered]
  left
  obtain ⟨response, selected, member⟩ := choice_response setup (RecoveryLeaks) bounds horizon
    NativeScheduler nativeSite nativeAt nativeChoice
  have simpleCovered : 6 * scale n * payoffBound + memberError n ≤ error n := by
    dsimp only [error]
    linarith [abs_nonneg (nativeError n), abs_nonneg (valueError n), abs_nonneg (affineError n),
      positiveTerms.1, le_abs_self (memberError n)]
  cases sends : response.transmission with
  | none =>
      have silent : nativeChoice = silenceChoice setup (RecoveryLeaks) bounds (Vegas.initialLaw
          setup)
          horizon NativeScheduler who nativeSite.1 := by
        apply Subtype.ext
        rw [selected, nativeAt]
        change some response = (silenceChoice setup (RecoveryLeaks) bounds (Vegas.initialLaw setup)
          horizon NativeScheduler who (some (nativePast, nativeView))).1
        have responseEq : response = ⟨none⟩ :=
          congrArg (fun transmission =>
            (⟨transmission⟩ : (application setup (RecoveryLeaks)).Action)) sends
        rw [responseEq]
        simp only [silenceChoice, responseChoice]
        split <;> rfl
      have main : lateChoice setup (RecoveryLeaks) bounds (Vegas.initialLaw setup) horizon
          NativeScheduler (sequence n) who nativeSite.1 (none : LateOption bounds.candidateCount) =
            PMF.pure nativeChoice := by
        rw [silent, nativeAt, lateChoice_none]
      exact (viaMain none main).trans simpleCovered
  | some material =>
      obtain ⟨named, submitted⟩ := submittedEvent_of_transmits setup (RecoveryLeaks) bounds member
          sends
      have atTurn := commitsAtTurn_of_notOwing wellFormed nativeSite nativeNotOwing nativeChoice
        selected submitted
      cases packet : material.call.packet with
      | malformed raw => exact (onePacket_not_malformed bounds member sends raw packet).elim
      | commitment named candidate =>
          let nativeBelief := target.belief who nativeSite
          have debtFree := siteDebtFree_of_not_owing setup (RecoveryLeaks) bounds horizon
              NativeScheduler
            nativeNotOwing
          have forced := forcedAgent_of_not_free setup (RecoveryLeaks) bounds horizon
              NativeScheduler
            nativeNotFree
          have unforcedMass : expect nativeBelief (fun history =>
              if ForcedState setup (RecoveryLeaks) who history.1.state then (0 : ℝ) else 1) ≤
                |irregularError n| := by
            have rows : ∀ history ∈ nativeBelief.support,
                (if ForcedState setup (RecoveryLeaks) who history.1.state then (0 : ℝ) else 1) ≤
                if RegularTrace setup (RecoveryLeaks) bounds horizon NativeScheduler (sequence n)
                    who
                    history.1.trace then 0 else 1 := by
              intro history _supported
              by_cases regular : RegularTrace setup (RecoveryLeaks) bounds horizon NativeScheduler
                  (sequence n) who history.1.trace
              · have ownIntended :=
                  ownCompletionsIntended_of_siteNotOwes wellFormed debtFree history
                have forcing := forcedState_of_regular wellFormed (sequence n) nativeAt forced
                  history regular ownIntended
                simp only [forcing, regular, ↓reduceIte, le_refl]
              · simp only [regular, ↓reduceIte]
                split <;> norm_num
            have averaged := expect_mono rows (payoffIntegrable_of_finite _ _)
              (payoffIntegrable_of_finite _ _)
            have pendingHere := nativePending
            rw [nativeAt] at pendingHere
            have rare := irregular n who nativeSite nativeNotFree nativeNotOwing nativeAt
              (pendingEvent_spec pendingHere).1
            exact averaged.trans (rare.trans (le_abs_self _))
          have bad := RecoveryOnePacket.unintendedCommitment_value_sub_le setup (RecoveryLeaks)
              bounds
            horizon (RecoveryScheduler) wellFormed
            (fun control trace clear ended => PhaseService.CompletesPlay.clear_native_counted setup
              leaks bounds horizon scheduler completes trace clear ended)
            target nativeSite nativeChoice nativeNotOwing atTurn intendedChoice nativeAt response
            selected material sends named candidate packet parameter utility excludedPayoff
            (readoutBounded who) (excludedBounded who) unforcedMass
          change |nativeValue (PMF.pure nativeChoice) - excludedPayoff who| ≤
            2 * payoffBound * |irregularError n| at bad
          obtain ⟨affineSite, _input, lower, affine⟩ := affineValues n who site clear keyed.2
            notOwing keyed.1
          have productNonneg := mul_nonneg
            (scoreUnit n (agentKey setup leaks bounds horizon scheduler ((M).agentAt site))
              none).1 (sub_nonneg.mpr lower)
          have optionLower : excludedPayoff who - affineError n ≤ actualValue (actualOption none) :=
            by have near := affine none; linarith [(abs_le.mp near).1]
          have memberBound := memberAt none
          rw [localGain_eq_sub] at memberBound ⊢
          change actualValue (actualOption none) - _ ≤ _ at memberBound
          change actualValue (PMF.pure choice) - _ ≤ _
          have covered : 2 * payoffBound * |irregularError n| + valueError n + affineError n +
              memberError n ≤ error n := by
            dsimp only [error]
            linarith [abs_nonneg (nativeError n), abs_nonneg (valueError n),
              le_abs_self (valueError n), le_abs_self (affineError n), le_abs_self (memberError n),
              positiveTerms.2]
          linarith [(abs_le.mp pureNear).2, (abs_le.mp bad).2]
      | opening named handle raw =>
          have packetSubmitted : (runtime setup).submittedEvent? (RecoveryLeaks) response = some
              named :=
            by
            unfold EventGraphRuntime.submittedEvent?
            simp only [sends, packet, Payload.event?]
          obtain ⟨p, v, turnResponse, turnEvent, seen, turnChosen, turnSubmitted, namedTurn⟩ :=
            atTurn
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (nativeAt.symm.trans seen))
          have responseEq := Option.some.inj (selected.symm.trans turnChosen)
          subst turnResponse
          have eventEq := Option.some.inj (packetSubmitted.symm.trans turnSubmitted)
          subst turnEvent
          have pendingHere := nativePending
          rw [nativeAt] at pendingHere
          have namedEq : named = nativeEvent :=
            Option.some.inj (namedTurn.symm.trans (pendingEvent_spec pendingHere).1)
          subst named
          have main := RecoveryOnePacket.lateChoice_eq_pure_opening setup (RecoveryLeaks) bounds
              horizon
            (RecoveryScheduler) wellFormed
            (sequence n) nativeSite nativeNotFree
            (siteDebtFree_of_not_owing setup (RecoveryLeaks) bounds horizon NativeScheduler
              nativeNotOwing)
            nativeAt nativePending nativeChoice selected member sends packet
            (⟨0, slots_pos⟩ : Fin bounds.candidateCount)
          exact (viaMain (some ⟨0, slots_pos⟩) main).trans simpleCovered

end Vegas.SequentialPhase
