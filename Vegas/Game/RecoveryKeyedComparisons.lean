/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryPooledMemberGains
import Vegas.Game.RecoveryKeyedCommitmentComparisons
import Vegas.Game.RecoveryLatePureChoices
import Vegas.Game.RecoveryUnintendedValue
import Vegas.Game.RecoveryIrregularBeliefBounds
import Vegas.Game.RecoveryNonLateChoices


/-! # All pure keyed comparisons under the original recovery assessment -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "RApp" => recoveryApplication (runtime setup) leaks
local notation "RawNative" => ReactiveApplication.protocol (application setup leaks)
  (PMF.map RecoveryState.native (Initial)) horizon (NativeScheduler)
local notation "ClearState" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native
    ∅))
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks

local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)

open Classical in
theorem recovery_keyed_local_comparisons [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [(recoveryApplication (runtime setup) leaks).FiniteNature Initial scheduler]
    [Finite setup.intendedProtocol.History]
    [∀ player, DecidableEq ((R).InfoState player)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependent)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slots_pos : 0 < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount p))
    (assessments : ℕ → (R).BehavioralAssessment)
    (fallback : ℕ → ∀ player, (R).Policy player)
    (assembled : ∀ n, (assessments n).strategy = (R).agentBehavior (R).playedInformation
      (fallback n)
      (fun agent => (weights n (pool setup leaks bounds Initial horizon scheduler agent)).bind
        (component setup leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (R) (assessments n)
      ((RMenu).decisionInformationAntichain Initial horizon scheduler))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (payoffBound : ℝ) (nonnegative : 0 ≤ payoffBound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    (payoffBounded : ∀ who (final : (RP).History),
      |recoveryExclusionBase parameter utility excludedPayoff final.state who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (upper : Player → ℝ) (le_upper : ∀ outcome who, utility outcome who ≤ upper who)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (pooled : ∀ n (alternative : ∀ p,
        PMF (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount p)) p,
      ∑ agent ∈ Finset.univ.filter
          (fun agent => pool setup leaks bounds Initial horizon scheduler agent = p),
        (if decision : (R).IsDecisionInfo agent.1 agent.2.1 then
          ((assessments n).continuationContext
              ((RMenu).bounded Initial horizon scheduler).wellFoundedHistories
              ⟨agent.2.1, decision⟩
              (fun final => recoveryExclusionBase parameter utility excludedPayoff final.state
                agent.1)).value
              (((assessments n).strategy agent.1).withLaw agent.2.1
                ((alternative (pool setup leaks bounds Initial horizon scheduler agent)).bind
                  (component setup leaks bounds Initial horizon scheduler (sequence n) (scale n)
                    (positive n).le (le_one n) agent))) -
            ((assessments n).continuationContext
              ((RMenu).bounded Initial horizon scheduler).wellFoundedHistories
              ⟨agent.2.1, decision⟩
              (fun final => recoveryExclusionBase parameter utility excludedPayoff final.state
                agent.1)).value ((assessments n).strategy agent.1)
        else 0) ≤ 0) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (R).InformationSite who),
        ¬ FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ¬ OwingAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ownedKeyed (FreeAgent setup leaks bounds Initial horizon scheduler)
          (KeyedAgent setup leaks bounds Initial horizon scheduler) ((R).agentAt site) →
        ∀ choice : (R).Choice who site.1,
          localGain (2 * horizon + 1) (fun final => final.state)
              (recoveryExclusionBase parameter utility excludedPayoff) (assessments n) site
              (PMF.pure choice) ≤ error n ∨
          ∃ mixture : PMF (setup.intendedModel.AssessmentDeviation who),
            localGain (2 * horizon + 1) (fun final => final.state)
                (recoveryExclusionBase parameter utility excludedPayoff) (assessments n) site
                (PMF.pure choice) ≤
              expect mixture (intendedSiteGain setup parameter utility excludedPayoff (sequence
                n)) +
                error n := by
  let certificate := ((NMenu).bounded (initialLaw setup) horizon
    NativeScheduler).wellFoundedHistories
  let rawCertificate := ((application setup leaks).bounded ((Initial).map RecoveryState.native)
    horizon NativeScheduler).wellFoundedHistories
  let recoveryCertificate := ((RApp).bounded Initial horizon scheduler).wellFoundedHistories
  let menuCertificate := ((RMenu).bounded Initial horizon scheduler).wellFoundedHistories
  let globalUpper := ∑ who : Player, |upper who|
  have above : ∀ outcome who, utility outcome who ≤ globalUpper := by
    intro outcome who
    exact (le_upper outcome who).trans ((le_abs_self _).trans
      (Finset.single_le_sum (fun player _ => abs_nonneg (upper player)) (Finset.mem_univ who)))
  obtain ⟨memberError, memberLimit, members⟩ := recovery_pooled_member_gain_bounds setup leaks
    bounds
    horizon scheduler wellFormed independent sequence sourceMixed scale positive le_one scaleEq
    covers coversInputs capacity weights assessments fallback assembled bayes opportunity inclusion
    timely certificate rawCertificate parameter utility excludedPayoff payoffBound nonnegative
    recoveryCertificate menuCertificate completes payoffBounded excludedBounded slots_pos
    readoutBounded globalUpper above below pooled
  obtain ⟨continuation, score, affineError, affineLimit, scoreUnit, affineValues⟩ :=
    recovery_keyed_component_value_bounds setup leaks bounds horizon scheduler wellFormed
      independent
      sequence sourceMixed scale positive le_one scaleEq covers coversInputs capacity weights
      assessments fallback assembled bayes opportunity inclusion timely certificate rawCertificate
      parameter utility excludedPayoff payoffBound nonnegative recoveryCertificate menuCertificate
      completes payoffBounded excludedBounded slots_pos readoutBounded globalUpper above below
  obtain ⟨valueError, valueLimit, comparisonValues⟩ := recovery_local_value_comparison_bounds setup
    leaks bounds horizon scheduler wellFormed independent sequence sourceMixed scale positive le_one
    scaleEq covers coversInputs capacity weights assessments fallback assembled bayes opportunity
    inclusion timely certificate rawCertificate parameter utility excludedPayoff payoffBound
    nonnegative recoveryCertificate menuCertificate completes payoffBounded excludedBounded
  obtain ⟨nativeError, nativeLimit, nativeCommitments⟩ :=
    nativeComparison_keyed_commitment_comparisons setup leaks bounds horizon scheduler wellFormed
      independent covers coversInputs capacity slots_pos sequence sourceMixed sourceBayes scale
      positive le_one scaleEq weights opportunity inclusion timely completes parameter utility
      excludedPayoff nonnegative readoutBounded excludedBounded
  obtain ⟨irregularError, irregularLimit, irregular⟩ := nativeComparison_irregular_bounds setup
    leaks
    bounds horizon scheduler wellFormed independent sequence sourceMixed scale positive le_one
    scaleEq covers coversInputs capacity weights
  have scaleLimit : Tendsto scale atTop (nhds 0) := by
    have identity : scale = fun n => trembleScale
        (combinedFloor setup leaks bounds horizon NativeScheduler (sequence n))
        (2 * horizon + 2) n := funext scaleEq
    rw [identity]
    exact tendsto_trembleScale _
      (fun n => combinedFloor_pos setup leaks bounds horizon NativeScheduler (sequence n))
      (fun n => combinedFloor_le_one setup leaks bounds horizon NativeScheduler (sequence n))
  let error := fun n => |nativeError n| + |memberError n| + 2 * |valueError n| +
    |affineError n| + 2 * payoffBound * |irregularError n| + 6 * scale n * payoffBound
  have errorLimit : Tendsto error atTop (nhds 0) := by
    simpa only [error, abs_zero, zero_mul, mul_zero, add_zero, zero_add] using
      (((((nativeLimit.abs.add memberLimit.abs).add (valueLimit.abs.const_mul 2)).add
        affineLimit.abs).add (irregularLimit.abs.const_mul (2 * payoffBound))).add
          ((scaleLimit.const_mul 6).mul_const payoffBound))
  refine ⟨error, errorLimit, ?_⟩
  intro n who site notFree notOwing keyed choice
  have positiveTerms : 0 ≤ 2 * payoffBound * |irregularError n| ∧
      0 ≤ 6 * scale n * payoffBound := by
    have := (positive n).le
    constructor <;> positivity
  obtain ⟨projectedPast, projectedView, event, atProjected, pendingProjected, _activated⟩ := keyed.1
  have someInput : ∃ past view, site.1 = some (past, view) := by
    cases current : site.1 with
    | none => simp [RecoveryProjection.information, current] at atProjected
    | some input => exact ⟨input.1, input.2, rfl⟩
  obtain ⟨past, view, atSite⟩ := someInput
  have pendingAt : pendingEvent setup leaks who
      (some (past.map (playerEntry (runtime setup) leaks), playerView (runtime setup) leaks view)) =
        some event := by
    change pendingEvent setup leaks who
      (RecoveryProjection.information (runtime setup) leaks site.1) = some event at pendingProjected
    simpa only [RecoveryProjection.information, atSite, Option.map_some] using pendingProjected
  have turn := (pendingEvent_spec (setup := setup) pendingAt).1
  obtain ⟨nativeSite, project, lifted, input, nativeNotFree, nativeNotOwing, _states, _belief,
    values⟩ := comparisonValues n who site notFree notOwing atSite turn
  have nativeKeyed : ownedKeyed (Vegas.FreeAgent setup leaks bounds horizon NativeScheduler)
      (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon NativeScheduler)
      ((N).agentAt nativeSite) := by
    refine ⟨?_, nativeNotFree⟩
    change LateDelivery setup leaks who nativeSite.1
    rw [input]
    exact keyed.1
  obtain ⟨nativePast, nativeView, nativeEvent, nativeAt, nativePending, _old⟩ := nativeKeyed.1
  rcases site with ⟨information, decision⟩
  dsimp only at lifted
  cases lifted
  let site : (R).InformationSite who :=
    ⟨liftInformation (runtime setup) leaks nativeSite.1, decision⟩
  let equivalent := sourceNativeChoiceEquiv setup leaks bounds horizon scheduler who nativeSite.1
  let nativeChoice := equivalent choice
  let target := nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
    positive
    le_one weights n
  let common := target.strategy
  let stopped := fun final : (NP).History => ¬ ClearState final.state ∨
    DecodedState setup leaks (failureProfile setup.program)
      (ProtocolState.OwesFailure who setup.program) final.state
  let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
    exclusionBase setup parameter utility excludedPayoff leaks final.state who
  let nativeValue := fun law => expect (target.belief who nativeSite) (fun history =>
    expect ((N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) common who
        ((common who).withLaw nativeSite.1 law)) stopped history.1) payoff)
  let actualValue := fun law => localValue (2 * horizon + 1) (fun final => final.state)
    (recoveryExclusionBase parameter utility excludedPayoff) (assessments n) site law
  let actualOption := fun option : LateOption bounds.candidateCount => keyedComponent setup
    leaks bounds Initial horizon scheduler
    (sequence n) (scale n) (positive n).le (le_one n) ((R).agentAt site) option
  let nativeOption := fun option : LateOption bounds.candidateCount => onePacketLate setup leaks
    bounds horizon NativeScheduler
    sequence
    scale positive le_one n ((N).agentAt nativeSite) option
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
    change |actualValue (actualOption option) - nativeValue
      (((actualOption option).map id).map equivalent)| ≤ valueError n at near
    rw [PMF.map_id] at near
    have same : (actualOption option).map equivalent = nativeOption option :=
      keyedComponent_sourceNative setup leaks bounds horizon scheduler (sequence n) (scale n)
        (positive n).le (le_one n) who nativeSite.1 decision option
    rwa [same] at near
  have memberAt : ∀ option,
      localGain (2 * horizon + 1) (fun final => final.state)
        (recoveryExclusionBase parameter utility excludedPayoff) (assessments n) site
        (actualOption option) ≤ memberError n := by
    intro option
    exact keyedComponent_gain_le_of_member_mixtures setup leaks bounds horizon scheduler parameter
      utility excludedPayoff (assessments n) (sequence n) (scale n) (positive n).le (le_one n) site
      keyed (members n who site) option
  have viaNative : ∀ option,
      localGain (2 * horizon + 1) (fun final => final.state)
          (recoveryExclusionBase parameter utility excludedPayoff) (assessments n) site
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
      lateChoice setup leaks bounds (initialLaw setup) horizon NativeScheduler (sequence n) who
        nativeSite.1 option = PMF.pure nativeChoice →
      localGain (2 * horizon + 1) (fun final => final.state)
          (recoveryExclusionBase parameter utility excludedPayoff) (assessments n) site
          (PMF.pure choice) ≤ 6 * scale n * payoffBound + memberError n := by
    intro option main
    have near := keyed_main_value_sub_le setup leaks bounds horizon scheduler (sequence n) (scale n)
      (positive n).le (le_one n) who nativeSite.1 decision option nativeChoice main (assessments n)
      (fun final => final.state) (recoveryExclusionBase parameter utility excludedPayoff)
      (payoffBounded who)
    change |actualValue (PMF.pure (equivalent.symm nativeChoice)) -
      actualValue (actualOption option)| ≤ 6 * scale n * payoffBound at near
    have same : equivalent.symm nativeChoice = choice := equivalent.symm_apply_apply choice
    rw [same] at near
    have member := memberAt option
    rw [localGain_eq_sub] at member ⊢
    change actualValue (actualOption option) - _ ≤ _ at member
    change actualValue (PMF.pure choice) - _ ≤ _
    linarith [(abs_le.mp near).2]
  by_cases intendedChoice : IntendedCommitment setup leaks bounds horizon NativeScheduler nativeSite
      nativeChoice
  · have metadata := intendedChoice
    obtain ⟨p, v, response, material, named, serial, payload, outputEq, value, atNative, selected,
      sends, packet, _after, _offered⟩ := metadata
    have submitted : (runtime setup).submittedEvent? leaks response = some named := by
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
    let mixture := mix success successNonneg successLe (PMF.pure deviation) (PMF.pure baseline)
    have zero : intendedSiteGain setup parameter utility excludedPayoff (sequence n) baseline = 0 :=
      by simp [intendedSiteGain, baseline, InformationModel.assessmentComparisonWith,
        InformationModel.assessmentLawWith, Profile.update_eq_self]
    have mixtureEq : expect mixture
        (intendedSiteGain setup parameter utility excludedPayoff (sequence n)) =
      success * intendedSiteGain setup parameter utility excludedPayoff (sequence n) deviation := by
      rw [expect_mix _ _ _ _ _ _ (payoffIntegrable_pure _ _) (payoffIntegrable_pure _ _),
        expect_pure, expect_pure, zero, mul_zero, add_zero]
    right
    refine ⟨mixture, ?_⟩
    rw [mixtureEq]
    have gain := viaNative option
    have covered : nativeError n + 2 * valueError n + memberError n ≤ error n := by
      dsimp only [error]
      linarith [le_abs_self (nativeError n), le_abs_self (valueError n), le_abs_self
        (memberError n),
        abs_nonneg (affineError n), positiveTerms.1, positiveTerms.2]
    linarith only [gain, bounded, covered]
  left
  obtain ⟨response, selected, member⟩ := choice_response setup leaks bounds horizon NativeScheduler
    nativeSite nativeAt nativeChoice
  have simpleCovered : 6 * scale n * payoffBound + memberError n ≤ error n := by
    dsimp only [error]
    linarith [abs_nonneg (nativeError n), abs_nonneg (valueError n), abs_nonneg (affineError n),
      positiveTerms.1, le_abs_self (memberError n)]
  cases sends : response.transmission with
  | none =>
      have silent : nativeChoice = silenceChoice setup leaks bounds (initialLaw setup) horizon
          NativeScheduler who nativeSite.1 := by
        apply Subtype.ext
        rw [selected, nativeAt]
        change some response = (silenceChoice setup leaks bounds (initialLaw setup) horizon
          NativeScheduler who (some (nativePast, nativeView))).1
        have responseEq : response = ⟨none⟩ :=
          congrArg (fun transmission => (⟨transmission⟩ : (application setup leaks).Action)) sends
        rw [responseEq]
        simp only [silenceChoice, responseChoice]
        split <;> rfl
      have main : lateChoice setup leaks bounds (initialLaw setup) horizon NativeScheduler
          (sequence n) who nativeSite.1 (none : LateOption bounds.candidateCount) =
            PMF.pure nativeChoice := by
        rw [silent, nativeAt, lateChoice_none]
      exact (viaMain none main).trans simpleCovered
  | some material =>
      obtain ⟨named, submitted⟩ := submittedEvent_of_transmits setup leaks bounds member sends
      have atTurn := commitsAtTurn_of_notOwing wellFormed nativeSite nativeNotOwing nativeChoice
        selected submitted
      cases packet : material.call.packet with
      | malformed raw => exact (onePacket_not_malformed bounds member sends raw packet).elim
      | commitment named candidate =>
          let nativeBelief := target.belief who nativeSite
          have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon NativeScheduler
            nativeNotOwing
          have forced := forcedAgent_of_not_free setup leaks bounds horizon NativeScheduler
            nativeNotFree
          have unforcedMass : expect nativeBelief (fun history =>
              if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤
                |irregularError n| := by
            have rows : ∀ history ∈ nativeBelief.support,
                (if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤
                if RegularTrace setup leaks bounds horizon NativeScheduler (sequence n) who
                    history.1.trace then 0 else 1 := by
              intro history _supported
              by_cases regular : RegularTrace setup leaks bounds horizon NativeScheduler
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
          have bad := recovery_unintendedCommitment_value_sub_le setup leaks bounds horizon
            scheduler
            wellFormed completes target nativeSite nativeChoice nativeNotOwing atTurn intendedChoice
            nativeAt response selected material sends named candidate packet parameter utility
            excludedPayoff (readoutBounded who) (excludedBounded who) unforcedMass
          change |nativeValue (PMF.pure nativeChoice) - excludedPayoff who| ≤
            2 * payoffBound * |irregularError n| at bad
          obtain ⟨lower, affine⟩ := affineValues n ((R).agentAt site) keyed notOwing decision
          have productNonneg := mul_nonneg
            (scoreUnit n (agentKey setup leaks bounds Initial horizon scheduler ((R).agentAt site))
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
          have packetSubmitted : (runtime setup).submittedEvent? leaks response = some named := by
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
          have main := lateChoice_eq_pure_opening setup leaks bounds horizon scheduler wellFormed
            (sequence n) nativeSite nativeNotFree
            (siteDebtFree_of_not_owing setup leaks bounds horizon NativeScheduler nativeNotOwing)
            nativeAt nativePending nativeChoice selected member sends packet
            (⟨0, slots_pos⟩ : Fin bounds.candidateCount)
          exact (viaMain (some ⟨0, slots_pos⟩) main).trans simpleCovered

end Vegas.RecoveryOnePacket
