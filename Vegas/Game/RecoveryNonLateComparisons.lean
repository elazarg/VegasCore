/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryNonLateNativeComparisons
import Vegas.Game.RecoveryUnpendingChoices
import Vegas.Game.RecoveryLocalValueComparison

/-! # Local recovery values under the same comparison posterior -/

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

variable {Public : Type*} {signal : State L setup.context → Public}

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
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native
    ∅))
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks

local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)

open Classical in
/-- Every pure nonlate actual recovery deviation is bounded by vanishing error
or a mixture of deviations in the original intended game, under the same witness. -/
theorem recovery_nonlate_local_comparisons [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [(recoveryApplication (runtime setup) leaks).FiniteNature Initial scheduler]
    [Finite setup.intendedProtocol.History]
    [∀ player, DecidableEq ((R).InfoState player)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
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
    (rawCertificate : (RawNative).WellFoundedHistories)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (payoffBound : ℝ) (nonnegative : 0 ≤ payoffBound)
    (recoveryCertificate : ((recoveryApplication (runtime setup) leaks).protocol Initial horizon
      scheduler).WellFoundedHistories)
    (menuCertificate : (RP).WellFoundedHistories)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    (payoffBounded : ∀ who (final : (RP).History),
      |recoveryExclusionBase parameter utility excludedPayoff final.state who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (upper : Player → ℝ) (le_upper : ∀ outcome who, utility outcome who ≤ upper who)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (R).InformationSite who),
        ¬ FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ¬ OwingAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ¬ ownedKeyed (FreeAgent setup leaks bounds Initial horizon scheduler)
          (KeyedAgent setup leaks bounds Initial horizon scheduler) ((R).agentAt site) →
        ∀ choice : (R).Choice who site.1,
          localGain (2 * horizon + 1) (fun final => final.state)
              (recoveryExclusionBase parameter utility excludedPayoff) (assessments n) site
              (PMF.pure choice) ≤ error n ∨
          ∃ mixture : PMF (setup.intendedModel.AssessmentDeviation who),
            localGain (2 * horizon + 1) (fun final => final.state)
                (recoveryExclusionBase parameter utility excludedPayoff) (assessments n) site
                (PMF.pure choice) ≤
              expect mixture
                (intendedSiteGain setup parameter utility excludedPayoff (sequence n)) +
                error n := by
  classical
  let certificate := ((NMenu).bounded (initialLaw setup) horizon
    (NativeScheduler)).wellFoundedHistories
  obtain ⟨nativeError, nativeLimit, nativeComparisons⟩ :=
    nativeComparison_nonlate_pending_comparisons setup leaks bounds horizon scheduler wellFormed
      independent observable covers coversInputs capacity sequence sourceMixed sourceBayes scale
      positive
      le_one
      scaleEq weights opportunity inclusion timely completes parameter utility excludedPayoff below
      upper le_upper nonnegative readoutBounded excludedBounded
  obtain ⟨valueError, valueLimit, comparisonValues⟩ := recovery_local_value_comparison_bounds setup
    leaks bounds horizon scheduler wellFormed independent observable sequence sourceMixed scale
    positive le_one
    scaleEq covers coversInputs capacity weights assessments fallback assembled bayes opportunity
    inclusion timely certificate rawCertificate parameter utility excludedPayoff payoffBound
    nonnegative recoveryCertificate menuCertificate completes payoffBounded excludedBounded
  let error := fun n => |nativeError n| + 2 * |valueError n|
  have limit : Tendsto error atTop (nhds 0) := by
    simpa only [abs_zero, zero_mul, mul_zero, add_zero] using
      nativeLimit.abs.add (valueLimit.abs.const_mul 2)
  refine ⟨error, limit, ?_⟩
  intro n who site notFree notOwing notKeyed choice
  have nonlate : ¬ KeyedAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) :=
    fun late => notKeyed ⟨late, notFree⟩
  obtain ⟨past, view, atSite⟩ : ∃ past view, site.1 = some (past, view) := by
    obtain ⟨history, _running, _choice, _legal⟩ := site.2
    have active := InformationSite.active (R) site history
    obtain ⟨control, state, actor⟩ := (RApp).control_of_active Initial horizon scheduler
      ((RMenu).toRawHistory Initial horizon scheduler history.1) who active
    change history.1.state = some control at state
    have observed := ((RMenu).info Initial horizon scheduler who history.1.trace).symm.trans
      history.2
    rw [state] at observed
    simp only [ReactiveApplication.observe, actor, ↓reduceIte] at observed
    exact ⟨control.execution.recall who, control.execution.observe (RApp) who, observed.symm⟩
  cases pending : pendingEvent setup leaks who
      (RecoveryProjection.information (runtime setup) leaks site.1) with
  | none =>
      left
      rw [localGain]
      have zero := withLaw_eq_self_of_unpending_notOwing setup leaks bounds horizon scheduler
        wellFormed site notFree notOwing nonlate atSite pending ((assessments n).strategy who)
        (PMF.pure choice)
      rw [zero]
      simp only [assessmentComparisonWith, sub_self]
      dsimp only [error]
      positivity
  | some event =>
      have pendingAt := pending
      rw [atSite] at pendingAt
      have turn : view.application.1.publicView.ownTurn? who = some event :=
        (pendingEvent_spec pendingAt).1
      obtain ⟨nativeSite, project, lifted, input, nativeNotFree, nativeNotOwing, _states, _belief,
        values⟩ := comparisonValues n who site notFree notOwing atSite turn
      have nativeNonlate : ¬ LateDelivery setup leaks who nativeSite.1 := by
        rw [input]
        exact nonlate
      have nativePending : pendingEvent setup leaks who nativeSite.1 = some event := by
        rw [input]
        exact pending
      rcases site with ⟨input, decision⟩
      dsimp only at lifted
      cases lifted
      let equivalent := sourceNativeChoiceEquiv setup leaks bounds horizon scheduler who
        nativeSite.1
      let nativeChoice := equivalent choice
      let common := nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
        positive le_one weights n
      let stopped := fun final : (NP).History => ¬ ClearState final.state ∨
        DecodedState setup leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure who setup.program) final.state
      let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
        exclusionBase setup parameter utility excludedPayoff leaks final.state who
      let nativeValue := fun law => expect
        ((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive
          le_one weights n).belief who nativeSite) (fun history =>
            expect ((N).runBehavioralUntil certificate
              (Profile.update (sig := (N).behavioralSignature) common who
                ((common who).withLaw nativeSite.1 law)) stopped history.1) payoff)
      have sourceLaw : (((assessments n).strategy who
          (liftInformation (runtime setup) leaks nativeSite.1)).map equivalent) =
          common who nativeSite.1 := by
        apply pmf_map_injective Subtype.val_injective
        rw [sourceNativeChoiceEquiv_map_val]
        exact (nativeComparisonStrategy_at_clear setup leaks bounds horizon scheduler sequence scale
          positive le_one weights n (fallback n) (assessments n).strategy (assembled n) nativeSite
          decision).symm
      have pureValue := values (PMF.pure choice)
      have baselineValue := values ((assessments n).strategy who
        (liftInformation (runtime setup) leaks nativeSite.1))
      dsimp only at pureValue baselineValue
      simp only [PMF.pure_map] at pureValue
      change |localValue (2 * horizon + 1) (fun final => final.state)
          (recoveryExclusionBase parameter utility excludedPayoff) (assessments n) _
          ((assessments n).strategy who _) - nativeValue
          ((((assessments n).strategy who _).map id).map equivalent)| ≤ valueError n
        at baselineValue
      rw [PMF.map_id, sourceLaw] at baselineValue
      change |localValue (2 * horizon + 1) (fun final => final.state)
          (recoveryExclusionBase parameter utility excludedPayoff) (assessments n) _
          (PMF.pure choice) - nativeValue (PMF.pure nativeChoice)| ≤ valueError n at pureValue
      change |localValue (2 * horizon + 1) (fun final => final.state)
          (recoveryExclusionBase parameter utility excludedPayoff) (assessments n) _
          ((assessments n).strategy who _) - nativeValue (common who nativeSite.1)| ≤
          valueError n at baselineValue
      have same : nativeValue (common who nativeSite.1) =
          expect ((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
            positive le_one weights n).belief who nativeSite) (fun history =>
              expect ((N).runBehavioralUntil certificate common stopped history.1) payoff) := by
        simp only [nativeValue, BehavioralPolicy.withLaw_eq_self, Profile.update_eq_self]
      let nativeGain := nativeValue (PMF.pure nativeChoice) - nativeValue (common who nativeSite.1)
      have gainBound : localGain (2 * horizon + 1) (fun final => final.state)
          (recoveryExclusionBase parameter utility excludedPayoff) (assessments n) _
          (PMF.pure choice) ≤ nativeGain + 2 * valueError n := by
        rw [localGain_eq_sub]
        dsimp only [nativeGain]
        linarith [(abs_le.mp pureValue).2, (abs_le.mp baselineValue).1]
      have compared := nativeComparisons n who nativeSite nativeChoice nativeNotFree nativeNotOwing
        nativeNonlate nativePending
      dsimp only at compared
      have nativeGainEq : nativeGain = expect
          ((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive
            le_one weights n).belief who nativeSite) (fun history =>
              expect ((N).runBehavioralUntil certificate
                (Profile.update (sig := (N).behavioralSignature) common who
                  ((common who).withLaw nativeSite.1 (PMF.pure nativeChoice))) stopped history.1)
                payoff -
              expect ((N).runBehavioralUntil certificate common stopped history.1) payoff) := by
        rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
        exact congrArg (fun base => nativeValue (PMF.pure nativeChoice) - base) same
      rw [← nativeGainEq] at compared
      have errorCovers : nativeError n + 2 * valueError n ≤ error n := by
        dsimp only [error]
        linarith [le_abs_self (nativeError n), le_abs_self (valueError n)]
      rcases compared with bounded | ⟨sourceDeviation, bounded⟩
      · left
        linarith only [gainBound, bounded, errorCovers]
      · right
        refine ⟨PMF.pure sourceDeviation, ?_⟩
        rw [expect_pure]
        linarith

end Vegas.RecoveryOnePacket
