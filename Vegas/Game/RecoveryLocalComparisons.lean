/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryNonLateComparisons
import Vegas.Game.RecoveryKeyedComparisons
import GameTheoryExtensions.Analysis.Protocol.GainComparison

/-! # All local comparisons under the original recovery completion -/

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
theorem recovery_local_comparisons [Fintype (RP).History]
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
  let rawCertificate := ((application setup leaks).bounded ((Initial).map RecoveryState.native)
    horizon NativeScheduler).wellFoundedHistories
  let recoveryCertificate := ((RApp).bounded Initial horizon scheduler).wellFoundedHistories
  let menuCertificate := ((RMenu).bounded Initial horizon scheduler).wellFoundedHistories
  obtain ⟨nonlateError, nonlateLimit, nonlateBound⟩ := recovery_nonlate_local_comparisons setup
    leaks
    bounds horizon scheduler wellFormed independent sequence sourceMixed sourceBayes scale positive
    le_one scaleEq covers coversInputs capacity weights assessments fallback assembled bayes
    opportunity inclusion timely rawCertificate parameter utility excludedPayoff payoffBound
    nonnegative recoveryCertificate menuCertificate completes payoffBounded excludedBounded below
    upper le_upper readoutBounded
  obtain ⟨keyedError, keyedLimit, keyedBound⟩ := recovery_keyed_local_comparisons setup leaks bounds
    horizon scheduler wellFormed independent sequence sourceMixed sourceBayes scale positive le_one
    scaleEq covers coversInputs capacity slots_pos weights assessments fallback assembled bayes
    opportunity inclusion timely parameter utility excludedPayoff payoffBound nonnegative completes
    payoffBounded excludedBounded below upper le_upper readoutBounded pooled
  let errors : Bool → ℕ → ℝ := fun keyed => if keyed then keyedError else nonlateError
  let error := fun n => ∑ index, |errors index n|
  refine ⟨error, ?_, ?_⟩
  · have limits : ∀ index, Tendsto (fun n => |errors index n|) atTop (nhds 0) := by
      intro index
      cases index with
      | false => simpa [errors] using nonlateLimit.abs
      | true => simpa [errors] using keyedLimit.abs
    simpa only [error, Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun index _ => limits index)
  intro n who site notFree choice
  by_cases owing : OwingAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site)
  · left
    rw [owingAgent_localGain_eq_zero setup leaks bounds horizon scheduler parameter utility
      excludedPayoff completes (assessments n) site owing]
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  by_cases keyed : ownedKeyed (FreeAgent setup leaks bounds Initial horizon scheduler)
      (KeyedAgent setup leaks bounds Initial horizon scheduler) ((R).agentAt site)
  · exact GainComparison.sum_abs_errors (fun index => errors index n) true
      (keyedBound n who site notFree owing keyed choice)
  · exact GainComparison.sum_abs_errors (fun index => errors index n) false
      (nonlateBound n who site notFree owing keyed choice)

end Vegas.RecoveryOnePacket
