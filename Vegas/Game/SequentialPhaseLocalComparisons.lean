/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseNonLateComparisons
import Vegas.Game.SequentialPhaseKeyedComparisons
import Vegas.Game.SequentialPhaseOwingGain
import GameTheoryExtensions.Analysis.Protocol.GainComparison

/-! # All local comparisons of the common singleton phase completion -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication (runtime setup) leaks).Scheduler)
  [(phaseApplication (runtime setup) leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]

variable {Public : Type*} {signal : State L setup.context → Public}

local notation "oldLeaks" => recoveryLeaks setup leaks
local notation "Initial" => recoveryInitialLaw setup
local notation "oldScheduler" => recoveryScheduler setup leaks scheduler
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler (runtime setup) (oldLeaks)
  (oldScheduler)
local notation "M" => model setup leaks bounds horizon scheduler
local notation "MMenu" => menu setup leaks bounds
local notation "MP" => ReactiveApplication.ResponseMenu.protocol (MMenu) (initialLaw setup)
  horizon scheduler
local notation "NMenu" => bounds.onePacketMenu (runtime setup) (oldLeaks)
local notation "Base" => phaseExclusionBase setup EventGraph.ExecutionMode.sequential
  (runtime setup) leaks

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq

private local instance localComparisonNativeNature :
    (application setup (oldLeaks)).FiniteNature (Vegas.initialLaw setup) (NativeScheduler) :=
  nativeNature setup leaks scheduler

private local instance localComparisonNativeInformation (who : Player) : DecidableEq
    ((onePacketModel setup (oldLeaks) bounds (Vegas.initialLaw setup) horizon
      (NativeScheduler)).InfoState who) :=
  nativeInfoDecidableEq setup leaks bounds horizon scheduler who

open Classical in
/-- The original phase completion compares every pure nonfree deviation with
exclusion or a lottery of gains in the fixed intended game. -/
theorem local_comparisons
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup (oldLeaks) bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slots_pos : 0 < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds horizon scheduler bounds.candidateCount p))
    (assessments : ℕ → (M).BehavioralAssessment)
    (fallback : ℕ → ∀ player, (M).Policy player)
    (assembled : ∀ n, (assessments n).strategy = componentStrategy setup leaks bounds horizon
      scheduler (fallback n) (sequence n) (scale n) (positive n).le (le_one n) (weights n))
    (mixed : ∀ n, (assessments n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (M) (assessments n)
      ((MMenu).decisionInformationAntichain (initialLaw setup) horizon scheduler))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : PhaseService.Opportunity (runtime setup) leaks (initialLaw setup) horizon
        scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion (runtime setup) leaks (initialLaw setup) horizon
        scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (payoffBound : ℝ) (nonnegative : 0 ≤ payoffBound)
    (completes : PhaseService.CompletesPlay (runtime setup) leaks (initialLaw setup) horizon
        scheduler)
    (payoffBounded : ∀ who (final : (MP).History),
      |(Base (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
          final.state who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (upper : Player → ℝ) (le_upper : ∀ outcome who, utility outcome who ≤ upper who)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (pooled : ∀ n (alternative : ∀ p,
        PMF (Part setup leaks bounds horizon scheduler bounds.candidateCount p)) p,
      ∑ agent ∈ Finset.univ.filter
          (fun agent => pool setup leaks bounds horizon scheduler agent = p),
        (if decision : (M).IsDecisionInfo agent.1 agent.2.1 then
          ((assessments n).continuationContext
              ((MMenu).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
              ⟨agent.2.1, decision⟩
              (fun final => (Base (fun terminal => utility (setup.parameterOutcome parameter
                  terminal)) excludedPayoff) final.state
                agent.1)).value
              (((assessments n).strategy agent.1).withLaw agent.2.1
                ((alternative (pool setup leaks bounds horizon scheduler
                    agent)).bind
                  (component setup leaks bounds horizon scheduler (sequence n)
                      (scale n)
                    (positive n).le (le_one n) agent))) -
            ((assessments n).continuationContext
              ((MMenu).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
              ⟨agent.2.1, decision⟩
              (fun final => (Base (fun terminal => utility (setup.parameterOutcome parameter
                  terminal)) excludedPayoff) final.state
                agent.1)).value ((assessments n).strategy agent.1)
        else 0) ≤ 0) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (M).InformationSite who),
        ¬ FreeAgent setup leaks bounds horizon scheduler ((M).agentAt site) →
        ∀ choice : (M).Choice who site.1,
          localGain (2 * horizon + 1) (fun final => final.state)
              ((Base (fun terminal => utility (setup.parameterOutcome parameter terminal))
                  excludedPayoff)) (assessments n) site
              (PMF.pure choice) ≤ error n ∨
          ∃ mixture : PMF (setup.intendedModel.AssessmentDeviation who),
            localGain (2 * horizon + 1) (fun final => final.state)
                ((Base (fun terminal => utility (setup.parameterOutcome parameter terminal))
                    excludedPayoff)) (assessments n) site
                (PMF.pure choice) ≤
              expect mixture (intendedSiteGain setup parameter utility excludedPayoff (sequence
                n)) +
                error n := by
  classical
  let rawCertificate := ((application setup (oldLeaks)).bounded
    ((Initial).map RecoveryState.native) horizon (NativeScheduler)).wellFoundedHistories
  let certificate := ((NMenu).bounded (Vegas.initialLaw setup) horizon
    (NativeScheduler)).wellFoundedHistories
  have gainEq (n : ℕ) (who : Player) (site : (M).InformationSite who)
      (law : PMF ((M).Choice who site.1)) :
      localGain (2 * horizon + 1) (fun final => final.state)
        (Base (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
        (assessments n) site law =
      ((assessments n).continuationContext
        ((MMenu).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories site
        (fun final => Base (fun terminal => utility (setup.parameterOutcome parameter terminal))
          excludedPayoff final.state who)).value
        (((assessments n).strategy who).withLaw site.1 law) -
      ((assessments n).continuationContext
        ((MMenu).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories site
        (fun final => Base (fun terminal => utility (setup.parameterOutcome parameter terminal))
          excludedPayoff final.state who)).value ((assessments n).strategy who) := by
    rw [localGain_eq_sub,
      localValue_eq_continuationContext (2 * horizon + 1) (fun final => final.state)
        (Base (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
        (assessments n) site ((MMenu).bounded (initialLaw setup) horizon scheduler),
      localValue_eq_continuationContext (2 * horizon + 1) (fun final => final.state)
        (Base (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
        (assessments n) site ((MMenu).bounded (initialLaw setup) horizon scheduler),
      BehavioralPolicy.withLaw_eq_self]
  have pooledGains (n : ℕ) (alternative : ∀ p,
      PMF (Part setup leaks bounds horizon scheduler bounds.candidateCount p)) (p) :
      ∑ agent ∈ Finset.univ.filter
        (fun agent => pool setup leaks bounds horizon scheduler agent = p),
        (if decision : (M).IsDecisionInfo agent.1 agent.2.1 then
          localGain (2 * horizon + 1) (fun final => final.state)
            (Base (fun terminal => utility (setup.parameterOutcome parameter terminal))
              excludedPayoff) (assessments n) (who := agent.1) ⟨agent.2.1, decision⟩
            ((alternative (pool setup leaks bounds horizon scheduler agent)).bind
              (component setup leaks bounds horizon scheduler (sequence n) (scale n)
                (positive n).le (le_one n) agent)) else 0) ≤ 0 := by
    simpa only [gainEq] using pooled n alternative p
  obtain ⟨nonlateError, nonlateLimit, nonlateBound⟩ := nonlate_local_comparisons setup leaks bounds
    horizon scheduler wellFormed independent observable sequence sourceMixed sourceBayes scale
    positive le_one scaleEq covers coversInputs capacity weights opportunity inclusion timely
    rawCertificate completes assessments fallback assembled mixed bayes parameter utility
    excludedPayoff nonnegative (fun final who => payoffBounded who final) excludedBounded below
    upper le_upper readoutBounded
  obtain ⟨keyedError, keyedLimit, keyedBound⟩ := keyed_local_comparisons setup leaks bounds horizon
    scheduler wellFormed independent observable sequence sourceMixed sourceBayes scale positive
    le_one scaleEq covers coversInputs capacity weights opportunity inclusion timely rawCertificate
    certificate completes assessments fallback assembled mixed bayes parameter utility
        excludedPayoff
    nonnegative (fun final who => payoffBounded who final) excludedBounded slots_pos readoutBounded
    upper le_upper below pooledGains
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
  obtain ⟨clear, _forced⟩ := Classical.not_not.mp notFree
  by_cases owing : RecoveryOnePacket.OwingAgent setup (oldLeaks) bounds Initial horizon
      (oldScheduler) (projectedAgent setup leaks bounds horizon scheduler ((M).agentAt site) clear)
  · left
    have actualPositive : 0 < (M).informationMass (assessments n).strategy who site :=
      (M).informationMass_pos_of_fullSupport _ (mixed n) who site
    have positiveSite : 0 < (M).informationMass
        (componentStrategy setup leaks bounds horizon scheduler (fallback n) (sequence n) (scale n)
          (positive n).le (le_one n) (weights n)) who site := by
      rw [← assembled n]
      exact actualPositive
    rw [component_owing_localGain_eq_zero setup leaks bounds horizon scheduler (fallback n)
      (sequence n) (scale n) (positive n) (le_one n) (weights n) who site clear positiveSite owing
      (assessments n) (assembled n) (bayes n) parameter utility excludedPayoff completes]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases keyed : ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
      (KeyedAgent setup leaks bounds horizon scheduler) ((M).agentAt site)
  · exact GainComparison.sum_abs_errors (fun index => errors index n) true
      (keyedBound n who site clear keyed owing choice)
  · exact GainComparison.sum_abs_errors (fun index => errors index n) false
      (nonlateBound n who site clear notFree owing keyed choice)

end Vegas.SequentialPhase
