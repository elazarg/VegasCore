/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseKeyedComponentValues
import Vegas.Game.SequentialPhaseOwingGain
import GameTheoryExtensions.Analysis.Protocol.AffineKeyedPools

/-! # Pooled keyed gains in the original phase game -/

noncomputable section

namespace Vegas.SequentialPhase

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (Vegas.graph setup))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  [(phaseApplication runtime leaks).FiniteNature (phaseInitialLaw setup) scheduler]

local notation "RecoveryLeaks" => recoveryLeaks setup leaks
local notation "RecoveryPrior" => recoveryInitialLaw setup
local notation "RecoveryScheduler" => recoveryScheduler setup runtime leaks scheduler
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler runtime
    (RecoveryLeaks)
  (RecoveryScheduler)
local notation "R" => recoveryModel setup runtime leaks bounds horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu runtime (RecoveryLeaks) bounds
local notation "NMenu" => bounds.onePacketMenu runtime (RecoveryLeaks)
local notation "N" => onePacketModel (runtime := runtime) setup (RecoveryLeaks) bounds
  (Vegas.initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol (RMenu) RecoveryPrior horizon
  (RecoveryScheduler)
local notation "NP" => onePacketProtocol (runtime := runtime) setup (RecoveryLeaks) bounds horizon
  (NativeScheduler)
local notation "RawNative" => ReactiveApplication.protocol (application (runtime := runtime) setup
  (RecoveryLeaks))
  (PMF.map RecoveryState.native (RecoveryPrior)) horizon (NativeScheduler)
local notation "Clear" => ReactiveApplication.stateInvariant (app := application (runtime :=
  runtime) setup
    (RecoveryLeaks))
  (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

local notation "P" => phaseApplication runtime leaks
local notation "M" => model setup runtime leaks bounds horizon scheduler
local notation "projectInfo" => PhaseRecoveryProjection.information runtime leaks
    (RecoveryLeaks)

attribute [local instance] phaseInfoDecidableEq recoveryInfoDecidableEq nativeInfoDecidableEq
  phaseHistoryFintype recoveryHistoryFintype nativeHistoryFintype nativeNature

open Classical in
private theorem component_mixture_gain_le_of_values
    (fallback : ∀ who, (M).Policy who)
    (source : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (weights : ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots p))
    (assessment : (M).BehavioralAssessment)
    (played : assessment.strategy = componentStrategy setup runtime leaks bounds horizon scheduler
      fallback
      source scale nonnegative le_one weights)
    (payoff : (P).ProtocolState → Player → ℝ)
    (pooled : ∀ (alternative : ∀ p, PMF (Part setup runtime leaks bounds horizon scheduler slots
      p)) p,
      ∑ agent ∈ Finset.univ.filter
        (fun agent => pool setup runtime leaks bounds horizon scheduler agent = p),
        (if decision : (M).IsDecisionInfo agent.1 agent.2.1 then
          localGain (2 * horizon + 1) (fun final => final.state) payoff assessment
            (who := agent.1) ⟨agent.2.1, decision⟩
            ((alternative (pool setup runtime leaks bounds horizon scheduler agent)).bind
              (component setup runtime leaks bounds horizon scheduler source scale nonnegative
                le_one
                agent))
          else 0) ≤ 0)
    (excluded : Player → ℝ)
    (noGain : ∀ who (site : (M).InformationSite who) (clear : ClearInput setup runtime leaks
      site.1),
      RecoveryOnePacket.OwingAgent (runtime := runtime) setup (RecoveryLeaks) bounds RecoveryPrior
        horizon
          (RecoveryScheduler)
        (projectedAgent setup runtime leaks bounds horizon scheduler ((M).agentAt site) clear) →
      ∀ law, localGain (2 * horizon + 1) (fun final => final.state) payoff assessment site law = 0)
    (continuation : (M).InformationAgent (M).playedInformation → ℝ)
    (score : Option (LateKey (runtime := runtime) setup (RecoveryLeaks)) → LateOption slots → ℝ)
      (error : ℝ)
    (values : ∀ agent : (M).InformationAgent (M).playedInformation,
      ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
        (KeyedAgent setup runtime leaks bounds horizon scheduler) agent →
      (∀ clear : ClearInput setup runtime leaks agent.2.1,
        ¬ RecoveryOnePacket.OwingAgent (runtime := runtime) setup (RecoveryLeaks) bounds
          RecoveryPrior horizon
            (RecoveryScheduler)
          (projectedAgent setup runtime leaks bounds horizon scheduler agent clear)) →
      ∀ decision : (M).IsDecisionInfo agent.1 agent.2.1,
        excluded agent.1 ≤ continuation agent ∧ ∀ option,
        |localValue (2 * horizon + 1) (fun final => final.state) payoff assessment
            (who := agent.1) ⟨agent.2.1, decision⟩
            (keyedComponent setup runtime leaks bounds horizon scheduler source scale nonnegative
              le_one
              agent option) -
          (excluded agent.1 + score (agentKey setup runtime leaks bounds horizon scheduler agent)
            option *
            (continuation agent - excluded agent.1))| ≤ error)
    (who : Player) (site : (M).InformationSite who)
    (keyed : ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
      (KeyedAgent setup runtime leaks bounds horizon scheduler) ((M).agentAt site))
    (alternative : PMF (Part setup runtime leaks bounds horizon scheduler slots
      (pool setup runtime leaks bounds horizon scheduler ((M).agentAt site)))) :
    localGain (2 * horizon + 1) (fun final => final.state) payoff assessment site
      (alternative.bind (component setup runtime leaks bounds horizon scheduler source scale
        nonnegative
        le_one ((M).agentAt site))) ≤
      Fintype.card ((M).InformationAgent (M).playedInformation) * (2 * max error 0) := by
  let indifferent := fun agent : (M).InformationAgent (M).playedInformation =>
    ∃ clear : ClearInput setup runtime leaks agent.2.1,
      RecoveryOnePacket.OwingAgent (runtime := runtime) setup (RecoveryLeaks) bounds RecoveryPrior
        horizon
          (RecoveryScheduler)
        (projectedAgent setup runtime leaks bounds horizon scheduler agent clear)
  have noGainAt : ∀ who (site : (M).InformationSite who),
      indifferent ((M).agentAt site) → ∀ law,
      localGain (2 * horizon + 1) (fun final => final.state) payoff assessment site law = 0 := by
    intro focal atSite owed law
    change (∃ clear : ClearInput setup runtime leaks atSite.1,
      RecoveryOnePacket.OwingAgent (runtime := runtime) setup (RecoveryLeaks) bounds RecoveryPrior
        horizon
          (RecoveryScheduler)
        (projectedAgent setup runtime leaks bounds horizon scheduler ((M).agentAt atSite) clear))
          at owed
    obtain ⟨clear, owing⟩ := owed
    exact noGain focal atSite clear owing law
  have componentValues (agent : (M).InformationAgent (M).playedInformation)
      (owned : ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
        (KeyedAgent setup runtime leaks bounds horizon scheduler) agent)
      (notOwing : ¬ indifferent agent)
      (decision : (M).IsDecisionInfo agent.1 agent.2.1) :
      excluded agent.1 ≤ continuation agent ∧ ∀ option,
        |localValue (2 * horizon + 1) (fun final => final.state) payoff assessment
            (who := agent.1) ⟨agent.2.1, decision⟩
            (keyedComponent setup runtime leaks bounds horizon scheduler source scale nonnegative
              le_one
              agent option) -
          (excluded agent.1 + score (agentKey setup runtime leaks bounds horizon scheduler agent)
            option *
            (continuation agent - excluded agent.1))| ≤ error := by
    exact values agent owned (fun clear owing => notOwing ⟨clear, owing⟩) decision
  exact @freeKeyed_memberGain_le_of_common_values Player inferInstance inferInstance
    ((menu setup runtime leaks bounds).protocol (phaseInitialLaw setup) horizon scheduler) M
    (fun who => phaseInfoDecidableEq setup runtime leaks bounds horizon scheduler who)
    (phaseHistoryFintype setup runtime leaks bounds horizon scheduler)
    (P).ProtocolState (Option (LateKey (runtime := runtime) setup (RecoveryLeaks))) (LateOption
      slots) inferInstance
    inferInstance (2 * horizon + 1)
    ((menu setup runtime leaks bounds).bounded (phaseInitialLaw setup) horizon scheduler)
    ((menu setup runtime leaks bounds).decisionRecall (phaseInitialLaw setup) horizon scheduler)
    (fun final => final.state) payoff fallback (FreeAgent setup runtime leaks bounds horizon
      scheduler)
    (KeyedAgent setup runtime leaks bounds horizon scheduler)
    (agentKey setup runtime leaks bounds horizon scheduler)
    indifferent (freeLaw setup runtime leaks bounds horizon scheduler scale nonnegative le_one)
    (prescribedComponent setup runtime leaks bounds horizon scheduler source scale nonnegative
      le_one)
    (keyedComponent setup runtime leaks bounds horizon scheduler source scale nonnegative le_one)
      weights
    assessment played (by
      intro alternative p
      have given := pooled alternative p
      simp only [component, pool, Part] at given
      convert given using 1
      congr 1
      ext agent
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]) excluded
    noGainAt continuation score error componentValues
    who site keyed alternative

variable {Public : Type*} {signal : State L setup.context → Public}

open Classical in
/-- Actual target pooled optimality controls each keyed component mixture.
Owed source debt is indifferent under arbitrary whole phase continuations. -/
theorem keyed_component_mixture_gain_bounds [Finite setup.intendedProtocol.History]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor (runtime := runtime) setup (RecoveryLeaks) bounds horizon (NativeScheduler)
        (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup runtime leaks bounds horizon scheduler bounds.candidateCount p))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : PhaseService.Opportunity runtime leaks (phaseInitialLaw setup) horizon
      scheduler delay)
    (inclusion : PhaseService.ProtectedInclusion runtime leaks (phaseInitialLaw setup)
      horizon scheduler bound)
    (timely : runtime.AsyncTimely delay bound)
    (rawCertificate : (RawNative).WellFoundedHistories)
    (certificate : (NP).WellFoundedHistories)
    (completes : PhaseService.CompletesPlay runtime leaks (phaseInitialLaw setup)
      horizon scheduler)
    (phaseAssessments : ℕ → (M).BehavioralAssessment)
    (fallback : ℕ → ∀ who, (M).Policy who)
    (assembled : ∀ n, (phaseAssessments n).strategy =
      componentStrategy setup runtime leaks bounds horizon scheduler (fallback n) (sequence n)
        (scale n)
        (positive n).le (le_one n) (weights n))
    (mixed : ∀ n, (phaseAssessments n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (M) (phaseAssessments n)
      ((menu setup runtime leaks bounds).decisionInformationAntichain (phaseInitialLaw setup)
        horizon
          scheduler))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (nonnegative : 0 ≤ payoffBound)
    (payoffBounded : ∀ history :
      ((menu setup runtime leaks bounds).protocol (phaseInitialLaw setup) horizon
        scheduler).History,
      ∀ who, |phaseExclusionBase setup .sequential runtime leaks
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
        PMF (Part setup runtime leaks bounds horizon scheduler bounds.candidateCount p)) p,
      ∑ agent ∈ Finset.univ.filter
        (fun agent => pool setup runtime leaks bounds horizon scheduler agent = p),
        (if decision : (M).IsDecisionInfo agent.1 agent.2.1 then
          localGain (2 * horizon + 1) (fun final => final.state)
            (phaseExclusionBase setup .sequential runtime leaks
              (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
            (phaseAssessments n) (who := agent.1) ⟨agent.2.1, decision⟩
            ((alternative (pool setup runtime leaks bounds horizon scheduler agent)).bind
              (component setup runtime leaks bounds horizon scheduler (sequence n) (scale n)
                (positive n).le (le_one n) agent)) else 0) ≤ 0) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (M).InformationSite who),
      ownedKeyed (FreeAgent setup runtime leaks bounds horizon scheduler)
        (KeyedAgent setup runtime leaks bounds horizon scheduler) ((M).agentAt site) →
      ∀ alternative : PMF (Part setup runtime leaks bounds horizon scheduler bounds.candidateCount
        (pool setup runtime leaks bounds horizon scheduler ((M).agentAt site))),
      localGain (2 * horizon + 1) (fun final => final.state)
        (phaseExclusionBase setup .sequential runtime leaks
          (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
        (phaseAssessments n) site
        (alternative.bind (component setup runtime leaks bounds horizon scheduler (sequence n)
          (scale n)
          (positive n).le (le_one n) ((M).agentAt site))) ≤ error n := by
  obtain ⟨continuationScore, valueError, valueLimit, _unit, values⟩ :=
    keyed_component_value_bounds setup runtime leaks bounds horizon scheduler wellFormed
    independent observable sequence sourceMixed
    scale positive le_one scaleEq covers coversInputs capacity weights opportunity inclusion timely
    rawCertificate certificate completes phaseAssessments fallback assembled mixed bayes parameter
    utility excludedPayoff nonnegative payoffBounded excludedBounded slots_pos readoutBounded upper
    le_upper below
  let continuation := fun n (agent : (M).InformationAgent (M).playedInformation) =>
    if decision : (N).IsDecisionInfo agent.1
        (RecoveryProjection.information runtime (RecoveryLeaks) (projectInfo agent.2.1))
            then
      siteValue (runtime := runtime) setup (RecoveryLeaks) bounds horizon (NativeScheduler)
        parameter utility
          excludedPayoff
        (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale
          positive
          le_one weights n) (setup.intendedOpeningProfile (sequence n).strategy)
        ⟨RecoveryProjection.information runtime (RecoveryLeaks) (projectInfo agent.2.1),
          decision⟩
    else excludedPayoff agent.1
  let count : ℝ := Fintype.card ((M).InformationAgent (M).playedInformation)
  refine ⟨fun n => count * (2 * max (valueError n) 0), ?_, ?_⟩
  · have limit : Tendsto (fun n => max (valueError n) 0) atTop (nhds 0) := by
      simpa using valueLimit.max (tendsto_const_nhds (x := (0 : ℝ)))
    simpa using (limit.const_mul 2).const_mul count
  intro n who site keyed alternative
  apply component_mixture_gain_le_of_values setup runtime leaks bounds horizon scheduler (fallback
    n)
    (sequence n) (scale n) (positive n).le (le_one n) (weights n) (phaseAssessments n) (assembled n)
    (phaseExclusionBase setup .sequential runtime leaks
      (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff)
    (pooled n) excludedPayoff ?_ (continuation n) (continuationScore n) (valueError n) ?_
    who site keyed alternative
  · intro focal atSite clear owing law
    have actualPositive : 0 < (M).informationMass (phaseAssessments n).strategy focal atSite :=
      (M).informationMass_pos_of_fullSupport _ (mixed n) focal atSite
    have positiveSite : 0 < (M).informationMass
        (componentStrategy setup runtime leaks bounds horizon scheduler (fallback n) (sequence n)
          (scale n)
          (positive n).le (le_one n) (weights n)) focal atSite := by
      rw [← assembled n]
      exact actualPositive
    exact component_owing_localGain_eq_zero setup runtime leaks bounds horizon scheduler (fallback
      n)
      (sequence n) (scale n) (positive n) (le_one n) (weights n) focal atSite clear positiveSite
      owing
      (phaseAssessments n) (assembled n) (bayes n) parameter utility excludedPayoff completes law
  · intro agent owned notOwing decision
    obtain ⟨clear, _forced⟩ := Classical.not_not.mp owned.2
    let atSite : (M).InformationSite agent.1 := ⟨agent.2.1, decision⟩
    have debtFree : ¬ RecoveryOnePacket.OwingAgent (runtime := runtime) setup (RecoveryLeaks)
      bounds RecoveryPrior
        horizon
        (RecoveryScheduler) (projectedAgent setup runtime leaks bounds horizon scheduler agent
          clear) :=
      notOwing clear
    obtain ⟨nativeSite, input, lower, near⟩ :=
      values n agent.1 atSite clear owned.2 debtFree owned.1
    have nativeDecision : (N).IsDecisionInfo agent.1
        (RecoveryProjection.information runtime (RecoveryLeaks) (projectInfo agent.2.1)) :=
      input ▸ nativeSite.2
    have nativeSiteEq : (⟨RecoveryProjection.information runtime (RecoveryLeaks)
        (projectInfo agent.2.1), nativeDecision⟩ : (N).InformationSite agent.1) = nativeSite :=
      Subtype.ext input.symm
    have continuationEq : continuation n agent =
        siteValue (runtime := runtime) setup (RecoveryLeaks) bounds horizon (NativeScheduler)
          parameter utility
            excludedPayoff
          (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale
            positive
            le_one weights n) (setup.intendedOpeningProfile (sequence n).strategy) nativeSite := by
      dsimp only [continuation]
      rw [dite_eq_left nativeDecision, nativeSiteEq]
    rw [continuationEq]
    exact ⟨lower, near⟩

end Vegas.SequentialPhase
