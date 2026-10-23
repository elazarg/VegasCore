/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryKeyedValueBounds
import Vegas.Game.RecoveryPooledGains

/-! # Member gains under the original pooled recovery completion -/

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
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "RApp" => recoveryApplication (runtime setup) leaks
local notation "RawNative" => ReactiveApplication.protocol (application setup leaks)
  (PMF.map RecoveryState.native (Initial)) horizon (NativeScheduler)
local notation "ClearState" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks

local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)

open Classical in
/-- The original common completion witness and concrete runtime value estimates
bound every member's component-mixture gain, with a uniform vanishing error.
The supplied weights, assessment sequence and continuation pooling are unchanged. -/
theorem recovery_pooled_member_gain_bounds [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [(recoveryApplication (runtime setup) leaks).FiniteNature Initial scheduler]
    [Finite setup.intendedProtocol.History]
    [∀ player, DecidableEq ((R).InfoState player)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependent)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
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
    (certificate : ((NMenu).protocol (initialLaw setup) horizon
      (NativeScheduler)).WellFoundedHistories)
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
    (slots_pos : 0 < bounds.candidateCount)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (upper : ℝ) (le_upper : ∀ outcome who, utility outcome who ≤ upper)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal → ∀ who,
        excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
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
    ∃ memberError : ℕ → ℝ, Tendsto memberError atTop (nhds 0) ∧
      ∀ n who (site : (R).InformationSite who)
        (alternative : PMF (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount
          (pool setup leaks bounds Initial horizon scheduler ((R).agentAt site)))),
        localGain (2 * horizon + 1) (fun final => final.state)
          (recoveryExclusionBase parameter utility excludedPayoff) (assessments n) site
          (alternative.bind (component setup leaks bounds Initial horizon scheduler (sequence n)
            (scale n) (positive n).le (le_one n) ((R).agentAt site))) ≤ memberError n := by
  obtain ⟨continuation, score, error, limit, _scoreUnit, values⟩ :=
    recovery_keyed_component_value_bounds setup leaks bounds horizon scheduler wellFormed
      independent
      sequence sourceMixed scale positive le_one scaleEq covers coversInputs capacity weights
      assessments fallback assembled bayes opportunity inclusion timely certificate rawCertificate
      parameter utility excludedPayoff payoffBound nonnegative recoveryCertificate menuCertificate
      completes payoffBounded excludedBounded slots_pos readoutBounded upper le_upper below
  let memberError := fun n =>
    (Fintype.card ((R).InformationAgent (R).playedInformation) : ℝ) * (2 * max (error n) 0)
  have memberLimit : Tendsto memberError atTop (nhds 0) := by
    have clipped : Tendsto (fun n => max (error n) 0) atTop (nhds 0) := by
      simpa only [max_self] using limit.max (tendsto_const_nhds (x := (0 : ℝ)))
    simpa only [mul_zero] using (clipped.const_mul 2).const_mul
      (Fintype.card ((R).InformationAgent (R).playedInformation) : ℝ)
  refine ⟨memberError, memberLimit, ?_⟩
  intro n who site alternative
  have pooledGain := pooledLocalGain_nonpos_of_continuation setup leaks bounds horizon scheduler
    (fun final => final.state) (recoveryExclusionBase parameter utility excludedPayoff)
    (assessments n) (sequence n) (scale n) (positive n).le (le_one n) (pooled n)
  exact componentGain_le_of_common_values setup leaks bounds horizon scheduler parameter utility
    excludedPayoff completes (assessments n) (sequence n) (scale n) (positive n).le (le_one n)
    (weights n) (fallback n) (assembled n) pooledGain (continuation n) (score n) (error n)
    (values n)
    who site alternative


open Classical in
/-- Every keyed option is an actual pure part of the same original pool, so
its component gain inherits the all-member-mixture bound without changing weights. -/
theorem keyedComponent_gain_le_of_member_mixtures [Fintype (RP).History]
    [∀ who, DecidableEq ((R).InfoState who)]
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (assessment : (R).BehavioralAssessment)
    (source : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    {who : Player} (site : (R).InformationSite who)
    (keyed : ownedKeyed (FreeAgent setup leaks bounds Initial horizon scheduler)
      (KeyedAgent setup leaks bounds Initial horizon scheduler) ((R).agentAt site))
    {error : ℝ}
    (members : ∀ alternative : PMF (Part setup leaks bounds Initial horizon scheduler slots
        (pool setup leaks bounds Initial horizon scheduler ((R).agentAt site))),
      localGain (2 * horizon + 1) (fun final => final.state)
        (recoveryExclusionBase parameter utility excludedPayoff) assessment site
        (alternative.bind (component setup leaks bounds Initial horizon scheduler source scale
          nonnegative le_one ((R).agentAt site))) ≤ error)
    (option : LateOption slots) :
    localGain (2 * horizon + 1) (fun final => final.state)
      (recoveryExclusionBase parameter utility excludedPayoff) assessment site
      (keyedComponent setup leaks bounds Initial horizon scheduler source scale nonnegative le_one
        ((R).agentAt site) option) ≤ error := by
  let agent := (R).agentAt site
  let prescribed := prescribedComponent setup leaks bounds Initial horizon scheduler source scale
    nonnegative le_one
  let lateLaw := keyedComponent setup leaks bounds Initial horizon scheduler source
    (slots := slots) scale nonnegative le_one
  obtain ⟨identify, same⟩ := freeKeyedComponent_of_not_free
    (key := agentKey setup leaks bounds Initial horizon scheduler)
    (keyed := KeyedAgent setup leaks bounds Initial horizon scheduler)
    (freeLaw setup leaks bounds Initial horizon scheduler scale nonnegative le_one)
    prescribed lateLaw keyed.2
  let best := keyedBest
    (keyed := ownedKeyed (FreeAgent setup leaks bounds Initial horizon scheduler)
      (KeyedAgent setup leaks bounds Initial horizon scheduler))
    (key := agentKey setup leaks bounds Initial horizon scheduler) (fun _ => option)
    (keyedPool (ownedKeyed (FreeAgent setup leaks bounds Initial horizon scheduler)
      (KeyedAgent setup leaks bounds Initial horizon scheduler))
      (agentKey setup leaks bounds Initial horizon scheduler) agent)
  let part := identify.symm best
  have lawEq : component setup leaks bounds Initial horizon scheduler source scale nonnegative
      le_one agent part = lateLaw agent option := by
    refine (same part).trans ?_
    change InformationModel.keyedComponent prescribed lateLaw agent
      (identify (identify.symm best)) = lateLaw agent option
    rw [identify.apply_symm_apply]
    exact keyedComponent_best_of_keyed prescribed lateLaw (fun _ => option) keyed
  have near := members (PMF.pure part)
  simp only [PMF.pure_bind] at near
  change localGain (2 * horizon + 1) (fun final => final.state)
    (recoveryExclusionBase parameter utility excludedPayoff) assessment site
    (component setup leaks bounds Initial horizon scheduler source scale nonnegative le_one
      agent part) ≤ error at near
  rw [lawEq] at near
  exact near

end Vegas.RecoveryOnePacket
