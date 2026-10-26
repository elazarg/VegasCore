/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryLocalComparisons
import GameTheoryExtensions.Analysis.Protocol.LocalSimulationLimit
import Vegas.Game.RecoveryInitializedClearance
import Vegas.Game.RecoveryExclusionPayoff
import Vegas.Game.OnePacketCertificateAssembly

/-! # Intended sequential equilibria in the one-packet recovery game

The common completion and its local comparisons preserve the joint typed
readout and base payoff law before count auditing extends the response menu.
The construction does not require an audit backend or a deposit.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (recoveryApplication (runtime setup) leaks).Scheduler}
  [(recoveryApplication (runtime setup) leaks).FiniteNature
    (PMF.map (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup)))
      (initialLaw setup)) scheduler]
  [Finite setup.intendedProtocol.History]

variable {Public : Type*} {signal : State L setup.context → Public}

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => RecoveryProjection.nativeScheduler
  (runtime setup) leaks scheduler
local notation "menu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "R" => RecoveryOnePacket.model setup leaks bounds Initial horizon scheduler
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler

local instance recoveryCompilationHistoryFintype : Fintype (RP).History :=
  (menu).historyFintype Initial horizon scheduler

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

open Classical in
/-- An intended sequential equilibrium has a recovery one-packet implementation
with the same joint readout and base payoff law and no exclusions on its paths,
before adding raw responses. -/
theorem RecoveryOnePacket.intended_sequentialEquilibrium_preserved
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal) {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    (timely : AsyncTimely (runtime setup) delay bound)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)))
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount) :
    ∃ native : (R).BehavioralAssessment,
      native.IsSequentialEquilibriumFor
        ((menu).decisionInformationAntichain Initial horizon scheduler)
        (fun who site => native.truncatedContinuationContext site
          (fun final => recoveryExclusionBase parameter utility excludedPayoff final.state who)
          (2 * horizon + 1)) ∧
      (∀ final ∈ ((R).runBehavioral native.strategy (2 * horizon + 1)).support,
        ∀ control, final.state = some control → control.execution.application.excluded = ∅) ∧
      ((R).runBehavioral native.strategy (2 * horizon + 1)).map (fun final =>
        (sourceReadout setup leaks (RecoveryProjection.protocolState (runtime setup) leaks
          final.state), recoveryExclusionBase parameter utility excludedPayoff final.state)) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  classical
  obtain ⟨sourceSequence, sourceMixed, sourceBayes, sourceConverges, sourceRational⟩ :=
    setup.intended_exclusionSource wellFormed parameter utility excludedPayoff intended
      equilibrium
  let floors := fun n => combinedFloor setup leaks bounds horizon (NativeScheduler)
    (sourceSequence n)
  let scale := fun n => trembleScale (floors n) (2 * horizon + 2) n
  have floorPositive := fun n =>
    combinedFloor_pos setup leaks bounds horizon (NativeScheduler) (sourceSequence n)
  have floorLeOne := fun n =>
    combinedFloor_le_one setup leaks bounds horizon (NativeScheduler) (sourceSequence n)
  have positive : ∀ n, 0 < scale n := fun n => trembleScale_pos (floorPositive n)
  have le_one : ∀ n, scale n ≤ 1 := fun n =>
    trembleScale_le_one (floorPositive n).le (floorLeOne n)
  have vanishes : Tendsto scale atTop (nhds 0) :=
    tendsto_trembleScale floors floorPositive floorLeOne
  obtain ⟨weights, sequence, limit, index, assembled, _mixed, bayes, increasing, converges,
      consistent, pooled, _limits, freeOptimal, _publicOptimal⟩ :=
    RecoveryOnePacket.exists_consistent_completion setup leaks bounds Initial horizon scheduler
      parameter utility excludedPayoff sourceSequence bounds.candidateCount scale positive le_one
      vanishes
  let fallback : ∀ who, (R).Policy who := fun _ _ => Classical.arbitrary _
  let payoffBound : ℝ := ∑ player,
    (max 0 (max (excludedPayoff player) (upperUtility player)) -
      min 0 (min (excludedPayoff player) (lowerUtility player)))
  obtain ⟨nonnegative, readoutBounded, excludedBounded⟩ :=
    exclusionPayoffs_bounded setup parameter utility excludedPayoff lowerUtility upperUtility
      lower_le le_upper
  have payoffBounded : ∀ who (final : (RP).History),
      |recoveryExclusionBase parameter utility excludedPayoff final.state who| ≤ payoffBound := by
    intro who final
    exact GameTheory.Math.abs_le_sum_interval_width
      (fun player => min 0 (min (excludedPayoff player) (lowerUtility player)))
      (fun player => max 0 (max (excludedPayoff player) (upperUtility player)))
      (fun _ => min_le_left _ _) (fun _ => le_max_left _ _) who
      (recoveryExclusionBase_mem_Icc parameter utility excludedPayoff lowerUtility upperUtility
        lower_le le_upper final.state who)
  obtain ⟨error, errorVanishes, comparisons⟩ :=
    if slots_pos : 0 < bounds.candidateCount then
      RecoveryOnePacket.recovery_local_comparisons setup leaks bounds horizon scheduler
        wellFormed independent observable sourceSequence sourceMixed sourceBayes scale positive
        le_one
        (fun _ => rfl) covers coversInputs capacity slots_pos weights sequence (fun _ => fallback)
        assembled bayes opportunity inclusion timely parameter utility excludedPayoff payoffBound
        nonnegative completes payoffBounded excludedBounded below upperUtility le_upper
        readoutBounded pooled
    else
      ⟨fun _ => 0, tendsto_const_nhds, by
          intro _ who _ _ _
          have impossible := capacity who
          omega⟩
  let sourceObserve := intendedReadoutExclusion setup parameter utility excludedPayoff
  let targetObserve := fun final : (RP).History =>
    (sourceReadout setup leaks (RecoveryProjection.protocolState (runtime setup) leaks final.state),
      recoveryExclusionBase parameter utility excludedPayoff final.state)
  let payoff := fun outcome : Option (State L setup.program.terminalCtx) × (Player → ℝ) =>
    fun who => outcome.2 who
  obtain ⟨lawError, lawVanishes, initialized⟩ :=
    RecoveryOnePacket.recovery_initialized_lawApproximation (setup := setup) (leaks := leaks)
        (bounds := bounds)
      (horizon := horizon) (scheduler := scheduler) (wellFormed := wellFormed) (covers := covers)
      (capacity := capacity) (sequence := sourceSequence) (scale := scale) (positive := positive)
      (le_one := le_one) (weights := weights) (fallback := fallback) (opportunity := opportunity)
      (inclusion := inclusion) (timely := timely) (completes := completes) (parameter := parameter)
      (utility := utility) (excludedPayoff := excludedPayoff)
      (strategies := fun n => (sequence n).strategy) (allAssembled := assembled)
      (vanishing := vanishes)
  obtain ⟨recoverySE, recoveryLaw⟩ :=
    sequentialEquilibrium_of_copied_comparisons_limit_of_lawError sourceObserve targetObserve
      (instructionCount setup.program + 1) (2 * horizon + 1)
      ((menu).bounded Initial horizon scheduler)
      ((menu).decisionRecall Initial horizon scheduler) payoff intended sourceSequence
      sourceConverges sourceRational sequence
      (fun _ site => ¬ RecoveryOnePacket.FreeAgent setup leaks bounds Initial horizon scheduler
          ((R).agentAt site))
      error errorVanishes (fun n who site notFree choice => by
        have compared := comparisons n who site notFree choice
        unfold intendedSiteGain payoffComponent at compared
        simpa only [localGain, assessmentComparisonWith, expect_map, targetObserve, sourceObserve,
          payoff, Function.comp_def] using compared)
      lawError lawVanishes initialized limit index increasing converges consistent
      (fun who site free law => by
        rw [← limit.continuationContext_eq_truncated_of_bounded
          ((menu).bounded Initial horizon scheduler).wellFoundedHistories
          ((menu).bounded Initial horizon scheduler)]
        exact freeOptimal who site (not_not.mp free) law)
  have noExclusion := RecoveryOnePacket.initialized_limit_no_exclusion setup leaks bounds
    horizon scheduler wellFormed covers capacity sourceSequence scale positive le_one vanishes
    weights fallback sequence assembled opportunity inclusion timely completes limit index
    increasing (fun who site => converges.strategy who site)
  exact ⟨limit, recoverySE, noExclusion, recoveryLaw⟩

end Vegas
