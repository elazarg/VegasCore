/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryLocalCompletionValue
import Vegas.Game.RecoveryPhaseValueBlind
import Vegas.Game.RecoveryFirstActivationValue
import Vegas.Game.OnePacketValueTransport

/-! # A single source deviation for all histories of a nonlate commitment -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

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
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)
local notation "Menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))

open Classical in
/-- Waiting at a fresh debt-free source decision has vanishing gain. -/
theorem nativeComparison_silence_history_comparison [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount p)) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    {who : Player} (site : (N).InformationSite who) (choice : (N).Choice who site.1)
    (notFree : ¬ Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site))
    (notOwing : ¬ Vegas.OwingAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site))
    (nonlate : ¬ LateDelivery setup leaks who site.1)
    (event : (graph setup).EventId)
    (pending : pendingEvent setup leaks who site.1 = some event)
    (silent : choice.1 = some ⟨none⟩)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (upper : ℝ) (le_upper : ∀ outcome, utility outcome who ≤ upper)
    {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound)
    :
    let common := nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
      positive le_one weights n
    let certificate := ((Menu).bounded (initialLaw setup) horizon
      (NativeScheduler)).wellFoundedHistories
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup parameter utility excludedPayoff leaks final.state who
    ∀ history : (N).InformationHistory who site.1,
      RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) who history.1.trace →
      expect ((N).runBehavioralUntil certificate
          (Profile.update (sig := (N).behavioralSignature) common who
            ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
        expect ((N).runBehavioralUntil certificate common stopped history.1) payoff ≤
      2 * ((2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
        (2 * horizon + 1)) + 2 * payoffBound * (1 - slotRetention (scale n)) +
      2 * payoffBound * (scale n ^ 3 * (2 * horizon + 1)) +
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
        (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * payoffBound) := by
  intro common certificate stopped payoff history regular
  have forced := forcedAgent_of_not_free setup leaks bounds horizon (NativeScheduler) notFree
  have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon (NativeScheduler) notOwing
  have ownIntended := ownCompletionsIntended_of_siteNotOwes wellFormed debtFree history
  have allDebtFree := not_owesFailure_of_regular wellFormed (sequence n) atSite forced history
    regular ownIntended
  have stateForced := forcedState_of_regular wellFormed (sequence n) atSite forced history regular
    ownIntended
  obtain ⟨remaining, execution, point, current, actualAt, never, ordered, decoded, intended,
    reached⟩ := firstActivation_history_facts setup leaks bounds horizon (NativeScheduler)
      wellFormed site pending nonlate history stateForced allDebtFree
  let key := LateKey.ofView setup leaks who (execution.recall who)
    (execution.observe (application setup leaks) who)
  have siteKey : lateKey setup leaks who site.1 = some key := by
    rw [actualAt]
    exact lateKey_some who (execution.recall who)
      (execution.observe (application setup leaks) who)
  have pendingHere := pending
  rw [actualAt] at pendingHere
  obtain ⟨turn, readyPublic, owned, _unrecorded⟩ := pendingEvent_spec pendingHere
  have ready := (execution.application.publicView_eventReady event).mp readyPublic
  have decodedPoint := (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have clear := publicExclusionRecord_of_decodedIntended
    ((Menu).toRawTrace (initialLaw setup) horizon (NativeScheduler) (current ▸ history.1.trace))
    decodedPoint intended
  have decided := decidedEvent_eq_of_pending setup leaks horizon (NativeScheduler) pendingHere
    ((Menu).toRawTrace (initialLaw setup) horizon (NativeScheduler) (current ▸ history.1.trace)) rfl
    (lateKey_some who (execution.recall who)
      (execution.observe (application setup leaks) who))
  have choiceEq : choice = silenceChoice setup leaks bounds (initialLaw setup) horizon
      (NativeScheduler) who site.1 := by
    apply Subtype.ext
    rw [silenceChoice_val who site.1 (by rw [actualAt]; rfl)]
    exact silent
  let installed := Profile.update (sig := (N).behavioralSignature) common who
    ((common who).withLaw site.1 (PMF.pure choice))
  let phase := (N).runBehavioralUntil certificate installed
    (LateStopped setup leaks bounds horizon (NativeScheduler) (siteRank site.1)) history.1
  have first : FirstActivation setup leaks who site.1 :=
    ⟨_, _, event, actualAt, pending, never⟩
  have physical := recovery_pending_phase_value_bounds (initialLaw_initialized setup)
    (initialLaw_native setup) completes parameter utility excludedPayoff wellFormed sequence scale
    positive le_one (fun n => nativeComparisonWeights setup leaks bounds horizon scheduler
      (weights n)) (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
      positive le_one weights)
    (nativeComparisonSequence_assembled setup leaks bounds horizon scheduler sequence scale
      positive le_one weights) n covers (by have := capacity who; omega) le_rfl site
    (Or.inr first)
    debtFree siteKey pending actualAt (PMF.pure choice) history stateForced
    (Or.inr (congrArg PMF.pure choiceEq)) readoutBounded excludedBounded
  dsimp only at physical
  change |expect phase _ -
      ((1 - expect phase (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0)) *
        decodedPointValue setup leaks bounds horizon (NativeScheduler) parameter utility
          excludedPayoff (setup.intendedOpeningProfile (sequence n).strategy) who
          (siteRank site.1) history.1 +
        expect phase (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0) *
          excludedPayoff who)| ≤ _ ∧ expect phase _ ≤ _ at physical
  have pointValue : decodedPointValue setup leaks bounds horizon (NativeScheduler) parameter
      utility excludedPayoff (setup.intendedOpeningProfile (sequence n).strategy) who
      (siteRank site.1) history.1 = sourcePointValue setup parameter utility excludedPayoff
        (setup.intendedOpeningProfile (sequence n).strategy) who point := by
    simp only [decodedPointValue, current, decoded, reached, ↓reduceIte]
  rw [pointValue] at physical
  have lower : excludedPayoff who ≤ sourcePointValue setup parameter utility excludedPayoff
      (setup.intendedOpeningProfile (sequence n).strategy) who point :=
    (sourcePointValue_mem_Icc setup parameter utility excludedPayoff
      (setup.intendedOpeningProfile (sequence n).strategy) who upper le_upper
      (fun target reachable => excludedPayoff_le_of_reached setup parameter utility excludedPayoff
        wellFormed below (sequence n).strategy target reachable who) point reached).1
  have probabilityNonneg : 0 ≤ expect phase
      (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0) := by
    apply expect_nonneg
    intro final _
    split <;> norm_num
  have phaseEq := recovery_pending_until_eq_clearUntil (initialLaw_initialized setup)
    (initialLaw_native setup) completes certificate installed history.1 current ordered clear event
    ready
  have tail := nativeComparison_local_completion_value_sub_le setup leaks bounds horizon scheduler
    wellFormed covers capacity sequence scale positive le_one weights n opportunity inclusion timely
    completes certificate who site.1 (PMF.pure choice) history.1 current history.2 event ready owned
    key decided ordered point decoded intended parameter utility excludedPayoff boundNonneg
    readoutBounded excludedBounded
  dsimp only at tail
  have freshEq : siteFresh who site.1 = fun control : (application setup leaks).Control =>
      ¬ StoreEventFailed control.execution.application.config.store event := by
    funext control
    simp only [siteFresh, pending]
  rw [← freshEq, ← phaseEq] at tail
  have baseline := nativeComparison_firstActivation_value_lower setup leaks bounds horizon
    scheduler wellFormed covers capacity sequence scale positive le_one weights n opportunity
    inclusion timely completes certificate history.1 current clear event pendingHere never ordered
    decoded intended parameter utility excludedPayoff boundNonneg readoutBounded excludedBounded
  dsimp only at baseline
  change sourcePointValue setup parameter utility excludedPayoff
      (setup.intendedOpeningProfile (sequence n).strategy) who point -
      expect ((N).runBehavioralUntil certificate common stopped history.1) payoff ≤ _ at baseline
  change |expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff -
      expect phase _| ≤ _ + 2 * payoffBound * expect phase _ at tail
  have smallBad := mul_le_mul_of_nonneg_left physical.2
    (by positivity : 0 ≤ 2 * payoffBound)
  have affineUpper := (abs_le.mp physical.1).2
  have tailUpper := (abs_le.mp tail).2
  nlinarith [mul_nonneg probabilityNonneg (sub_nonneg.mpr lower)]

end Vegas.RecoveryOnePacket
