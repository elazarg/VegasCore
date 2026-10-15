/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryLocalCompletionValue
import Vegas.Game.RecoveryPhaseValueBlind

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
/-- The actual common continuation factors through the current event, with
uniform source-potential and physical completion errors. -/
theorem nativeComparison_pending_value_affine [Fintype (RP).History]
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
    {who : Player} (site : (N).InformationSite who)
    (pendingSite : LateDelivery setup leaks who site.1 ∨ FirstActivation setup leaks who site.1)
    (debtFree : SiteDebtFree setup leaks bounds horizon (NativeScheduler) site)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (law : PMF ((N).Choice who site.1))
    (history : (N).InformationHistory who site.1)
    (forced : ForcedState setup leaks who history.1.state)
    (lawShape : (∃ option : LateOption bounds.candidateCount,
      law = onePacketLate setup leaks bounds horizon (NativeScheduler) sequence scale positive
        le_one n ((N).agentAt site) option) ∨
      law = PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
        who site.1))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let common := nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
      positive le_one weights n
    let certificate := ((Menu).bounded (initialLaw setup) horizon
      (NativeScheduler)).wellFoundedHistories
    let installed := Profile.update (sig := (N).behavioralSignature) common who
      ((common who).withLaw site.1 law)
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup parameter utility excludedPayoff leaks final.state who
    let failure := expect ((N).runBehavioralFrom installed (2 * horizon + 1) history.1)
      (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0)
    |expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff -
      ((1 - failure) *
        decodedPointValue setup leaks bounds horizon (NativeScheduler) parameter utility
          excludedPayoff (setup.intendedOpeningProfile (sequence n).strategy) who
          (siteRank site.1) history.1 +
        failure * excludedPayoff who)| ≤
      (2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
        (2 * horizon + 1) +
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
        (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * payoffBound) +
      2 * payoffBound * (scale n ^ 3 * (2 * horizon + 1)) := by
  intro common certificate installed stopped payoff failure
  let phase := (N).runBehavioralUntil certificate installed
    (LateStopped setup leaks bounds horizon (NativeScheduler) (siteRank site.1)) history.1
  obtain ⟨remaining, execution, current, recallEq, observeEq, ordered⟩ :=
    ordered_of_site setup leaks bounds horizon (NativeScheduler) atSite history
  subst recallEq
  subst observeEq
  let menu := bounds.onePacketMenu (runtime setup) leaks
  have trace : (menu.protocol (initialLaw setup) horizon (NativeScheduler)).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.1.trace
  have rawTrace := menu.toRawTrace (initialLaw setup) horizon (NativeScheduler) trace
  have pendingAt := pending
  rw [atSite] at pendingAt
  obtain ⟨turn, readyView, owned, _⟩ := pendingEvent_spec pendingAt
  have ready := (execution.application.publicView_eventReady event).mp readyView
  have siteKeyHere := siteKey
  rw [atSite] at siteKeyHere
  have decided := decidedEvent_eq_of_pending setup leaks horizon (NativeScheduler) pendingAt
    rawTrace rfl siteKeyHere
  obtain ⟨point, decoded, intendedPoint, _reachedPoint⟩ :=
    intendedReached_of_forced_debtFree wellFormed site debtFree history current ordered forced
  have pointDecoded := (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have clear := publicExclusionRecord_of_decodedIntended rawTrace pointDecoded intendedPoint
  have phaseEq := recovery_pending_until_eq_clearUntil (initialLaw_initialized setup)
    (initialLaw_native setup) completes certificate installed history.1 current ordered clear event
    ready
  have tail := nativeComparison_local_completion_value_sub_le setup leaks bounds horizon scheduler
    wellFormed covers capacity sequence scale positive le_one weights n opportunity inclusion timely
    completes certificate who site.1 law history.1 current history.2 event ready owned key decided
    ordered point decoded intendedPoint parameter utility excludedPayoff boundNonneg readoutBounded
    excludedBounded
  dsimp only at tail
  have freshEq : siteFresh who site.1 = fun control : (application setup leaks).Control =>
      ¬ StoreEventFailed control.execution.application.config.store event := by
    funext control
    simp only [siteFresh, pending]
  rw [← freshEq, ← phaseEq] at tail
  have physical := recovery_pending_phase_value_bounds (initialLaw_initialized setup)
    (initialLaw_native setup) completes parameter utility excludedPayoff wellFormed sequence scale
    positive le_one (fun n => nativeComparisonWeights setup leaks bounds horizon scheduler
      (weights n)) (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
      positive le_one weights)
    (nativeComparisonSequence_assembled setup leaks bounds horizon scheduler sequence scale
      positive le_one weights) n covers (by have := capacity who; omega) le_rfl site pendingSite
    debtFree siteKey pending atSite law history forced lawShape readoutBounded excludedBounded
  dsimp only at physical
  change |expect phase _ -
      ((1 - expect phase (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0)) *
        decodedPointValue setup leaks bounds horizon (NativeScheduler) parameter utility
          excludedPayoff (setup.intendedOpeningProfile (sequence n).strategy) who
          (siteRank site.1) history.1 +
        expect phase (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0) *
          excludedPayoff who)| ≤ _ ∧ expect phase _ ≤ _ at physical
  change |expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff -
      expect phase _| ≤ _ + 2 * payoffBound * expect phase _ at tail
  have smallBad := mul_le_mul_of_nonneg_left physical.2
    (by positivity : 0 ≤ 2 * payoffBound)
  have failureEq := recovery_pending_failure_run_eq_phase (initialLaw_initialized setup)
    (initialLaw_native setup) completes certificate installed history.1 current ordered clear key
    event ready decided
  dsimp only [failure]
  rw [failureEq]
  exact (abs_sub_le _ _ _).trans ((add_le_add tail physical.1).trans (by linarith))

end Vegas.RecoveryOnePacket
