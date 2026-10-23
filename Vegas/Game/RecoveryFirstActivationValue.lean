/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourcePhaseValue

/-! # The common continuation value at a fresh source decision -/

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
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))

open Classical in
/-- At a genuine first callback, the original common continuation is at least
the source value up to its current tremble and honest future retention errors. -/
theorem nativeComparison_firstActivation_value_lower [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    (certificate : (NP).WellFoundedHistories) (history : (NP).History)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (clear : PublicExclusionRecord (RecoveryState.mk execution.application ∅))
    (event : (graph setup).EventId)
    (pending : pendingEvent setup leaks who (some (execution.recall who,
      execution.observe (application setup leaks) who)) = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    sourcePointValue setup parameter utility excludedPayoff
        (setup.intendedOpeningProfile (sequence n).strategy) who point -
      expect ((N).runBehavioralUntil certificate
        (nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale positive
          le_one weights n) stopped history)
        (fun final => if stopped final then excludedPayoff who else
          exclusionBase setup parameter utility excludedPayoff leaks final.state who) ≤
      (2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
        (2 * horizon + 1) + 2 * payoffBound * (1 - slotRetention (scale n)) := by
  intro stopped
  let common := nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
    positive le_one weights n
  let info := (N).infoOf who history.trace
  let main := honestChoice setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
    (sequence n) who info
  let installed := Profile.update (sig := (N).behavioralSignature) common who
    ((common who).withLaw info main)
  let phase := fun final : (NP).History =>
    LateStopped setup leaks bounds horizon (NativeScheduler) rank final ∨ ¬ Clear final.state
  let phaseLaw := (N).runBehavioralUntil certificate installed phase history
  let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
    exclusionBase setup parameter utility excludedPayoff leaks final.state who
  let later := fun final : (NP).History =>
    expect ((N).runBehavioralUntil certificate installed stopped final) payoff
  let value := fun final : (NP).History => (nativeDecodedState setup leaks final.state).elim 0
    (sourcePointValue setup parameter utility excludedPayoff
      (setup.intendedOpeningProfile (sequence n).strategy) who)
  let error := (2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
    (2 * horizon + 1)
  have payoffBounded : ∀ final, |payoff final| ≤ payoffBound := by
    intro final
    dsimp only [payoff]
    split
    · exact excludedBounded
    · rw [exclusionBase_eq_readout]
      exact readoutBounded _
  have laterBounded : ∀ final, |later final| ≤ payoffBound :=
    fun _ => expect_abs_le_of_bounded boundNonneg payoffBounded
  have valueBounded : ∀ final, |value final| ≤ payoffBound := by
    intro final
    dsimp only [value]
    cases nativeDecodedState setup leaks final.state with
    | none =>
        change |(0 : ℝ)| ≤ payoffBound
        simpa only [abs_zero] using boundNonneg
    | some point =>
        exact expect_abs_le_of_bounded boundNonneg readoutBounded
  have running : ¬ (NP).terminal history.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  have active : (NP).active history.state who := by rw [current]; rfl
  have going : ¬ phase history := by
    rintro (⟨other, state, nextPrefix⟩ | failure)
    · rw [current] at state
      cases Option.some.inj state
      have := isPrefix_unique nextPrefix ordered
      omega
    · exact failure (by
        rw [current]
        exact clear)
  have pointwise : ∀ final ∈ phaseLaw.support, |later final - value final| ≤ error := by
    intro final member
    obtain ⟨target, anchor, _stepped, targetIntended, state, _clear, _completed, atRank,
      boundary⟩ :=
      recovery_firstActivation_honest_successorBoundary (initialLaw_initialized setup)
        (initialLaw_native setup) completes opportunity inclusion timely wellFormed covers capacity
        (sequence n) certificate common history current clear event pending never ordered decoded
        intended info rfl final member
    have after := runUntil_after_localLaw_eq certificate
      ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall (initialLaw setup) horizon
        (NativeScheduler)).actsOnceWhereItMatters common who info main phase stopped history rfl
      active running going final member
    have targetDecoded : nativeDecodedState setup leaks final.state = some target := by
      rw [state]
      exact (decodedPoint_eq_of_isPrefix boundary.ordered).trans atRank
    have near := nativeComparison_stopped_boundary_value_sub_le setup leaks bounds horizon
      scheduler wellFormed covers capacity sequence scale positive le_one weights n opportunity
      inclusion timely completes certificate (rank + 1) final anchor state boundary target atRank
      targetIntended parameter utility excludedPayoff who boundNonneg readoutBounded excludedBounded
    have depth : (application setup leaks).rank horizon final.state ≤ 2 * horizon + 1 := by
      have := (application setup leaks).trace_bound (initialLaw setup) horizon (NativeScheduler)
        ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
          (NativeScheduler) final.trace)
      omega
    dsimp only [later, value]
    rw [after, targetDecoded]
    exact near.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast depth) (by
      have := slotRetention_le_one (positive n).le (le_one n)
      positivity))
  have sourceLaw := recovery_firstActivation_honest_sourceLaw (initialLaw_initialized setup)
    (initialLaw_native setup) opportunity inclusion timely completes wellFormed covers capacity
    (sequence n) certificate common history current clear event pending never ordered decoded
    intended info rfl
  have sourceMean : expect phaseLaw value = sourcePointValue setup parameter utility excludedPayoff
      (setup.intendedOpeningProfile (sequence n).strategy) who point := by
    have mean := congrArg (fun law : PMF (Option (ProtocolState setup.program)) =>
      expect law (fun decoded => decoded.elim 0 (sourcePointValue setup parameter utility
        excludedPayoff (setup.intendedOpeningProfile (sequence n).strategy) who))) sourceLaw
    rw [expect_map, expect_map] at mean
    exact mean.trans (expect_sourcePointValue_behavioralStateStep setup parameter utility
      excludedPayoff _ who readoutBounded point)
  have reference : |expect ((N).runBehavioralUntil certificate installed stopped history) payoff -
      sourcePointValue setup parameter utility excludedPayoff
        (setup.intendedOpeningProfile (sequence n).strategy) who point| ≤ error := by
    rw [debtStopped_eq_bind_eventPhase certificate installed who history _ current ordered point
      decoded intended, expect_bind_tower_bounded _ _ _ payoffBounded, ← sourceMean,
      ← expect_sub (payoffIntegrable_of_bounded _ _ laterBounded)
        (payoffIntegrable_of_bounded _ _ valueBounded)]
    have integrable := payoffIntegrable_sub (payoffIntegrable_of_bounded phaseLaw later
      laterBounded) (payoffIntegrable_of_bounded phaseLaw value valueBounded)
    have upper := expect_le_const phaseLaw _ integrable error fun final member =>
      (abs_le.mp (pointwise final member)).2
    have lower := expect_mono (μ := phaseLaw) (f := fun _ => -error)
      (fun final member => (abs_le.mp (pointwise final member)).1)
      (payoffIntegrable_constant _ _) integrable
    rw [expect_constant] at lower
    exact abs_le.mpr ⟨lower, upper⟩
  have infoEq : info = some (execution.recall who,
      execution.observe (application setup leaks) who) := by
    change ((bounds.onePacketMenu (runtime setup) leaks).signals (initialLaw setup) horizon
      (NativeScheduler)).infoOf who history.trace = _
    rw [ReactiveApplication.ResponseMenu.info, current]
    simp only [ReactiveApplication.observe, ite_true]
  have forced : Vegas.forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup)
      horizon (NativeScheduler) who info := by
    apply forcedAgent_of_history history
    rw [current]
    exact ⟨rank, point, ordered, decoded, forcedPoint_of_intended who intended⟩
  have first : FirstActivation setup leaks who info := by
    refine ⟨_, _, event, infoEq, ?_, never⟩
    rw [infoEq]
    exact pending
  have close := PMF.WithinTV.of_domination main (common who info) (slotRetention (scale n))
    (slotRetention_le_one (positive n).le (le_one n)) (fun choice =>
      onePacketMixture_ge_honest_of_not_late setup leaks bounds horizon (NativeScheduler) sequence
        scale positive le_one n (nativeComparisonWeights setup leaks bounds horizon scheduler
          (weights n)) (not_lateDelivery_of_firstActivation first) ⟨history, rfl⟩ forced choice)
  have safe : ¬ stopped history := by
    rintro (failure | debt)
    · exact failure (by rw [current]; exact clear)
    · rw [current] at debt
      obtain ⟨found, ⟨residual⟩, holds⟩ := debt
      exact ProtocolState.Intended.not_owesFailure who setup.program point intended
        (holds point ((decodedPoint_eq_of_isPrefix residual.checkpoint.ordered).symm.trans
          ((decodedPoint_eq_of_isPrefix ordered).trans decoded)))
  let selectedValue := fun choice : (N).Choice who info =>
    expect ((N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) common who
        ((common who).commit info choice)) stopped history) payoff
  have selectedBounded : ∀ choice, |selectedValue choice| ≤ payoffBound :=
    fun _ => expect_abs_le_of_bounded boundNonneg payoffBounded
  have estimate := close.expect_sub_le selectedValue (-payoffBound) (2 * payoffBound)
    (fun choice _ => by have := abs_le.mp (selectedBounded choice); constructor <;> linarith)
  have affine := fun law => (N).runBehavioralUntil_update_withLaw_eq_bind certificate
    ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall (initialLaw setup) horizon
      (NativeScheduler)).actsOnceWhereItMatters common who (common who) info law stopped history
        rfl safe running active
  have baseline := affine (common who info)
  rw [BehavioralPolicy.withLaw_eq_self, Profile.update_eq_self] at baseline
  have mainLaw := affine main
  have baselineMean := congrArg (fun law => expect law payoff) baseline
  have mainMean := congrArg (fun law => expect law payoff) mainLaw
  rw [expect_bind_tower_bounded _ _ _ payoffBounded] at baselineMean mainMean
  have estimate' :
      expect ((N).runBehavioralUntil certificate installed stopped history) payoff -
        expect ((N).runBehavioralUntil certificate common stopped history) payoff ≤
          (1 - slotRetention (scale n)) * (2 * payoffBound) := by
    rw [mainMean, baselineMean]
    exact estimate
  have near := (abs_le.mp reference).1
  dsimp only [error] at near
  linarith

end Vegas.RecoveryOnePacket
