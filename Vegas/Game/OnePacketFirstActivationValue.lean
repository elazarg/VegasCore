/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketComparisonContinuationValue
import Vegas.Game.OnePacketSuccessorBoundary

/-! # The common continuation value at a fresh source decision -/

noncomputable section

namespace Vegas.OnePacketComparison

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)

local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks)
    (fun native : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

open Classical in
/-- At a genuine first callback, the original common continuation is at least
the source value up to its current tremble and honest future retention errors. -/
theorem assembled_firstActivation_value_lower
    [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      positive le_one weights targetSequence) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some
        control) →
      control.execution.application.config.defaulted = ∅ →
      OpportunityAt runtime leaks control.execution delay)
    (inclusion : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some
        control) →
      control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt runtime leaks control.execution bound)
    (timely : runtime.AsyncTimely delay bound)
    (completes : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some
        control) →
      control.execution.application.config.defaulted = ∅ →
      (application setup runtime leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (certificate : (NP).WellFoundedHistories) (history : (NP).History)
    {remaining : Nat} {who : Player} {execution : (application setup runtime leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (clear : execution.application.config.defaulted = ∅)
    (event : (graph setup).EventId)
    (pending : pendingEvent setup runtime leaks who (some (execution.logs who,
      execution.observe (application setup runtime leaks) who)) = some event)
    (never : ∀ entry ∈ execution.logs who, ¬ ActivatedAt setup runtime leaks who event entry)
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
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    sourcePointValue setup parameter utility excludedPayoff
        (setup.intendedOpeningProfile (sequence n).strategy) who point -
      expect ((N).runBehavioralUntil certificate
        (targetSequence n).strategy stopped history)
        (fun final => if stopped final then excludedPayoff who else
          exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who) ≤
      (2 * payoffBound * (1 - slotRetention (scale n))) *
        (2 * horizon + 1) + 2 * payoffBound * (1 - slotRetention (scale n)) := by
  intro stopped
  let common := (targetSequence n).strategy
  let info := (N).infoOf who history.trace
  let main := honestChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler
    (sequence n) who info
  let installed := Profile.update (sig := (N).behavioralSignature) common who
    ((common who).withLaw info main)
  let phase := fun final : (NP).History =>
    LateStopped setup runtime leaks bounds horizon scheduler rank final ∨ ¬ Clear
      final.state
  let phaseLaw := (N).runBehavioralUntil certificate installed phase history
  let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
    exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who
  let later := fun final : (NP).History =>
    expect ((N).runBehavioralUntil certificate installed stopped final) payoff
  let value := fun final : (NP).History => (nativeDecodedState setup runtime leaks
    final.state).elim 0
    (sourcePointValue setup parameter utility excludedPayoff
      (setup.intendedOpeningProfile (sequence n).strategy) who)
  let error := (2 * payoffBound * (1 - slotRetention (scale n))) *
    (2 * horizon + 1)
  have baseBounded : ∀ final : (NP).History,
      |exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who| ≤
        payoffBound := by
    intro final
    cases final.state with
    | none => simpa only [exclusionBase, abs_zero] using boundNonneg
    | some control =>
        change |if who ∈ control.execution.application.config.defaulted then excludedPayoff who
          else exclusionReadoutUtility setup parameter utility excludedPayoff
            (sourceReadout setup runtime leaks (some control)) who| ≤ payoffBound
        split
        · exact excludedBounded
        · exact readoutBounded _
  have payoffBounded : ∀ final, |payoff final| ≤ payoffBound := by
    intro final
    dsimp only [payoff]
    split
    · exact excludedBounded
    · exact baseBounded final
  have laterBounded : ∀ final, |later final| ≤ payoffBound :=
    fun _ => expect_abs_le_of_bounded boundNonneg payoffBounded
  have valueBounded : ∀ final, |value final| ≤ payoffBound := by
    intro final
    dsimp only [value]
    cases nativeDecodedState setup runtime leaks final.state with
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
    rintro (⟨other, state, event, completed, rankEq⟩ | failure)
    · rw [current] at state
      cases Option.some.inj state
      have earlier := (ordered.2 event).mp completed
      omega
    · exact failure (by
        rw [current]
        exact clear)
  have pointwise : ∀ final ∈ phaseLaw.support, |later final - value final| ≤ error := by
    intro final member
    obtain ⟨target, anchor, _stepped, targetIntended, state, _clear, _completed, atRank,
      boundary⟩ :=
      counted_firstActivation_honest_successorBoundary (runtime := runtime) completes opportunity
        inclusion timely
        covers capacity
        (sequence n) certificate common history current clear event pending never ordered decoded
        intended info rfl final member
    have after := runUntil_after_localLaw_eq certificate
      ((bounds.onePacketMenu runtime leaks).decisionRecall (initialLaw setup) horizon
        scheduler).actsOnceWhereItMatters common who info main phase stopped history rfl
      active running going final member
    have targetDecoded : nativeDecodedState setup runtime leaks final.state = some target := by
      rw [state]
      exact (decodedPoint_eq_of_isPrefix boundary.ordered).trans atRank
    have near := assembled_stopped_boundary_value_sub_le setup runtime leaks bounds horizon
      scheduler wellFormed covers capacity sequence scale positive le_one weights targetSequence
      assembled n opportunity inclusion timely completes certificate (rank + 1) final anchor state
      boundary target atRank targetIntended parameter utility excludedPayoff who boundNonneg
      baseBounded excludedBounded
    have depth : (application setup runtime leaks).rank horizon final.state ≤ 2 * horizon + 1 := by
      have := (application setup runtime leaks).trace_bound (initialLaw setup) horizon
        scheduler
        ((bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon
          scheduler final.trace)
      omega
    dsimp only [later, value]
    rw [after, targetDecoded]
    exact near.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast depth) (by
      have := slotRetention_le_one (positive n).le (le_one n)
      positivity))
  have sourceLaw := counted_firstActivation_honest_sourceLaw (runtime := runtime) opportunity
    inclusion timely completes
    covers capacity
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
    rw [debtStopped_eq_bind_eventPhase (runtime := runtime) certificate installed who history _
      current ordered point
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
  have infoEq : info = some (execution.logs who,
      execution.observe (application setup runtime leaks) who) := by
    change ((bounds.onePacketMenu runtime leaks).signals (initialLaw setup) horizon
      scheduler).infoOf who history.trace = _
    rw [ReactiveApplication.ResponseMenu.info, current]
    simp only [ReactiveApplication.observe, ite_true]
  have forced : Vegas.forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks)
    (initialLaw setup)
      horizon scheduler who info := by
    apply forcedAgent_of_history (runtime := runtime) history
    rw [current]
    exact ⟨rank, point, ordered, decoded, forcedPoint_of_intended who intended⟩
  have first : FirstActivation setup runtime leaks who info := by
    refine ⟨_, _, event, infoEq, ?_, never⟩
    rw [infoEq]
    exact pending
  have close := PMF.WithinTV.of_domination main (common who info) (slotRetention (scale n))
    (slotRetention_le_one (positive n).le (le_one n)) (fun choice => by
      dsimp only [common]
      rw [assembled n]
      exact onePacketMixture_ge_honest_of_not_late setup runtime leaks bounds horizon scheduler
        sequence scale positive le_one n (weights n)
        (not_lateDelivery_of_firstActivation (runtime := runtime) first) ⟨history, rfl⟩ forced
        (clearInput_of_intended setup runtime leaks bounds horizon scheduler history current
          ((decodedPoint_eq_of_isPrefix ordered).trans decoded) intended who) choice)
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
    ((bounds.onePacketMenu runtime leaks).decisionRecall (initialLaw setup) horizon
      scheduler).actsOnceWhereItMatters common who (common who) info law stopped history
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

end Vegas.OnePacketComparison
