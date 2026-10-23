/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryKeyedFailure
import Vegas.Game.RecoveryPendingValueAffine
import Vegas.Game.RecoveryLocalValueComparison
import GameTheoryExtensions.Math.Probability.AffineDecorrelation
import Vegas.Game.OnePacketLateCommitments

/-! # Keyed payoff factors under the actual common posterior -/

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
/-- The same native comparison posterior factors the pending-event failure and
source continuation value. Only actual recovery service premises are used. -/
theorem nativeComparison_keyed_value_sub_le [Fintype (RP).History]
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
    (late : LateDelivery setup leaks who site.1)
    (debtFree : SiteDebtFree setup leaks bounds horizon (NativeScheduler) site)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    {unforced gamma : ℝ}
    (unforcedMass : expect ((nativeComparisonSequence setup leaks bounds horizon scheduler
      sequence scale positive le_one weights n).belief who site) (fun history =>
        if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤ unforced)
    (decorrelated : BeliefDecorrelated ((nativeComparisonSequence setup leaks bounds horizon
      scheduler sequence scale positive le_one weights n).belief who site)
      (fun history => operationalRecord setup leaks bounds horizon (NativeScheduler)
        history.1.trace)
      (fun history => nativeDecodedState setup leaks history.1.state) gamma)
    (option : LateOption bounds.candidateCount)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let target := nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
      positive le_one weights n
    let common := target.strategy
    let certificate := ((NMenu).bounded (initialLaw setup) horizon
      (NativeScheduler)).wellFoundedHistories
    let law := onePacketLate setup leaks bounds horizon (NativeScheduler) sequence scale positive
      le_one n ((N).agentAt site) option
    let installed := Profile.update (sig := (N).behavioralSignature) common who
      ((common who).withLaw site.1 law)
    let stopped := fun final : (NP).History => ¬ ClearState final.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup parameter utility excludedPayoff leaks final.state who
    let error := (2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
      (2 * horizon + 1) +
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
        (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * payoffBound) +
      2 * payoffBound * (scale n ^ 3 * (2 * horizon + 1))
    |expect (target.belief who site) (fun history =>
        expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff) -
      (excludedPayoff who +
        (1 - localFailure (2 * horizon + 1) target site
          {final | DecisionFailed key final.state} law) *
          (siteValue setup leaks bounds horizon (NativeScheduler) parameter utility excludedPayoff
            target (setup.intendedOpeningProfile (sequence n).strategy) site - excludedPayoff
              who))| ≤
      error + 2 * payoffBound * unforced +
      4 * payoffBound * ((2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3) + unforced) +
      4 * payoffBound * gamma := by
  intro target common certificate law installed stopped payoff error
  let belief := target.belief who site
  let failure := fun history : (N).InformationHistory who site.1 =>
    expect (localHistoryRun (2 * horizon + 1) target site law history)
      (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0)
  let value := fun history : (N).InformationHistory who site.1 =>
    decodedPointValue setup leaks bounds horizon (NativeScheduler) parameter utility excludedPayoff
      (setup.intendedOpeningProfile (sequence n).strategy) who (siteRank site.1) history.1
  let valueOf : setup.ProtocolState → ℝ := fun found => match found with
    | none => excludedPayoff who
    | some point => if IntendedReached setup point then
        sourcePointValue setup parameter utility excludedPayoff
          (setup.intendedOpeningProfile (sequence n).strategy) who point else excludedPayoff who
  let result := fun history : (N).InformationHistory who site.1 =>
    expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff
  let lumping := nativeComparisonLumping setup leaks bounds horizon scheduler sequence scale
    positive
    le_one weights covers capacity n who
  let lumped := lumpedFailure setup leaks bounds horizon (NativeScheduler) lumping
    (2 * horizon + 1) key option
  let pathError : ℝ := (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)
  have pathNonneg : 0 ≤ pathError := by
    have := (positive n).le
    dsimp only [pathError]
    positivity
  have errorNonneg : 0 ≤ error := by
    have retained := slotRetention_le_one (positive n).le (le_one n)
    have := (positive n).le
    dsimp only [error]
    positivity
  have failureUnit : ∀ history, 0 ≤ failure history ∧ failure history ≤ 1 := by
    intro history
    exact expect_mem_unit _ _ fun _ => by split <;> norm_num
  have lumpedUnit : ∀ record, 0 ≤ lumped record ∧ lumped record ≤ 1 := by
    intro record
    exact expect_mem_unit _ _ (lumping.failure_unit key)
  have valueBounded : ∀ found, |valueOf found| ≤ payoffBound := by
    intro found
    cases found with
    | none => exact excludedBounded
    | some point =>
        simp only [valueOf]
        split
        · exact expect_abs_le_of_bounded boundNonneg readoutBounded
        · exact excludedBounded
  have valueEq : ∀ history : (N).InformationHistory who site.1,
      value history = valueOf (nativeDecodedState setup leaks history.1.state) := by
    intro history
    obtain ⟨remaining, execution, current, _, _, ordered⟩ :=
      ordered_of_site setup leaks bounds horizon (NativeScheduler) atSite history
    unfold value decodedPointValue
    rw [current]
    change _ = valueOf (decodedPoint setup execution.application.config)
    rw [decodedPoint_eq_of_isPrefix ordered]
    rfl
  have failureNear : expect belief (fun history => |failure history - lumped
      (operationalRecord setup leaks bounds horizon (NativeScheduler) history.1.trace)|) ≤
      pathError + unforced := by
    have pointwise : ∀ history ∈ belief.support,
        |failure history - lumped (operationalRecord setup leaks bounds horizon (NativeScheduler)
          history.1.trace)| ≤ pathError +
          if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1 := by
      intro history supported
      by_cases forced : ForcedState setup leaks who history.1.state
      · simp only [forced, ↓reduceIte, add_zero]
        have near := lumping.pathwise (2 * horizon + 1) site ⟨Or.inl late, debtFree⟩ key siteKey
          option history supported forced
        simpa only [failure, localHistoryRun, lumped, pathError, target, law,
          InformationModel.truncatedRunner, lumpedFailure] using near
      · simp only [forced, ↓reduceIte]
        have := failureUnit history
        have := lumpedUnit (operationalRecord setup leaks bounds horizon (NativeScheduler)
          history.1.trace)
        rw [abs_le]
        constructor <;> linarith
    have averaged := expect_mono pointwise (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)
    rw [expect_add (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _),
      expect_constant] at averaged
    exact averaged.trans (by dsimp only [belief]; linarith [unforcedMass])
  have payoffNear : expect belief (fun history =>
      |result history - (excludedPayoff who +
        (1 - failure history) * (value history - excludedPayoff who))|) ≤
      error + 2 * payoffBound * unforced := by
    have payoffBounded : ∀ final, |payoff final| ≤ payoffBound := by
      intro final
      dsimp only [payoff]
      split
      · exact excludedBounded
      · rw [exclusionBase_eq_readout]
        exact readoutBounded _
    have pointwise : ∀ history ∈ belief.support,
        |result history - (excludedPayoff who +
          (1 - failure history) * (value history - excludedPayoff who))| ≤
        error + 2 * payoffBound *
          if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1 := by
      intro history _supported
      by_cases forced : ForcedState setup leaks who history.1.state
      · simp only [forced, ↓reduceIte, mul_zero, add_zero]
        have near := nativeComparison_pending_value_affine setup leaks bounds horizon scheduler
          wellFormed covers capacity sequence scale positive le_one weights n opportunity inclusion
          timely completes site (Or.inl late) debtFree siteKey pending atSite law history forced
          (Or.inl ⟨option, rfl⟩) parameter utility excludedPayoff boundNonneg readoutBounded
          excludedBounded
        have centered : (excludedPayoff who +
            (1 - failure history) * (value history - excludedPayoff who)) =
            (1 - failure history) * value history + failure history * excludedPayoff who := by ring
        rw [centered]
        exact near
      · simp only [forced, ↓reduceIte, mul_one]
        have resultBound := expect_abs_le_of_bounded boundNonneg payoffBounded
          (μ := ((N).runBehavioralUntil certificate installed stopped history.1))
        have sourceBound : |value history| ≤ payoffBound := by rw [valueEq]; exact valueBounded _
        have failedUnit := failureUnit history
        have mixtureBound : |excludedPayoff who +
            (1 - failure history) * (value history - excludedPayoff who)| ≤ payoffBound := by
          rw [abs_le] at excludedBounded sourceBound ⊢
          constructor <;> nlinarith
        exact (abs_sub _ _).trans (by linarith)
    have averaged := expect_mono pointwise (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)
    rw [expect_add (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _),
      expect_constant, expect_const_mul] at averaged
    have nonneg : 0 ≤ 2 * payoffBound := by linarith
    have scaled := mul_nonneg nonneg (sub_nonneg.mpr unforcedMass)
    dsimp only [belief] at averaged
    nlinarith
  have affine := abs_expect_affine_sub_le_of_decorrelated belief
    (fun history => operationalRecord setup leaks bounds horizon (NativeScheduler) history.1.trace)
    (fun history => nativeDecodedState setup leaks history.1.state) decorrelated failure result
      value
    lumped valueOf (excludedPayoff who)
    (fun history => by have := failureUnit history; rw [abs_le]; constructor <;> linarith)
    (fun record => by have := lumpedUnit record; rw [abs_le]; constructor <;> linarith)
    valueBounded valueEq excludedBounded failureNear payoffNear
  have failureEq : localFailure (2 * horizon + 1) target site
      {final | DecisionFailed key final.state} law = expect belief failure := by
    unfold localFailure
    rw [expect_localRun]
    rfl
  rw [failureEq]
  exact affine

open Classical in
/-- The original common posterior has a uniformly vanishing affine keyed-value error. -/
theorem nativeComparison_keyed_value_bounds [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    [Finite setup.intendedProtocol.History]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependent)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slots_pos : 0 < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount p))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (payoffBound : ℝ) (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound) :
    ∃ (failureScore : ℕ → LateKey setup leaks → LateOption bounds.candidateCount → ℝ)
      (error : ℕ → ℝ), Tendsto error atTop (nhds 0) ∧
      (∀ n key option, 0 ≤ failureScore n key option ∧ failureScore n key option ≤ 1) ∧
      ∀ n who (site : (N).InformationSite who),
        ¬ Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ¬ Vegas.OwingAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ownedKeyed (Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler))
          (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon (NativeScheduler))
          ((N).agentAt site) →
        ∀ key, lateKey setup leaks who site.1 = some key → ∀ option,
        let target := nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
          positive le_one weights n
        let certificate := ((NMenu).bounded (initialLaw setup) horizon
          (NativeScheduler)).wellFoundedHistories
        let law := onePacketLate setup leaks bounds horizon (NativeScheduler) sequence scale
          positive
          le_one n ((N).agentAt site) option
        let installed := Profile.update (sig := (N).behavioralSignature) target.strategy who
          ((target.strategy who).withLaw site.1 law)
        let stopped := fun final : (NP).History => ¬ ClearState final.state ∨
          DecodedState setup leaks (failureProfile setup.program)
            (ProtocolState.OwesFailure who setup.program) final.state
        |expect (target.belief who site) (fun history =>
            expect ((N).runBehavioralUntil certificate installed stopped history.1)
              (fun final => if stopped final then excludedPayoff who else
                exclusionBase setup parameter utility excludedPayoff leaks final.state who)) -
          (excludedPayoff who + (1 - failureScore n key option) *
            (siteValue setup leaks bounds horizon (NativeScheduler) parameter utility excludedPayoff
              target (setup.intendedOpeningProfile (sequence n).strategy) site - excludedPayoff
                who))| ≤
          error n := by
  let inputs := nativeBaseInputs setup leaks bounds horizon scheduler wellFormed independent
    sequence sourceMixed covers coversInputs capacity slots_pos
  have sameScale : scale = inputs.scale := funext scaleEq
  subst scale
  let target := nativeComparisonSequence setup leaks bounds horizon scheduler sequence inputs.scale
    positive le_one weights
  have assembled := nativeComparisonSequence_assembled setup leaks bounds horizon scheduler sequence
    inputs.scale positive le_one weights
  have mixed := nativeComparisonSequence_fullyMixed setup leaks bounds horizon scheduler sequence
    inputs.scale positive le_one weights
  have bayes := nativeComparisonSequence_bayes setup leaks bounds horizon scheduler sequence
    inputs.scale positive le_one weights
  obtain ⟨unforced, unforcedLimit, unforcedBound⟩ := inputs.lateUnforced setup leaks bounds horizon
    (NativeScheduler) wellFormed
    (fun n => nativeComparisonWeights setup leaks bounds horizon scheduler (weights n))
    target assembled mixed bayes
  obtain ⟨gamma, gammaLimit, decorrelated⟩ := inputs.lateDecorrelated setup leaks bounds horizon
    (NativeScheduler) wellFormed sourceMixed
    (fun n => nativeComparisonWeights setup leaks bounds horizon scheduler (weights n))
    target assembled mixed bayes
  obtain ⟨score, scoreError, scoreLimit, scoreUnit, scoreNear⟩ :=
    nativeComparison_keyed_failure_bounds setup leaks bounds horizon scheduler wellFormed
      independent
      sequence sourceMixed inputs.scale positive le_one (fun _ => rfl) covers coversInputs capacity
      slots_pos weights
  let depth : ℝ := 2 * horizon + 1
  let path := fun n => depth * (inputs.scale n ^ 3 + inputs.scale n ^ 3)
  let row := fun n => (2 * payoffBound * (Fintype.card Player *
      (1 - slotRetention (inputs.scale n)))) * depth +
    (2 * (inputs.scale n ^ 3 + path n) * depth + inputs.scale n ^ 3 * depth) * (2 * payoffBound) +
      2 * payoffBound * (inputs.scale n ^ 3 * depth)
  let error := fun n => row n + 2 * payoffBound * |unforced n| +
    4 * payoffBound * (path n + |unforced n|) + 4 * payoffBound * |gamma n| +
      2 * payoffBound * |scoreError n|
  have cube := inputs.scale_vanishing.pow 3
  have retention := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_slotRetention inputs.scale_vanishing)
  have pathLimit : Tendsto path atTop (nhds 0) := by
    simpa [path] using (cube.add cube).const_mul depth
  have rowLimit : Tendsto row atTop (nhds 0) := by
    have first := (retention.const_mul (2 * payoffBound * Fintype.card Player)).mul_const depth
    have second := ((((cube.add pathLimit).const_mul 2).mul_const depth).add
      (cube.mul_const depth)).mul_const (2 * payoffBound)
    have third := (cube.mul_const depth).const_mul (2 * payoffBound)
    simpa [row, mul_assoc] using (first.add second).add third
  refine ⟨score, error, ?_, scoreUnit, ?_⟩
  · simpa [error] using (((rowLimit.add (unforcedLimit.abs.const_mul (2 * payoffBound))).add
      ((pathLimit.add unforcedLimit.abs).const_mul (4 * payoffBound))).add
        (gammaLimit.abs.const_mul (4 * payoffBound))).add
          (scoreLimit.abs.const_mul (2 * payoffBound))
  intro n who site notFree notOwing keyed key siteKey option targetAt certificate law installed
    stopped
  obtain ⟨past, view, event, atSite, pending, _⟩ := id keyed.1
  have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon (NativeScheduler) notOwing
  have core := nativeComparison_keyed_value_sub_le setup leaks bounds horizon scheduler wellFormed
    covers capacity sequence inputs.scale positive le_one weights n opportunity inclusion timely
    completes site keyed.1 debtFree siteKey pending atSite
      ((unforcedBound n who site notFree notOwing keyed).trans (le_abs_self _))
      ((decorrelated n who site notFree notOwing keyed).mono (le_abs_self _)) option parameter
        utility
      excludedPayoff boundNonneg (readoutBounded who) (excludedBounded who)
  let failure := localFailure (2 * horizon + 1) targetAt site
    {final | DecisionFailed key final.state} law
  let value := siteValue setup leaks bounds horizon (NativeScheduler) parameter utility
    excludedPayoff
    targetAt (setup.intendedOpeningProfile (sequence n).strategy) site
  have valueBound : |value - excludedPayoff who| ≤ 2 * payoffBound := by
    have valueBounded : |value| ≤ payoffBound := expect_abs_le_of_bounded boundNonneg
      (fun history => abs_decodedPointValue_le setup leaks bounds horizon (NativeScheduler)
        parameter utility excludedPayoff _ who _ history.1 (readoutBounded who)
        (excludedBounded who))
    exact (abs_sub _ _).trans (by linarith [excludedBounded who])
  have scoreBound : |failure - score n key option| ≤ |scoreError n| :=
    (scoreNear n who site notFree notOwing keyed key siteKey option).trans (le_abs_self _)
  have gap : |(excludedPayoff who + (1 - failure) * (value - excludedPayoff who)) -
      (excludedPayoff who + (1 - score n key option) * (value - excludedPayoff who))| ≤
      2 * payoffBound * |scoreError n| := by
    have difference : (excludedPayoff who + (1 - failure) * (value - excludedPayoff who)) -
        (excludedPayoff who + (1 - score n key option) * (value - excludedPayoff who)) =
        (score n key option - failure) * (value - excludedPayoff who) := by ring
    rw [difference, abs_mul, abs_sub_comm]
    exact (mul_le_mul scoreBound valueBound (abs_nonneg _) (by positivity)).trans
      (le_of_eq (mul_comm _ _))
  have finalBound := (abs_sub_le
    (expect (targetAt.belief who site) (fun history =>
      expect ((N).runBehavioralUntil certificate installed stopped history.1)
        (fun final => if stopped final then excludedPayoff who else
          exclusionBase setup parameter utility excludedPayoff leaks final.state who)))
    (excludedPayoff who + (1 - failure) * (value - excludedPayoff who))
    (excludedPayoff who + (1 - score n key option) * (value - excludedPayoff who))).trans
      (add_le_add core gap)
  simpa [error, row, path, depth, failure, value, Nat.cast_add, Nat.cast_mul] using finalBound

open Classical in
private theorem recovery_keyed_value_bounds_at_site [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ player, DecidableEq ((N).InfoState player)]
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
        excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who) :
    ∃ (score : ℕ → LateKey setup leaks → LateOption bounds.candidateCount → ℝ)
      (error : ℕ → ℝ), Tendsto error atTop (nhds 0) ∧
      (∀ n key option, 0 ≤ score n key option ∧ score n key option ≤ 1) ∧
      ∀ n who (site : (R).InformationSite who),
        ¬ FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ¬ OwingAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ownedKeyed (FreeAgent setup leaks bounds Initial horizon scheduler)
          (KeyedAgent setup leaks bounds Initial horizon scheduler) ((R).agentAt site) →
        ∀ {past : List (RApp).PlayerEntry} {view : (RApp).PlayerView},
        site.1 = some (past, view) → ∀ {event : (graph setup).EventId},
        view.application.1.publicView.ownTurn? who = some event →
        ∃ nativeSite : (N).InformationSite who,
          nativeSite.1 = RecoveryProjection.information (runtime setup) leaks site.1 ∧
          excludedPayoff who ≤ siteValue setup leaks bounds horizon (NativeScheduler)
            parameter utility excludedPayoff
            (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive
              le_one weights n) (setup.intendedOpeningProfile (sequence n).strategy) nativeSite ∧
          ∀ key, agentKey setup leaks bounds Initial horizon scheduler ((R).agentAt site) =
            some key → ∀ option,
          |localValue (2 * horizon + 1) (fun final => final.state)
              (recoveryExclusionBase parameter utility excludedPayoff) (assessments n) site
              (keyedComponent setup leaks bounds Initial horizon scheduler (sequence n) (scale n)
                (positive n).le (le_one n) ((R).agentAt site) option) -
            (excludedPayoff who + score n key option *
              (siteValue setup leaks bounds horizon (NativeScheduler) parameter utility
                excludedPayoff (nativeComparisonSequence setup leaks bounds horizon scheduler
                  sequence scale positive le_one weights n)
                  (setup.intendedOpeningProfile (sequence n).strategy) nativeSite -
                    excludedPayoff who))| ≤ error n := by
  obtain ⟨failureScore, physical, physicalLimit, unit, valueNear⟩ :=
    nativeComparison_keyed_value_bounds setup leaks bounds horizon scheduler wellFormed independent
      sequence sourceMixed scale positive le_one scaleEq covers coversInputs capacity slots_pos
      weights opportunity inclusion timely completes parameter utility excludedPayoff payoffBound
      nonnegative readoutBounded excludedBounded
  obtain ⟨transport, transportLimit, transported⟩ := recovery_local_value_comparison_bounds setup
    leaks bounds horizon scheduler wellFormed independent sequence sourceMixed scale positive le_one
    scaleEq covers coversInputs capacity weights assessments fallback assembled bayes opportunity
    inclusion timely certificate rawCertificate parameter utility excludedPayoff payoffBound
    nonnegative recoveryCertificate menuCertificate completes payoffBounded excludedBounded
  refine ⟨fun n key option => 1 - failureScore n key option,
    fun n => transport n + physical n, ?_, ?_, ?_⟩
  · simpa using transportLimit.add physicalLimit
  · intro n key option
    have := unit n key option
    constructor <;> linarith
  intro n who site notFree notOwing keyed past view atSite event turn
  obtain ⟨nativeSite, project, lifted, input, nativeNotFree, nativeNotOwing, _states, _belief,
    localNear⟩ := transported n who site notFree notOwing atSite turn
  have nativeKeyed : ownedKeyed
      (Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler))
      (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon (NativeScheduler))
      ((N).agentAt nativeSite) := by
    refine ⟨?_, nativeNotFree⟩
    change LateDelivery setup leaks who nativeSite.1
    rw [input]
    exact keyed.1
  have lower := (siteValue_mem_Icc setup leaks bounds horizon (NativeScheduler) parameter utility
    excludedPayoff (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
      positive le_one weights n) (setup.intendedOpeningProfile (sequence n).strategy) nativeSite
    upper (fun outcome => le_upper outcome who)
    (fun point reached => excludedPayoff_le_of_reached setup parameter utility excludedPayoff
      wellFormed below (sequence n).strategy point reached who)).1
  refine ⟨nativeSite, input, lower, ?_⟩
  intro key siteKey option
  have nativeKey : lateKey setup leaks who nativeSite.1 = some key := by
    rw [input]
    exact siteKey
  let law := keyedComponent setup leaks bounds Initial horizon scheduler (sequence n) (scale n)
    (positive n).le (le_one n) ((R).agentAt site) option
  have bridge := localNear law
  have comparison := valueNear n who nativeSite nativeNotFree nativeNotOwing nativeKeyed key
    nativeKey option
  have lawEq : (law.map (Equiv.cast
      (congrArg (fun input => (R).Choice who input) lifted.symm))).map
        (sourceNativeChoiceEquiv setup leaks bounds horizon scheduler who nativeSite.1) =
      onePacketLate setup leaks bounds horizon (NativeScheduler) sequence scale positive le_one n
        ((N).agentAt nativeSite) option := by
    rcases site with ⟨information, decision⟩
    dsimp only at lifted
    cases lifted
    change ((keyedComponent setup leaks bounds Initial horizon scheduler (sequence n) (scale n)
      (positive n).le (le_one n)
      ((R).agentAt ⟨liftInformation (runtime setup) leaks nativeSite.1, decision⟩) option).map
        id).map
        (sourceNativeChoiceEquiv setup leaks bounds horizon scheduler who nativeSite.1) = _
    rw [PMF.map_id]
    apply pmf_map_injective Subtype.val_injective
    rw [sourceNativeChoiceEquiv_map_val]
    have projected := keyedComponent_native setup leaks bounds horizon scheduler (sequence n)
      (scale n) (positive n).le (le_one n)
      ((R).agentAt ⟨liftInformation (runtime setup) leaks nativeSite.1, decision⟩)
      (clearInput_lift (runtime setup) leaks nativeSite.1) option
    rw [information_liftInformation] at projected
    exact projected
  dsimp only at bridge comparison
  rw [lawEq] at bridge
  exact (abs_sub_le _ _ _).trans (add_le_add bridge comparison)


open Classical in
private theorem keyedSite_geometry [Fintype (RP).History]
    [∀ player, DecidableEq ((R).InfoState player)] {who : Player} (site : (R).InformationSite who)
    (keyed : KeyedAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site)) :
    ∃ (past : List (RApp).PlayerEntry) (view : (RApp).PlayerView)
      (event : (graph setup).EventId) (key : LateKey setup leaks),
      site.1 = some (past, view) ∧ view.application.1.publicView.ownTurn? who = some event ∧
      agentKey setup leaks bounds Initial horizon scheduler ((R).agentAt site) = some key := by
  obtain ⟨nativePast, nativeView, event, atNative, pending, _activated⟩ := keyed
  have existsInput : ∃ input, site.1 = some input := by
    cases current : site.1 with
    | none => simp [RecoveryProjection.information, current] at atNative
    | some input => exact ⟨input, rfl⟩
  obtain ⟨⟨past, view⟩, atSite⟩ := existsInput
  have pendingAt : pendingEvent setup leaks who
      (some (past.map (playerEntry (runtime setup) leaks), playerView (runtime setup) leaks view)) =
        some event := by
    change pendingEvent setup leaks who
      (RecoveryProjection.information (runtime setup) leaks site.1) = some event at pending
    simpa only [RecoveryProjection.information, atSite, Option.map_some] using pending
  have turn := (pendingEvent_spec (setup := setup) pendingAt).1
  refine ⟨past, view, event, LateKey.ofView setup leaks who
    (past.map (playerEntry (runtime setup) leaks)) (playerView (runtime setup) leaks view),
    atSite, turn, ?_⟩
  change lateKey setup leaks who (RecoveryProjection.information (runtime setup) leaks site.1) = _
  rw [atSite]
  rfl

open Classical in
theorem recovery_keyed_component_value_bounds [Fintype (RP).History]
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
        excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who) :
    ∃ (continuation : ℕ → (R).InformationAgent (R).playedInformation → ℝ)
      (score : ℕ → Option (LateKey setup leaks) → LateOption bounds.candidateCount → ℝ)
      (error : ℕ → ℝ), Tendsto error atTop (nhds 0) ∧
      (∀ n key option, 0 ≤ score n key option ∧ score n key option ≤ 1) ∧
      ∀ n (agent : (R).InformationAgent (R).playedInformation),
        ownedKeyed (FreeAgent setup leaks bounds Initial horizon scheduler)
          (KeyedAgent setup leaks bounds Initial horizon scheduler) agent →
        ¬ OwingAgent setup leaks bounds Initial horizon scheduler agent →
        ∀ decision : (R).IsDecisionInfo agent.1 agent.2.1,
          excludedPayoff agent.1 ≤ continuation n agent ∧ ∀ option,
          |localValue (2 * horizon + 1) (fun final => final.state)
              (recoveryExclusionBase parameter utility excludedPayoff) (assessments n)
              (who := agent.1) ⟨agent.2.1, decision⟩
              (keyedComponent setup leaks bounds Initial horizon scheduler (sequence n) (scale n)
                (positive n).le (le_one n) agent option) -
            (excludedPayoff agent.1 + score n
              (agentKey setup leaks bounds Initial horizon scheduler agent) option *
                (continuation n agent - excludedPayoff agent.1))| ≤ error n := by
  obtain ⟨score, error, limit, unit, bounded⟩ := recovery_keyed_value_bounds_at_site setup leaks
    bounds horizon scheduler wellFormed independent sequence sourceMixed scale positive le_one
      scaleEq
    covers coversInputs capacity weights assessments fallback assembled bayes opportunity inclusion
    timely certificate rawCertificate parameter utility excludedPayoff payoffBound nonnegative
    recoveryCertificate menuCertificate completes payoffBounded excludedBounded slots_pos
    readoutBounded upper le_upper below
  let continuation := fun n (agent : (R).InformationAgent (R).playedInformation) =>
    if decision : (N).IsDecisionInfo agent.1
        (RecoveryProjection.information (runtime setup) leaks agent.2.1) then
      siteValue setup leaks bounds horizon (NativeScheduler) parameter utility excludedPayoff
        (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive
          le_one
          weights n) (setup.intendedOpeningProfile (sequence n).strategy)
        ⟨RecoveryProjection.information (runtime setup) leaks agent.2.1, decision⟩
    else excludedPayoff agent.1
  refine ⟨continuation, fun n key option => key.elim 0 (fun key => score n key option),
    error, limit, ?_, ?_⟩
  · intro n key option
    cases key with
    | none => exact ⟨le_rfl, zero_le_one⟩
    | some key => exact unit n key option
  intro n agent keyed notOwing decision
  let site : (R).InformationSite agent.1 := ⟨agent.2.1, decision⟩
  have agentEq : (R).agentAt site = agent := by cases agent; rfl
  obtain ⟨past, view, event, key, atSite, turn, siteKey⟩ :=
    keyedSite_geometry setup leaks bounds horizon scheduler site keyed.1
  obtain ⟨nativeSite, input, lower, values⟩ :=
    bounded n agent.1 site keyed.2 notOwing keyed atSite turn
  have nativeDecision : (N).IsDecisionInfo agent.1
      (RecoveryProjection.information (runtime setup) leaks agent.2.1) := input ▸ nativeSite.2
  have nativeSiteEq : (⟨RecoveryProjection.information (runtime setup) leaks agent.2.1,
      nativeDecision⟩ : (N).InformationSite agent.1) = nativeSite := Subtype.ext input.symm
  have valueEq : continuation n agent = siteValue setup leaks bounds horizon (NativeScheduler)
      parameter utility excludedPayoff
      (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive le_one
        weights n) (setup.intendedOpeningProfile (sequence n).strategy) nativeSite := by
    dsimp only [continuation]
    rw [dite_eq_left nativeDecision, nativeSiteEq]
  refine ⟨by rw [valueEq]; exact lower, ?_⟩
  intro option
  have keyEq : agentKey setup leaks bounds Initial horizon scheduler agent = some key := by
    simpa only [agentEq] using siteKey
  simpa only [agentEq, keyEq, Option.elim_some, valueEq] using values key siteKey option

end Vegas.RecoveryOnePacket
