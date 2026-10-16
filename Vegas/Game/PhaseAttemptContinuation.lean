/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseLocalValueContinuation
import Vegas.Game.PhaseContinuationFloor
import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound

/-! # Actual local values through physical attempt exits and retries -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (menu : (phaseApplication runtime leaks).ResponseMenu)
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "P" => phaseApplication runtime leaks
local notation "M" => menu.information initial horizon scheduler
local notation "E" => menu.protocol initial horizon scheduler

omit [Fintype Player] in
/-- Stop when the focal player is permanently excluded or the original
physical attempt has ended. The existing stopped runner also stops at a
terminal history. -/
def PhaseAttemptExit (who : Player) (attempt : CommitAttemptId) : (P).ProtocolState → Prop
  | none => False
  | some control => who ∈ control.execution.application.current.excluded ∨
      control.execution.application.attempt ≠ attempt

omit [Fintype Player] in
/-- A retry boundary retains a surviving focal player and a changed attempt
generation. It does not assert that the continuation pays the exclusion floor. -/
def PhaseSurvivingRetry (who : Player) (attempt : CommitAttemptId) : (P).ProtocolState → Prop
  | none => False
  | some control => who ∉ control.execution.application.current.excluded ∧
      control.execution.application.generation ≠ attempt.generation

omit [Fintype Player] in
private theorem retry_not_excluded (who : Player) (attempt : CommitAttemptId)
    (state : (P).ProtocolState) (retry : PhaseSurvivingRetry setup mode runtime leaks who
      attempt state) : ¬ PhaseExcluded setup mode runtime leaks who state := by
  cases state with
  | none => exact retry.elim
  | some control => exact retry.1

open Classical in
/-- The original assessment fiber follows the existing actual local runner
until focal exclusion or the end of this attempt. No source or terminal
probability law is supplied. -/
def phaseLocalAttemptBoundary (assessment : (M).BehavioralAssessment)
    (who : Player) (site : (M).InformationSite who) (law : PMF ((M).Choice who site.1))
    (attempt : CommitAttemptId) : PMF (E).History :=
  (assessment.belief who site).bind fun history =>
    (M).runBehavioralUntil ((menu).bounded initial horizon scheduler).wellFoundedHistories
      (Profile.update (sig := (M).behavioralSignature) assessment.strategy who
        ((assessment.strategy who).withLaw site.1 law))
      (fun stop => PhaseAttemptExit setup mode runtime leaks who attempt stop.state) history.1

/-- Every boundary in the actual local assessment fiber has reached the
physical attempt exit or the existing terminal condition. -/
theorem phaseLocalAttemptBoundary_support (assessment : (M).BehavioralAssessment)
    (who : Player) (site : (M).InformationSite who) (law : PMF ((M).Choice who site.1))
    (attempt : CommitAttemptId) (stop : (E).History)
    (supported : stop ∈ (phaseLocalAttemptBoundary setup mode runtime leaks menu initial horizon
      scheduler assessment who site law attempt).support) :
    PhaseAttemptExit setup mode runtime leaks who attempt stop.state ∨ (E).terminal stop.state := by
  classical
  unfold phaseLocalAttemptBoundary at supported
  rw [PMF.mem_support_bind_iff] at supported
  obtain ⟨history, _prior, member⟩ := supported
  exact (M).mem_support_runBehavioralUntil _ _ _ history.1 stop member

open Classical in
/-- The entire actual terminal continuation after the installed local law.
In particular this retains the real retry continuation, all later callbacks
and the same common assessment policy. -/
def phaseLocalBoundaryValue (assessment : (M).BehavioralAssessment)
    (who : Player) (site : (M).InformationSite who) (law : PMF ((M).Choice who site.1))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (history : (E).History) : ℝ :=
  expect ((M).runBehavioralTerminalFrom
    ((menu).bounded initial horizon scheduler).wellFoundedHistories
    (Profile.update (sig := (M).behavioralSignature) assessment.strategy who
      ((assessment.strategy who).withLaw site.1 law)) history)
    (fun final => phaseExclusionBase setup mode runtime leaks utility excludedPayoff final.state
      who)

open Classical in
/-- The original local terminal law factors through the actual attempt exit.
This is the checked stopping tower for the same runner, not a replacement
evaluator or a source-law assumption. -/
theorem phase_localRun_eq_attempt_boundary (assessment : (M).BehavioralAssessment)
    (who : Player) (site : (M).InformationSite who) (law : PMF ((M).Choice who site.1))
    (attempt : CommitAttemptId) :
    localRun (2 * horizon + 1) assessment site law =
      (phaseLocalAttemptBoundary setup mode runtime leaks menu initial horizon scheduler assessment
        who site law attempt).bind
        ((M).runBehavioralTerminalFrom ((menu).bounded initial horizon
          scheduler).wellFoundedHistories
          (Profile.update (sig := (M).behavioralSignature) assessment.strategy who
            ((assessment.strategy who).withLaw site.1 law))) := by
  rw [localRun_eq_bind]
  unfold phaseLocalAttemptBoundary
  rw [PMF.bind_bind]
  apply bind_congr_on_support
  intro history _supported
  change (M).runBehavioralFrom _ (2 * horizon + 1) history.1 = _
  rw [← (M).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    ((menu).bounded initial horizon scheduler).wellFoundedHistories
    ((menu).bounded initial horizon scheduler)]
  exact (M).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil _ _ _ history.1

omit [Fintype Player] in
private theorem base_bounded
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (who : Player) (B : ℝ) (nonnegative : 0 ≤ B)
    (utilityBound : ∀ terminal owner, |utility terminal owner| ≤ B)
    (excludedBound : |excludedPayoff who| ≤ B) :
    ∀ state, |phaseExclusionBase setup mode runtime leaks utility excludedPayoff state who| ≤ B :=
      by
  intro state
  have interval := phaseExclusionBase_mem_Icc setup mode runtime leaks utility excludedPayoff
    (fun _ => -B) (fun _ => B) (fun terminal owner => (abs_le.mp
      (utilityBound terminal owner)).1)
    (fun terminal owner => (abs_le.mp (utilityBound terminal owner)).2) state who
  have excludedLower := (abs_le.mp excludedBound).1
  have excludedUpper := (abs_le.mp excludedBound).2
  apply abs_le.mpr
  simpa only [min_eq_right excludedLower, min_eq_right (neg_nonpos.mpr nonnegative),
    max_eq_right excludedUpper, max_eq_right nonnegative, Set.mem_Icc] using interval

theorem phaseLocalBoundaryValue_bounded (assessment : (M).BehavioralAssessment)
    (who : Player) (site : (M).InformationSite who) (law : PMF ((M).Choice who site.1))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (B : ℝ) (nonnegative : 0 ≤ B)
    (utilityBound : ∀ terminal owner, |utility terminal owner| ≤ B)
    (excludedBound : |excludedPayoff who| ≤ B) (history : (E).History) :
    |phaseLocalBoundaryValue setup mode runtime leaks menu initial horizon scheduler assessment who
      site law utility excludedPayoff history| ≤ B := by
  apply expect_abs_le_of_bounded nonnegative
  intro final
  exact base_bounded setup mode runtime leaks utility excludedPayoff who B nonnegative utilityBound
    excludedBound final.state

theorem phaseLocalBoundaryValue_of_excluded (assessment : (M).BehavioralAssessment)
    (who : Player) (site : (M).InformationSite who) (law : PMF ((M).Choice who site.1))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (history : (E).History) (excluded : PhaseExcluded setup mode runtime leaks who history.state) :
    phaseLocalBoundaryValue setup mode runtime leaks menu initial horizon scheduler assessment who
      site law utility excludedPayoff history = excludedPayoff who :=
  phase_excluded_expected_payoff setup mode runtime leaks utility excludedPayoff menu initial
    horizon scheduler ((menu).bounded initial horizon scheduler).wellFoundedHistories _ who history
      excluded

open Classical in
/-- The exact local value retains separate surviving-retry and remaining
continuation contributions. Only permanent focal exclusion is replaced by
its actual fixed payoff. No retry value or probability is identified with a
source reference or assumed independent of the selected option. -/
theorem phase_localValue_eq_attempt_contributions
    (assessment : (M).BehavioralAssessment) (who : Player) (site : (M).InformationSite who)
    (law : PMF ((M).Choice who site.1)) (attempt : CommitAttemptId)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (B : ℝ) (nonnegative : 0 ≤ B)
    (utilityBound : ∀ terminal owner, |utility terminal owner| ≤ B)
    (excludedBound : |excludedPayoff who| ≤ B) :
    let boundary := phaseLocalAttemptBoundary setup mode runtime leaks menu initial horizon
      scheduler
      assessment who site law attempt
    let value := phaseLocalBoundaryValue setup mode runtime leaks menu initial horizon scheduler
      assessment who site law utility excludedPayoff
    localValue (2 * horizon + 1) (fun final : (E).History => final.state)
      (phaseExclusionBase setup mode runtime leaks utility excludedPayoff) assessment site law =
      excludedPayoff who +
        expect boundary (fun stop => if PhaseSurvivingRetry setup mode runtime leaks who attempt
          stop.state then value stop - excludedPayoff who else 0) +
        expect boundary (fun stop => if PhaseExcluded setup mode runtime leaks who stop.state then 0
          else if PhaseSurvivingRetry setup mode runtime leaks who attempt stop.state then 0
          else value stop - excludedPayoff who) := by
  classical
  intro boundary value
  let retry := fun stop : (E).History => if PhaseSurvivingRetry setup mode runtime leaks who attempt
    stop.state then value stop - excludedPayoff who else 0
  let remaining := fun stop : (E).History =>
    if PhaseExcluded setup mode runtime leaks who stop.state then 0
    else if PhaseSurvivingRetry setup mode runtime leaks who attempt stop.state then 0
    else value stop - excludedPayoff who
  have valueBound := phaseLocalBoundaryValue_bounded setup mode runtime leaks menu initial horizon
    scheduler assessment who site law utility excludedPayoff B nonnegative utilityBound
      excludedBound
  have gap (stop : (E).History) : |value stop - excludedPayoff who| ≤ 2 * B := by
    exact (abs_sub _ _).trans (by linarith [valueBound stop])
  have retryBound (stop : (E).History) : |retry stop| ≤ 2 * B := by
    dsimp only [retry]
    split
    · exact gap stop
    · simpa only [abs_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) nonnegative
  have remainingBound (stop : (E).History) : |remaining stop| ≤ 2 * B := by
    dsimp only [remaining]
    split
    · simpa only [abs_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) nonnegative
    · split
      · simpa only [abs_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) nonnegative
      · exact gap stop
  have splitValue (stop : (E).History) :
      value stop = excludedPayoff who + retry stop + remaining stop := by
    by_cases excluded : PhaseExcluded setup mode runtime leaks who stop.state
    · have fixed := phaseLocalBoundaryValue_of_excluded setup mode runtime leaks menu initial
        horizon scheduler assessment who site law utility excludedPayoff stop excluded
      have noRetry := retry_not_excluded setup mode runtime leaks who attempt stop.state
      simp only [retry, remaining, ite_eq_left excluded,
        ite_eq_right (fun reached => noRetry reached excluded)]
      exact (show value stop = excludedPayoff who from fixed).trans (by ring)
    · by_cases retried : PhaseSurvivingRetry setup mode runtime leaks who attempt stop.state
      · simp only [retry, remaining, ite_eq_left retried, ite_eq_right excluded]
        ring
      · simp only [retry, remaining, ite_eq_right retried, ite_eq_right excluded]
        ring
  rw [localValue_eq_expect_localRun,
    phase_localRun_eq_attempt_boundary setup mode runtime leaks menu initial horizon scheduler
      assessment who site law attempt]
  rw [expect_bind_tower_bounded _ _
    (fun final : (E).History =>
      phaseExclusionBase setup mode runtime leaks utility excludedPayoff final.state who)
    (fun final => base_bounded setup mode runtime leaks utility excludedPayoff who B nonnegative
      utilityBound excludedBound final.state)]
  change expect boundary value = _
  rw [expect_congr_on_support (g := fun stop => excludedPayoff who + retry stop + remaining stop)
    (fun stop _ => splitValue stop)]
  rw [expect_add (payoffIntegrable_add (payoffIntegrable_constant boundary (excludedPayoff who))
      (payoffIntegrable_of_bounded boundary retry retryBound))
      (payoffIntegrable_of_bounded boundary remaining remainingBound),
    expect_add (payoffIntegrable_constant boundary (excludedPayoff who))
      (payoffIntegrable_of_bounded boundary retry retryBound), expect_constant]

open Classical in
/-- The actual full retry contribution is controlled by its actual boundary
probability. This does not assume that the probability vanishes or that the
retry value is constant across timing options or information agents. -/
theorem phase_local_retry_contribution_bound
    (assessment : (M).BehavioralAssessment) (who : Player) (site : (M).InformationSite who)
    (law : PMF ((M).Choice who site.1)) (attempt : CommitAttemptId)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (B : ℝ) (nonnegative : 0 ≤ B)
    (utilityBound : ∀ terminal owner, |utility terminal owner| ≤ B)
    (excludedBound : |excludedPayoff who| ≤ B) :
    let boundary := phaseLocalAttemptBoundary setup mode runtime leaks menu initial horizon
      scheduler
      assessment who site law attempt
    let value := phaseLocalBoundaryValue setup mode runtime leaks menu initial horizon scheduler
      assessment who site law utility excludedPayoff
    |expect boundary (fun stop => if PhaseSurvivingRetry setup mode runtime leaks who attempt
      stop.state then value stop - excludedPayoff who else 0)| ≤
      2 * B * expect boundary (fun stop =>
        if PhaseSurvivingRetry setup mode runtime leaks who attempt stop.state then 1 else 0) := by
  classical
  intro boundary value
  let retry := fun stop : (E).History => if PhaseSurvivingRetry setup mode runtime leaks who attempt
    stop.state then value stop - excludedPayoff who else 0
  let indicator := fun stop : (E).History =>
    if PhaseSurvivingRetry setup mode runtime leaks who attempt stop.state then (1 : ℝ) else 0
  have valueBound := phaseLocalBoundaryValue_bounded setup mode runtime leaks menu initial horizon
    scheduler assessment who site law utility excludedPayoff B nonnegative utilityBound
      excludedBound
  have point (stop : (E).History) : |retry stop| ≤ 2 * B * indicator stop := by
    dsimp only [retry, indicator]
    split
    · simp only [mul_one]
      exact (abs_sub _ _).trans (by linarith [valueBound stop])
    · simp only [abs_zero, mul_zero, le_refl]
  have retryInt : PayoffIntegrable boundary retry :=
    payoffIntegrable_of_bounded boundary retry (C := 2 * B) (fun stop => by
      have unit : indicator stop ≤ 1 := by dsimp only [indicator]; split <;> norm_num
      exact (point stop).trans (by nlinarith))
  have indicatorInt : PayoffIntegrable boundary indicator :=
    payoffIntegrable_of_bounded boundary indicator (C := 1) (fun stop => by
      dsimp only [indicator]; split <;> norm_num)
  have upper := expect_mono (μ := boundary) (fun stop _ => (le_abs_self _).trans (point stop))
    retryInt (payoffIntegrable_const_mul indicatorInt)
  have lower := expect_mono (μ := boundary)
    (fun stop _ => (neg_le_neg (point stop)).trans (neg_abs_le _))
    (payoffIntegrable_neg (payoffIntegrable_const_mul indicatorInt)) retryInt
  rw [expect_const_mul] at upper
  rw [expect_neg, expect_const_mul] at lower
  exact abs_le.mpr ⟨lower, upper⟩

end Vegas
