/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseAttemptContinuation

/-! # Unilateral gains with their full surviving-retry contribution -/

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

variable
  (assessment : (ReactiveApplication.ResponseMenu.information menu initial horizon
    scheduler).BehavioralAssessment) (who : Player)
  (site : (ReactiveApplication.ResponseMenu.information menu initial horizon
    scheduler).InformationSite who)
  (attempt : CommitAttemptId)
  (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)

open Classical in
/-- The actual excess terminal payoff carried by a surviving retry, with the
original information fiber, local deviation and full continuation retained. -/
def phaseLocalRetryPayoff (law : PMF ((M).Choice who site.1)) : ℝ :=
  expect (phaseLocalAttemptBoundary setup mode runtime leaks menu initial horizon scheduler
    assessment who site law attempt) fun stop =>
      if PhaseSurvivingRetry setup mode runtime leaks who attempt stop.state then
        phaseLocalBoundaryValue setup mode runtime leaks menu initial horizon scheduler assessment
          who site law utility excludedPayoff stop - excludedPayoff who
      else 0

open Classical in
/-- The complementary excess terminal payoff at the actual attempt boundary,
zero on permanent focal exclusion and on surviving retries. -/
def phaseLocalNonretryPayoff (law : PMF ((M).Choice who site.1)) : ℝ :=
  expect (phaseLocalAttemptBoundary setup mode runtime leaks menu initial horizon scheduler
    assessment who site law attempt) fun stop =>
      if PhaseExcluded setup mode runtime leaks who stop.state then 0
      else if PhaseSurvivingRetry setup mode runtime leaks who attempt stop.state then 0
      else phaseLocalBoundaryValue setup mode runtime leaks menu initial horizon scheduler
        assessment who site law utility excludedPayoff stop - excludedPayoff who

open Classical in
/-- The surviving-retry probability under the same actual local deviation. -/
def phaseLocalRetryProbability (law : PMF ((M).Choice who site.1)) : ℝ :=
  expect (phaseLocalAttemptBoundary setup mode runtime leaks menu initial horizon scheduler
    assessment who site law attempt) fun stop =>
      if PhaseSurvivingRetry setup mode runtime leaks who attempt stop.state then 1 else 0

variable (B : ℝ) (nonnegative : 0 ≤ B)
  (utilityBound : ∀ terminal owner, |utility terminal owner| ≤ B)
  (excludedBound : |excludedPayoff who| ≤ B)

include nonnegative utilityBound excludedBound in
open Classical in
/-- An actual unilateral gain separates the change in surviving-reset payoff
from the remaining boundary payoff change. Neither reset law nor its value
is assumed common across local choices or pooled information agents. -/
theorem phase_localGain_eq_attempt_difference (law : PMF ((M).Choice who site.1)) :
    localGain (2 * horizon + 1) (fun final : (E).History => final.state)
      (phaseExclusionBase setup mode runtime leaks utility excludedPayoff) assessment site law =
      (phaseLocalRetryPayoff setup mode runtime leaks menu initial horizon scheduler assessment who
        site attempt utility excludedPayoff law -
        phaseLocalRetryPayoff setup mode runtime leaks menu initial horizon scheduler assessment who
          site attempt utility excludedPayoff (assessment.strategy who site.1)) +
      (phaseLocalNonretryPayoff setup mode runtime leaks menu initial horizon scheduler assessment
        who site attempt utility excludedPayoff law -
        phaseLocalNonretryPayoff setup mode runtime leaks menu initial horizon scheduler assessment
          who site attempt utility excludedPayoff (assessment.strategy who site.1)) := by
  rw [localGain_eq_sub]
  rw [phase_localValue_eq_attempt_contributions setup mode runtime leaks menu initial horizon
    scheduler assessment who site law attempt utility excludedPayoff B nonnegative utilityBound
      excludedBound,
    phase_localValue_eq_attempt_contributions setup mode runtime leaks menu initial horizon
      scheduler
      assessment who site (assessment.strategy who site.1) attempt utility excludedPayoff B
        nonnegative utilityBound excludedBound]
  change excludedPayoff who +
      phaseLocalRetryPayoff setup mode runtime leaks menu initial horizon scheduler assessment who
        site attempt utility excludedPayoff law +
      phaseLocalNonretryPayoff setup mode runtime leaks menu initial horizon scheduler assessment
        who site attempt utility excludedPayoff law - _ = _
  dsimp only [phaseLocalRetryPayoff, phaseLocalNonretryPayoff]
  ring

include nonnegative utilityBound excludedBound in
open Classical in
/-- The discarded reset term in a unilateral comparison is controlled by the
TWO actual surviving-retry probabilities. No vanishing claim or replacement
by a fixed exclusion payoff is used. -/
theorem phase_localGain_sub_nonretry_difference_bound
    (law : PMF ((M).Choice who site.1)) :
    |localGain (2 * horizon + 1) (fun final : (E).History => final.state)
      (phaseExclusionBase setup mode runtime leaks utility excludedPayoff) assessment site law -
      (phaseLocalNonretryPayoff setup mode runtime leaks menu initial horizon scheduler assessment
        who site attempt utility excludedPayoff law -
        phaseLocalNonretryPayoff setup mode runtime leaks menu initial horizon scheduler assessment
          who site attempt utility excludedPayoff (assessment.strategy who site.1))| ≤
      2 * B *
        (phaseLocalRetryProbability setup mode runtime leaks menu initial horizon scheduler
          assessment who site attempt law +
        phaseLocalRetryProbability setup mode runtime leaks menu initial horizon scheduler
          assessment
          who site attempt (assessment.strategy who site.1)) := by
  have changed := phase_local_retry_contribution_bound setup mode runtime leaks menu initial horizon
    scheduler assessment who site law attempt utility excludedPayoff B nonnegative utilityBound
      excludedBound
  have original := phase_local_retry_contribution_bound setup mode runtime leaks menu initial
    horizon scheduler assessment who site (assessment.strategy who site.1) attempt utility
      excludedPayoff B nonnegative utilityBound excludedBound
  change |phaseLocalRetryPayoff setup mode runtime leaks menu initial horizon scheduler assessment
    who site attempt utility excludedPayoff law| ≤
    2 * B * phaseLocalRetryProbability setup mode runtime leaks menu initial horizon scheduler
      assessment who site attempt law at changed
  change |phaseLocalRetryPayoff setup mode runtime leaks menu initial horizon scheduler assessment
    who site attempt utility excludedPayoff (assessment.strategy who site.1)| ≤
    2 * B * phaseLocalRetryProbability setup mode runtime leaks menu initial horizon scheduler
      assessment who site attempt (assessment.strategy who site.1) at original
  rw [phase_localGain_eq_attempt_difference setup mode runtime leaks menu initial horizon scheduler
    assessment who site attempt utility excludedPayoff B nonnegative utilityBound excludedBound law]
  rw [add_sub_cancel_right]
  exact (abs_sub _ _).trans (by linarith)

end Vegas
