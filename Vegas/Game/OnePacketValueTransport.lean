/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCommitmentCompletion
import Vegas.Game.IntendedCommitGain
import Vegas.Game.OnePacketForcedRegular

/-! # Payoff-range bounds and regular histories

**Gains are bounded by the payoff range.** With every utility between a lower
and an upper bound, the exclusion payoff of every readout is bounded by the
payoff range (`Vegas.abs_exclusionReadoutUtility_le`), and the gain of every
deviation at every history is at most twice the payoff range in absolute
value, in the one-packet game (`Vegas.abs_onePacket_historyGain_le`) and in the
intended game (`Vegas.abs_intended_historyGain_le`).

**Regular histories owe nothing.** At a forced site, a regular history along
which the owner's own completions are intended decodes to a point at which no
player owes a failure (`Vegas.not_owesFailure_of_regular`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

omit [Fintype Player] in
/-- The exclusion payoff of every readout is bounded in absolute value by the
payoff range. -/
theorem abs_exclusionReadoutUtility_le (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (readout : Option (State L setup.program.terminalCtx)) (who : Player) :
    |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤
      max 0 (max (excludedPayoff who) (upperUtility who)) -
        min 0 (min (excludedPayoff who) (lowerUtility who)) := by
  have within := exclusionReadoutUtility_mem_Icc setup parameter utility excludedPayoff
    lowerUtility upperUtility lower_le le_upper readout who
  have lowNonpos : min 0 (min (excludedPayoff who) (lowerUtility who)) ≤ 0 := min_le_left _ _
  have highNonneg : 0 ≤ max 0 (max (excludedPayoff who) (upperUtility who)) := le_max_left _ _
  exact abs_le.mpr ⟨by linarith [within.1], by linarith [within.2]⟩

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **Native gains are bounded by the payoff range.** -/
theorem abs_onePacket_historyGain_le (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (assessment : (onePacketN).BehavioralAssessment) {who : Player}
    (deviation : (onePacketN).AssessmentDeviation who)
    (history : (onePacketN).InformationHistory who deviation.1.1) :
    |(onePacketN).historyGain ((onePacketN).truncatedRunner (2 * horizon + 1))
        (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
          utility excludedPayoff) (payoffComponent setup) assessment deviation history| ≤
      2 * (max 0 (max (excludedPayoff who) (upperUtility who)) -
        min 0 (min (excludedPayoff who) (lowerUtility who))) := by
  have each : ∀ final, |payoffComponent setup (readoutExclusion setup leaks bounds
      (initialLaw setup) horizon scheduler parameter utility excludedPayoff final) who| ≤
      max 0 (max (excludedPayoff who) (upperUtility who)) -
        min 0 (min (excludedPayoff who) (lowerUtility who)) := fun final =>
    abs_exclusionReadoutUtility_le setup parameter utility excludedPayoff lowerUtility
      upperUtility lower_le le_upper _ who
  have rangeNonneg := (abs_nonneg _).trans (each history.1)
  unfold InformationModel.historyGain
  rw [expect_map, expect_map]
  simp only [Function.comp_def]
  have first := expect_abs_le_of_bounded (μ := ((onePacketN).truncatedRunner (2 * horizon + 1)
    (Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy who
      deviation.2) history.1)) rangeNonneg each
  have second := expect_abs_le_of_bounded (μ := ((onePacketN).truncatedRunner (2 * horizon + 1)
    (Profile.update (sig := (onePacketN).behavioralSignature) assessment.strategy who
      (assessment.strategy who)) history.1)) rangeNonneg each
  have firstBounds := abs_le.mp first
  have secondBounds := abs_le.mp second
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [Fintype Player] in
/-- **Intended gains are bounded by the payoff range.** -/
theorem abs_intended_historyGain_le [Fintype Player] (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (assessment : setup.intendedModel.BehavioralAssessment) {who : Player}
    (deviation : setup.intendedModel.AssessmentDeviation who)
    (history : setup.intendedModel.InformationHistory who deviation.1.1) :
    |setup.intendedModel.historyGain
        (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
        (intendedReadoutExclusion setup parameter utility excludedPayoff) (payoffComponent setup)
        assessment deviation history| ≤
      2 * (max 0 (max (excludedPayoff who) (upperUtility who)) -
        min 0 (min (excludedPayoff who) (lowerUtility who))) := by
  have each : ∀ final, |payoffComponent setup (intendedReadoutExclusion setup parameter utility
      excludedPayoff final) who| ≤
      max 0 (max (excludedPayoff who) (upperUtility who)) -
        min 0 (min (excludedPayoff who) (lowerUtility who)) := fun final =>
    abs_exclusionReadoutUtility_le setup parameter utility excludedPayoff lowerUtility
      upperUtility lower_le le_upper _ who
  have rangeNonneg := (abs_nonneg _).trans (each history.1)
  unfold InformationModel.historyGain
  rw [expect_map, expect_map]
  simp only [Function.comp_def]
  have first := expect_abs_le_of_bounded (μ := (setup.intendedModel.truncatedRunner
    (instructionCount setup.program + 1) (Profile.update
      (sig := setup.intendedModel.behavioralSignature) assessment.strategy who deviation.2)
      history.1)) rangeNonneg each
  have second := expect_abs_le_of_bounded (μ := (setup.intendedModel.truncatedRunner
    (instructionCount setup.program + 1) (Profile.update
      (sig := setup.intendedModel.behavioralSignature) assessment.strategy who
      (assessment.strategy who)) history.1)) rangeNonneg each
  have firstBounds := abs_le.mp first
  have secondBounds := abs_le.mp second
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable {setup leaks bounds horizon scheduler} in
omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **Regular histories owe nothing.** For a well-formed setup, at a forced
decision site of who, a regular history along which who's own completions decode
to intended actions decodes to a point at which no player owes a failure. -/
theorem not_owesFailure_of_regular (wellFormed : setup.WellFormed)
    (assessment : setup.intendedModel.BehavioralAssessment) {who : Player}
    {site : (onePacketN).InformationSite who} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler who site.1)
    (history : (onePacketN).InformationHistory who site.1)
    (regular : RegularTrace setup leaks bounds horizon scheduler assessment who history.1.trace)
    (ownIntended : OwnCompletionsIntended (bounds := bounds) (horizon := horizon)
      (scheduler := scheduler) who history.1.trace) :
    ∀ point, nativeDecodedState setup leaks history.1.state = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point := by
  intro point decodedState player
  have forcedState := forcedState_of_regular wellFormed assessment atSite forced history regular
    ownIntended
  cases state : history.1.state with
  | none =>
      rw [state] at decodedState
      cases decodedState
  | some control =>
      rw [state] at forcedState decodedState
      have record := publicRecord_of_forced who history.1.trace control state forcedState
      obtain ⟨found, foundDecoded, intendedFound⟩ := intended_of_regular wellFormed assessment who
        history.1.trace control state record regular ownIntended
      change decodedPoint setup control.execution.application.config = some point at decodedState
      rw [foundDecoded, Option.some.injEq] at decodedState
      subst decodedState
      exact ProtocolState.Intended.not_owesFailure player setup.program found intendedFound

end Vegas
