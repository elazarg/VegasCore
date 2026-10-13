/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCommitmentGain
import Vegas.Game.OnePacketForcedRegular

/-! # Value transport of intended commitments in belief

**Gains are bounded by the payoff range.** With every utility between a lower
and an upper bound, the gain of every deviation at every history is at most
twice the payoff range in absolute value, in the one-packet game
(`Vegas.abs_onePacket_historyGain_le`) and in the intended game
(`Vegas.abs_intended_historyGain_le`).

**Regular histories owe nothing.** At a forced site, a regular history along
which the owner's own completions are intended decodes to a point at which no
player owes a failure (`Vegas.not_owesFailure_of_regular`).

**Value transport in belief.** At a forced first activation outside the late
pools, a choice committing an intended value at the player's own turn gains at
most what committing that value gains in the intended game, in expectation
over the native belief pushed to the intended site, up to twice the transport
error plus twelve times the scale times the payoff range, plus four times the
payoff range times the belief of the irregular histories
(`Vegas.onePacket_valueTransport_le`).
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
private theorem abs_exclusionReadoutUtility_le (lowerUtility upperUtility : Player → ℝ)
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

open Classical in
/-- **Value transport in belief.** For a well-formed setup under the
asynchronous contract with timely delays and retention of first covered
canonical packets, with bounded utilities, at a forced site outside the late
pools of an assembled profile, let a choice commit an intended value at the
player's own turn, and let who's own completions be intended along the regular
histories of the site. Then committing the same source action at the projected
site has a gain, in expectation over the native belief pushed to the intended
site by the replay projection, at least the gain of the choice, up to twice the
transport error plus twelve times the scale times the payoff range, plus four
times the payoff range times the belief of the irregular histories. -/
theorem onePacket_valueTransport_le
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (wellFormed : setup.WellFormed) {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence)
    (n : ℕ) {who : Player} (site : (onePacketN).InformationSite who)
    (choice : (onePacketN).Choice who site.1)
    (forced : ¬ UnforcedAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site))
    (unkeyed : ¬ ownedKeyed (UnforcedAgent setup leaks bounds horizon scheduler)
      (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
      ((onePacketN).agentAt site))
    (atTurn : CommitsAtTurn setup leaks bounds horizon scheduler who site choice)
    (intended : IntendedCommitment setup leaks bounds horizon scheduler site choice)
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1))
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (ownIntended : ∀ history : (onePacketN).InformationHistory who site.1,
      RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace →
      OwnCompletionsIntended (bounds := bounds) (horizon := horizon) (scheduler := scheduler) who
        history.1.trace) :
    ∃ policy : setup.intendedModel.BehavioralPolicy who,
      onePacketSiteGain setup leaks bounds horizon scheduler parameter utility excludedPayoff
          (targetSequence n) site (PMF.pure choice) ≤
        expect (((targetSequence n).belief who site).map
            (replayProjection setup leaks bounds horizon scheduler
              (projectedSite setup leaks decision) site atSite rfl))
            (setup.intendedModel.historyGain
              (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
              (intendedReadoutExclusion setup parameter utility excludedPayoff)
              (payoffComponent setup) (sequence n) (projectedSite setup leaks decision, policy)) +
          (2 * (((Fintype.card Player * (2 * horizon + 1) : ℕ) *
              (1 - slotRetention (scale n))) *
              (max 0 (max (excludedPayoff who) (upperUtility who)) -
                min 0 (min (excludedPayoff who) (lowerUtility who)))) +
            12 * scale n * (max 0 (max (excludedPayoff who) (upperUtility who)) -
              min 0 (min (excludedPayoff who) (lowerUtility who)))) +
          4 * (max 0 (max (excludedPayoff who) (upperUtility who)) -
              min 0 (min (excludedPayoff who) (lowerUtility who))) *
            expect ((targetSequence n).belief who site) (fun history =>
              if RegularTrace setup leaks bounds horizon scheduler (sequence n) who
                history.1.trace then 0 else 1) := by
  obtain ⟨policy, perHistory⟩ := onePacket_intendedCommitment_gain_le setup leaks bounds horizon
    scheduler parameter utility excludedPayoff wellFormed contract timely retains lowerUtility
    upperUtility lower_le le_upper sequence scale scale_pos scale_le_one weights targetSequence
    assembled n site choice forced unkeyed atTurn intended decision atSite
  refine ⟨policy, ?_⟩
  let range := max 0 (max (excludedPayoff who) (upperUtility who)) -
    min 0 (min (excludedPayoff who) (lowerUtility who))
  let error := 2 * (((Fintype.card Player * (2 * horizon + 1) : ℕ) *
    (1 - slotRetention (scale n))) * range) + 12 * scale n * range
  have rangeNonneg : 0 ≤ range := by
    have := le_max_left 0 (max (excludedPayoff who) (upperUtility who))
    have := min_le_left 0 (min (excludedPayoff who) (lowerUtility who))
    simp only [range]
    linarith
  have errorNonneg : 0 ≤ error := by
    have retentionLe := slotRetention_le_one (scale_pos n).le (scale_le_one n)
    have := (scale_pos n).le
    have : 0 ≤ (1 - slotRetention (scale n)) := by linarith
    simp only [error]
    positivity
  let native := (onePacketN).historyGain ((onePacketN).truncatedRunner (2 * horizon + 1))
    (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter utility
      excludedPayoff) (payoffComponent setup) (targetSequence n)
    (site, ((targetSequence n).strategy who).withLaw site.1 (PMF.pure choice))
  let source := setup.intendedModel.historyGain
    (setup.intendedModel.truncatedRunner (instructionCount setup.program + 1))
    (intendedReadoutExclusion setup parameter utility excludedPayoff)
    (payoffComponent setup) (sequence n) (projectedSite setup leaks decision, policy)
  let replay := replayProjection setup leaks bounds horizon scheduler
    (projectedSite setup leaks decision) site atSite rfl
  let irregular := fun history : (onePacketN).InformationHistory who site.1 =>
    if RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace then
      (0 : ℝ) else 1
  have pointwise : ∀ history, native history ≤
      (source (replay history) + error) + 4 * range * irregular history := by
    intro history
    by_cases regular : RegularTrace setup leaks bounds horizon scheduler (sequence n) who
      history.1.trace
    · have near := perHistory history (not_owesFailure_of_regular wellFormed (sequence n) atSite
        (not_not.mp forced) history regular (ownIntended history regular))
      simp only [irregular, regular, ↓reduceIte, mul_zero, add_zero]
      exact near
    · have nativeBound : |native history| ≤ 2 * range := abs_onePacket_historyGain_le setup
        leaks bounds horizon scheduler parameter utility excludedPayoff lowerUtility upperUtility
        lower_le le_upper (targetSequence n) (site, ((targetSequence n).strategy who).withLaw
          site.1 (PMF.pure choice)) history
      have sourceBound : |source (replay history)| ≤ 2 * range := abs_intended_historyGain_le
        setup parameter utility excludedPayoff lowerUtility upperUtility lower_le le_upper
        (sequence n) (projectedSite setup leaks decision, policy) (replay history)
      simp only [irregular, regular, ↓reduceIte, mul_one]
      linarith [(abs_le.mp nativeBound).2, (abs_le.mp sourceBound).1]
  unfold onePacketSiteGain
  dsimp only
  rw [gain_eq_expect_historyGain, expect_map]
  calc expect ((targetSequence n).belief who site) native
      ≤ expect ((targetSequence n).belief who site)
          (fun history => (source (replay history) + error) + 4 * range * irregular history) :=
        expect_mono (fun history _ => pointwise history) (payoffIntegrable_of_finite _ _)
          (payoffIntegrable_of_finite _ _)
    _ = _ := by
        rw [expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
          expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
          expect_constant, expect_const_mul]
        rfl

end Vegas
