/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCompletionLaw

/-! # The stopped value from a completion-point law of full success

**The stopped value.** Under play from a history until the event of a rank
completes, valued at each stop by the completion value at a completion and by a
bounded payoff elsewhere, a completion-point law of success one with error
error puts the expected value within twice error times the bound of the
expected source continuation value of its step law
(`Vegas.abs_expect_stoppedValue_sub_le_of_completionPointLaw`): the stops
without a completion point have mass at most error.
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

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
  scheduler).InfoState who)] in
open Classical in
/-- **The stopped value from a completion-point law of full success.** Let the
completion-point law from a history under installed, until the event of rank
rank completes, have success one, step law stepLaw and error error. Value
each stop at the completion value of profile when the event has completed, with
fallback fallback, and at payoff otherwise; let the exclusion payoff of
who at every readout, fallback and payoff be bounded by bound. Then the
expected value is within twice error times bound of the expected source
continuation value of profile under stepLaw. -/
theorem abs_expect_stoppedValue_sub_le_of_completionPointLaw
    (installed : ∀ who, (onePacketN).BehavioralPolicy who)
    (profile : BehavioralProfile setup.program) (rank : Nat)
    (fresh : (application setup leaks).Control → Prop) (who : Player)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (stepLaw : PMF (ProtocolState setup.program)) {error bound : ℝ}
    (readoutBounded : ∀ readout, |exclusionReadoutUtility setup parameter utility excludedPayoff
      readout who| ≤ bound)
    (pointLaw : CompletionPointLaw setup leaks bounds horizon scheduler installed rank fresh
      history 1 stepLaw error)
    (fallback payoff : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History → ℝ)
    (fallbackBounded : ∀ later, |fallback later| ≤ bound)
    (payoffBounded : ∀ final, |payoff final| ≤ bound) :
    |expect ((onePacketN).runBehavioralUntil
        ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
          scheduler).wellFoundedHistories installed
        (LateStopped setup leaks bounds horizon scheduler rank) history)
        (fun stop => if LateStopped setup leaks bounds horizon scheduler rank stop then
          completionValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
            profile rank fresh who fallback stop
          else payoff stop) -
      expect stepLaw (sourcePointValue setup parameter utility excludedPayoff profile who)| ≤
      2 * error * bound := by
  let untilLaw := (onePacketN).runBehavioralUntil
    ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
      scheduler).wellFoundedHistories installed
    (LateStopped setup leaks bounds horizon scheduler rank) history
  let stopped := LateStopped setup leaks bounds horizon scheduler rank
  let point := completionPoint setup leaks bounds horizon scheduler rank fresh
  let value := sourcePointValue setup parameter utility excludedPayoff profile who
  let other := fun stop => if stopped stop then fallback stop else payoff stop
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans (readoutBounded none)
  have valueBounded : ∀ target, |value target| ≤ bound := fun target =>
    expect_abs_le_of_bounded boundNonneg fun readout => readoutBounded readout
  have otherBounded : ∀ stop, |other stop| ≤ bound := fun stop => by
    simp only [other]
    split
    · exact fallbackBounded stop
    · exact payoffBounded stop
  -- The value at a stop is its value at the completion point and the rest.
  have split : ∀ stop, (if stopped stop then
      completionValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        profile rank fresh who fallback stop else payoff stop) =
      (point stop).elim 0 value + (point stop).elim (other stop) (fun _ => 0) := by
    intro stop
    by_cases halted : stopped stop
    · rw [ite_eq_left halted .., completionValue_eq_elim setup leaks bounds horizon scheduler
        parameter utility excludedPayoff profile rank fresh who fallback halted]
      cases pointCase : completionPoint setup leaks bounds horizon scheduler rank fresh stop with
      | none => simp [point, other, halted, pointCase]
      | some target => simp [point, value, pointCase]
    · have none : point stop = none := by
        cases pointCase : point stop with
        | none => rfl
        | some target =>
            exact (halted (completionValue_of_completionPoint setup leaks bounds horizon
              scheduler parameter utility excludedPayoff profile rank fresh who fallback
              pointCase).1).elim
      rw [ite_eq_right halted .., none]
      simp [other, halted]
  have pointPart := pointLaw value bound valueBounded
  have unitPart := pointLaw (fun _ => 1) 1 (fun _ => by simp)
  rw [one_mul] at pointPart unitPart
  rw [expect_constant, mul_one] at unitPart
  have firstBounded : ∀ stop, |(point stop).elim 0 value| ≤ bound := fun stop => by
    cases point stop with
    | none => simpa using boundNonneg
    | some target => exact valueBounded target
  have restBounded : ∀ stop, |(point stop).elim (other stop) (fun _ => 0)| ≤
      bound * (point stop).elim 1 (fun _ => 0) := fun stop => by
    cases point stop with
    | none => simpa using otherBounded stop
    | some target => simp
  have missing : expect untilLaw (fun stop => (point stop).elim 1 (fun _ => 0)) =
      1 - expect untilLaw (fun stop => (point stop).elim 0 (fun _ => 1)) := by
    have total : ∀ stop, (point stop).elim 1 (fun _ => 0) =
        1 - (point stop).elim 0 (fun _ => (1 : ℝ)) := fun stop => by
      cases point stop <;> simp
    rw [expect_congr_on_support (g := fun stop => 1 - (point stop).elim 0 (fun _ => (1 : ℝ)))
      fun stop _ => total stop,
      expect_sub (payoffIntegrable_of_bounded _ _ (C := 1) fun _ => by simp)
        (payoffIntegrable_of_bounded _ _ (C := 1) fun stop => by
          cases point stop <;> simp), expect_constant]
  have restAbs : |expect untilLaw (fun stop => (point stop).elim (other stop) (fun _ => 0))| ≤
      bound * error := by
    have upper := expect_mono (μ := untilLaw)
      (f := fun stop => (point stop).elim (other stop) (fun _ => 0))
      (g := fun stop => bound * (point stop).elim 1 (fun _ => 0))
      (fun stop _ => (abs_le.mp (restBounded stop)).2)
      (payoffIntegrable_of_bounded _ _ (C := bound) fun stop =>
        (restBounded stop).trans (by cases point stop <;> simp [boundNonneg]))
      (payoffIntegrable_of_bounded _ _ (C := bound) fun stop => by
        cases point stop <;> simp [abs_of_nonneg boundNonneg, boundNonneg])
    have lower := expect_mono (μ := untilLaw)
      (f := fun stop => -(bound * (point stop).elim 1 (fun _ => 0)))
      (g := fun stop => (point stop).elim (other stop) (fun _ => 0))
      (fun stop _ => (abs_le.mp (restBounded stop)).1)
      (payoffIntegrable_of_bounded _ _ (C := bound) fun stop => by
        cases point stop <;> simp [abs_of_nonneg boundNonneg, boundNonneg])
      (payoffIntegrable_of_bounded _ _ (C := bound) fun stop =>
        (restBounded stop).trans (by cases point stop <;> simp [boundNonneg]))
    rw [expect_const_mul, missing] at upper
    rw [expect_neg, expect_const_mul, missing] at lower
    have unit := abs_le.mp unitPart
    have product : bound * (1 - expect untilLaw (fun stop =>
        (point stop).elim 0 (fun _ => (1 : ℝ)))) ≤ bound * error :=
      mul_le_mul_of_nonneg_left (by linarith [unit.1]) boundNonneg
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  change |expect untilLaw _ - _| ≤ _
  rw [expect_congr_on_support (g := fun stop => (point stop).elim 0 value +
      (point stop).elim (other stop) (fun _ => 0)) fun stop _ => split stop,
    expect_add (payoffIntegrable_of_bounded _ _ firstBounded)
      (payoffIntegrable_of_bounded _ _ (C := bound) fun stop =>
        (restBounded stop).trans (by cases point stop <;> simp [boundNonneg]))]
  calc _ ≤ |expect untilLaw (fun stop => (point stop).elim 0 value) - expect stepLaw value| +
        |expect untilLaw (fun stop => (point stop).elim (other stop) (fun _ => 0))| := by
        rw [show expect untilLaw (fun stop => (point stop).elim 0 value) +
          expect untilLaw (fun stop => (point stop).elim (other stop) (fun _ => 0)) -
            expect stepLaw value = (expect untilLaw (fun stop => (point stop).elim 0 value) -
              expect stepLaw value) +
            expect untilLaw (fun stop => (point stop).elim (other stop) (fun _ => 0)) by ring]
        exact abs_add_le _ _
    _ ≤ error * bound + bound * error := add_le_add pointPart restAbs
    _ = 2 * error * bound := by ring

open Classical in
/-- **The value of play from a history by its completion-point law.** For a
well-formed setup under the asynchronous contract with timely delays and
retention of first covered canonical packets, at a history of a decision of who
in an assembled profile, with a law installed at an information state info,
whose configuration is a prefix of the rank of info: if the completion-point
law from the history has success one, step law stepLaw and error error, the
expected exclusion payoff of who under truncated play is within the transport
error plus twice error times the payoff range of the expected source
continuation value of the intended effective opening under stepLaw. -/
theorem abs_expect_historyRun_sub_le_of_completionPointLaw (wellFormed : setup.WellFormed)
    {delay bound : (graph setup).EventId → Nat}
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
    (n : ℕ) {who : Player} (info : (application setup leaks).Info) (decision : info.isSome)
    (law : PMF ((onePacketN).Choice who info))
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) {remaining : Nat} {execution : (application setup leaks).Execution}
    (startState : start.state = some ⟨remaining, some who, execution⟩)
    (ordered : execution.application.config.cut.IsPrefix (siteRank info))
    (fresh : (application setup leaks).Control → Prop) (stepLaw : PMF (ProtocolState setup.program))
    {error : ℝ}
    (pointLaw : CompletionPointLaw setup leaks bounds horizon scheduler
      (Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy who
        (((targetSequence n).strategy who).withLaw info law))
      (siteRank info) fresh start 1 stepLaw error) :
    |expect (((onePacketN).runBehavioralFrom
        (Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy who
          (((targetSequence n).strategy who).withLaw info law)) (2 * horizon + 1) start).map
        (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter utility
          excludedPayoff)) (payoffComponent setup · who) -
      expect stepLaw (sourcePointValue setup parameter utility excludedPayoff
        (setup.intendedOpeningProfile (sequence n).strategy) who)| ≤
      ((Fintype.card Player * (2 * horizon + 1) : ℕ) * (1 - slotRetention (scale n))) *
          (max 0 (max (excludedPayoff who) (upperUtility who)) -
            min 0 (min (excludedPayoff who) (lowerUtility who))) +
        2 * error * (max 0 (max (excludedPayoff who) (upperUtility who)) -
            min 0 (min (excludedPayoff who) (lowerUtility who))) := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
  have bounded := menu.bounded (initialLaw setup) horizon scheduler
  let certificate := bounded.wellFoundedHistories
  let installed := Profile.update (sig := model.behavioralSignature) (targetSequence n).strategy
    who (((targetSequence n).strategy who).withLaw info law)
  let low := min 0 (min (excludedPayoff who) (lowerUtility who))
  let range := max 0 (max (excludedPayoff who) (upperUtility who)) - low
  have boundedReadout : ∀ readout, low ≤ exclusionReadoutUtility setup parameter utility
      excludedPayoff readout who ∧
      exclusionReadoutUtility setup parameter utility excludedPayoff readout who ≤ low + range :=
    fun readout => by
      have within := exclusionReadoutUtility_mem_Icc setup parameter utility excludedPayoff
        lowerUtility upperUtility lower_le le_upper readout who
      exact ⟨within.1, by simp only [low, range]; linarith [within.2]⟩
  have zeroWithin : low ≤ 0 ∧ 0 ≤ low + range :=
    ⟨min_le_left _ _, by
      simp only [low, range]
      linarith [le_max_left 0 (max (excludedPayoff who) (upperUtility who))]⟩
  have readoutBounded : ∀ readout, |exclusionReadoutUtility setup parameter utility
      excludedPayoff readout who| ≤ range := fun readout => by
    obtain ⟨lowerBound, upperBound⟩ := boundedReadout readout
    exact abs_le.mpr ⟨by linarith [zeroWithin.2], by linarith [zeroWithin.1]⟩
  have retentionNonneg := slotRetention_nonneg (scale_pos n).le (scale_le_one n)
  have retentionLe := slotRetention_le_one (scale_pos n).le (scale_le_one n)
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    startState ▸ menu.toRawTrace (initialLaw setup) horizon scheduler start.trace
  obtain ⟨found, foundOrdered, seen⟩ := pendingAt_history rawTrace
  have sameRank := isPrefix_unique foundOrdered ordered
  subst sameRank
  let payoff := fun final : (menu.protocol (initialLaw setup) horizon scheduler).History =>
    exclusionBase setup parameter utility excludedPayoff leaks final.state who
  have transport := abs_expect_offFailed_sub_completionValue_le bounds parameter utility
    excludedPayoff wellFormed contract timely (sequence n) retains retentionNonneg retentionLe
    installed (siteRank info)
    (fun start anchor state reached point decoded intendedPoint =>
      installed_dominates setup leaks bounds horizon scheduler contract timely retains
        sequence scale scale_pos scale_le_one weights targetSequence assembled n info decision
        law start anchor state reached point decoded intendedPoint)
    ∅ fresh (fun _ _ _ _ _ _ _ impossible => impossible) who low range boundedReadout zeroWithin
    start startState ⟨foundOrdered, seen⟩
  have payoffBounded : ∀ final, |payoff final| ≤ range := fun final => readoutBounded _
  have stopped := abs_expect_stoppedValue_sub_le_of_completionPointLaw setup leaks bounds horizon
    scheduler parameter utility excludedPayoff installed
    (setup.intendedOpeningProfile (sequence n).strategy) (siteRank info) fresh who start stepLaw
    readoutBounded pointLaw
    (fun later => expect (model.runBehavioralTerminalFrom certificate installed later) payoff)
    payoff (fun later => expect_abs_le_of_bounded ((abs_nonneg _).trans (readoutBounded none))
      payoffBounded) payoffBounded
  have runEq : expect ((model.runBehavioralFrom installed (2 * horizon + 1) start).map
      (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter utility
        excludedPayoff)) (payoffComponent setup · who) =
      expect (model.runBehavioralTerminalFrom certificate installed start) payoff := by
    rw [expect_map, ← model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
      bounded]
    rfl
  change |expect ((model.runBehavioralFrom installed (2 * horizon + 1) start).map _) _ - _| ≤ _
  rw [runEq]
  simp only [Set.mem_empty_iff_false, ite_false] at transport
  exact (abs_sub_le _ _ _).trans (add_le_add transport stopped)

end Vegas
