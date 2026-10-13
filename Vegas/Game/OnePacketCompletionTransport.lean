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

end Vegas
