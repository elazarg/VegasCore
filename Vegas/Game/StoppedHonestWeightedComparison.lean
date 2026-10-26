/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.StoppedCharge
import Vegas.Game.StoppedHonestComparison

/-! # Stopped honest comparisons with information-dependent mixture weights

The error is the honest conditional sum of per-response losses. Each player may
choose its mixture weight from its actual information; no uniform retained
fraction is required. The original conditional response-count bounds remain separate.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [Fintype Player] [DecidableEq Player]
    {L : IExpr} [IExpr.ResultTypes L]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (initial : PMF (application setup leaks).State)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)

local notation "N" => onePacketModel setup leaks bounds initial horizon scheduler
local notation "P" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) initial horizon scheduler

/-- Every callback may have its own retained fraction, depending on the full
actual history. The cost is the honest expected sum of those callback losses. -/
theorem onePacket_stopped_withinTV_of_history_retention
    (assessment : setup.intendedModel.BehavioralAssessment)
    (certificate : (P).WellFoundedHistories) (stopped : (P).History → Prop)
    (profile : ∀ who, (N).BehavioralPolicy who) (start : (P).History)
    (retention : (P).History → ℝ)
    (nonnegative : ∀ history, 0 ≤ retention history)
    (le_one : ∀ history, retention history ≤ 1)
    (lower : ∀ elapsed history,
      history ∈ ((N).runBehavioralFrom
        (honestProfile setup leaks bounds initial horizon scheduler assessment) elapsed
        start).support →
      ∀ who, (P).active history.state who → ∀ choice,
        retention history *
          ((honestProfile setup leaks bounds initial horizon scheduler assessment who
            ((N).infoOf who history.trace)) choice).toReal ≤
          ((profile who ((N).infoOf who history.trace)) choice).toReal) :
    let honest := honestProfile setup leaks bounds initial horizon scheduler assessment
    let charge := fun history : (P).History => (1 - retention history) *
      (application setup leaks).responseCharge history.state
    PMF.WithinTV (expectedCharge (N) certificate honest stopped charge start)
      ((N).runBehavioralUntil certificate honest stopped start)
      ((N).runBehavioralUntil certificate profile stopped start) := by
  classical
  intro honest charge
  have bounded := (bounds.onePacketMenu (runtime setup) leaks).bounded initial horizon scheduler
  have chargeNonnegative (history : (P).History) : 0 ≤ charge history :=
    mul_nonneg (sub_nonneg.mpr (le_one history)) (Nat.cast_nonneg _)
  have chargeBounded (history : (P).History) : charge history ≤ 1 := by
    calc
      _ ≤ 1 * ((application setup leaks).responseCharge history.state : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith [nonnegative history]) (Nat.cast_nonneg _)
      _ ≤ 1 := by
        simpa only [one_mul, Nat.cast_le_one] using
          (application setup leaks).responseCharge_le_one history.state
  let inside := fun history => ∃ elapsed,
    history ∈ ((N).runBehavioralFrom honest elapsed start).support
  have closed : ∀ history next, inside history → ¬ stopped history →
      ¬ (P).terminal history.state → next ∈ ((N).runBehavioralFrom honest 1 history).support →
      inside next := by
    rintro history next ⟨elapsed, reached⟩ _ _ member
    refine ⟨elapsed + 1, ?_⟩
    rw [(N).runBehavioralFrom_add honest elapsed 1, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨history, reached, member⟩
  intro event
  have estimate := (N).abs_expect_runBehavioralUntil_sub_le_of_stepTV_interval_potential
    certificate honest profile stopped inside (fun final => if final ∈ event then 1 else 0)
    (low := 0) (width := 1) (by norm_num) (fun _ => by split <;> norm_num)
    charge (expectedCharge (N) certificate honest stopped charge)
    (fun history _ => (expectedCharge_bounds (N) bounded certificate honest stopped charge
      chargeNonnegative chargeBounded history).1) closed
    (fun _ _ _ _ => expectedCharge_integrable (N) bounded certificate honest stopped charge
      chargeNonnegative chargeBounded _)
    (by
      intro history _ halt running
      have drift := expectedCharge_drift (N) bounded certificate honest stopped charge
        chargeNonnegative chargeBounded history halt running
      simpa only [one_mul] using drift.le)
    (by
      rintro history ⟨elapsed, reached⟩ _ _
      exact onePacket_step_withinTV_honest setup leaks bounds initial horizon scheduler assessment
        profile history (nonnegative history) (le_one history) (lower elapsed history reached))
    start ⟨0, by simp [InformationModel.runBehavioralFrom]⟩
  simpa only [expect_indicator] using estimate

/-- The history-dependent bound has an operational producer: every player mixes
honest play with an arbitrary policy at a rate depending only on its own information.
No final-law or comparison-error premise is supplied by the caller. -/
theorem onePacket_mixture_stopped_withinTV_honest
    (assessment : setup.intendedModel.BehavioralAssessment)
    (certificate : (P).WellFoundedHistories) (stopped : (P).History → Prop)
    (other : ∀ who, (N).BehavioralPolicy who) (start : (P).History)
    (rate : ∀ who, (N).InfoState who → ℝ)
    (nonnegative : ∀ who info, 0 ≤ rate who info)
    (le_one : ∀ who info, rate who info ≤ 1) :
    let honest := honestProfile setup leaks bounds initial horizon scheduler assessment
    let profile := fun who info => mix (rate who info) (nonnegative who info) (le_one who info)
      (honest who info) (other who info)
    let retention := fun history : (P).History =>
      ((application setup leaks).actor history.state).elim 1
        (fun who => rate who ((N).infoOf who history.trace))
    let charge := fun history : (P).History => (1 - retention history) *
      (application setup leaks).responseCharge history.state
    PMF.WithinTV (expectedCharge (N) certificate honest stopped charge start)
      ((N).runBehavioralUntil certificate honest stopped start)
      ((N).runBehavioralUntil certificate profile stopped start) := by
  classical
  intro honest profile retention charge
  apply onePacket_stopped_withinTV_of_history_retention setup leaks bounds initial horizon scheduler
    assessment certificate stopped profile start retention
  · intro history
    dsimp only [retention]
    cases (application setup leaks).actor history.state with
    | none => exact zero_le_one
    | some who => exact nonnegative who _
  · intro history
    dsimp only [retention]
    cases (application setup leaks).actor history.state with
    | none => exact le_rfl
    | some who => exact le_one who _
  · intro elapsed history _ who active choice
    change (application setup leaks).actor history.state = some who at active
    dsimp only [retention]
    rw [active]
    change rate who ((N).infoOf who history.trace) * _ ≤ _
    dsimp only [profile]
    have branchLower := mix_retains_right
      ⟨1 - rate who ((N).infoOf who history.trace),
        ⟨by linarith [le_one who ((N).infoOf who history.trace)],
          by linarith [nonnegative who ((N).infoOf who history.trace)]⟩⟩
      (other who ((N).infoOf who history.trace)) (honest who ((N).infoOf who history.trace)) choice
    rw [mix_swap (rate who ((N).infoOf who history.trace))
      (nonnegative who _) (le_one who _) (honest who ((N).infoOf who history.trace))
      (other who ((N).infoOf who history.trace))] at branchLower
    simpa only [sub_sub_cancel] using branchLower

end Vegas
