/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.StoppedHonestComparison
import Interaction.ReactiveResponseCount

/-! # Honest stopped comparisons charged to actual expected responses -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (application setup leaks).State)
  (horizon : Nat) (scheduler : (application setup leaks).Scheduler)

local notation "menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "N" => onePacketModel setup leaks bounds initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) initial horizon scheduler

/-- Honest-choice loss is charged to the actual conditional number of future
responses. This compares complete stopped history laws at every starting site. -/
theorem onePacket_stopped_withinTV_honest
    (assessment : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories) (stopped : (E).History → Prop)
    (profile : ∀ who, (N).BehavioralPolicy who) (start : (E).History)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (dominates : DominatesHonestFrom setup leaks bounds initial horizon scheduler assessment
      retention profile start) :
    PMF.WithinTV ((1 - retention) * (menu).expectedResponses initial horizon scheduler certificate
        (honestProfile setup leaks bounds initial horizon scheduler assessment) stopped start)
      ((N).runBehavioralUntil certificate
        (honestProfile setup leaks bounds initial horizon scheduler assessment) stopped start)
      ((N).runBehavioralUntil certificate profile stopped start) := by
  classical
  let honest := honestProfile setup leaks bounds initial horizon scheduler assessment
  let exposure := (menu).expectedResponses initial horizon scheduler certificate honest stopped
  let inside := fun history => ∃ fuel, history ∈ ((N).runBehavioralFrom honest fuel start).support
  have closed : ∀ history next, inside history → ¬ stopped history →
      ¬ (E).terminal history.state → next ∈ ((N).runBehavioralFrom honest 1 history).support →
      inside next := by
    rintro history next ⟨fuel, reached⟩ _ _ member
    refine ⟨fuel + 1, ?_⟩
    rw [(N).runBehavioralFrom_add honest fuel 1, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨history, reached, member⟩
  intro event
  have estimate := (N).abs_expect_runBehavioralUntil_sub_le_of_stepTV_interval_potential
    certificate honest profile stopped inside (fun final => if final ∈ event then 1 else 0)
    (low := 0) (width := 1) (by norm_num)
    (fun _ => by split <;> norm_num)
    (fun history => (1 - retention) * (application setup leaks).responseCharge history.state)
    (fun history => (1 - retention) * exposure history)
    (fun history _ => mul_nonneg (sub_nonneg.mpr le_one)
      ((menu).expectedResponses_bounds initial horizon scheduler certificate honest stopped
        history).1)
    closed
    (fun _ _ _ _ => payoffIntegrable_const_mul
      ((menu).expectedResponses_integrable initial horizon scheduler certificate honest stopped _))
    (by
      intro history _ halt running
      have drift := (menu).expectedResponses_drift initial horizon scheduler certificate honest
        stopped history halt running
      rw [expect_const_mul]
      change (1 : ℝ) * ((1 - retention) * _) +
        (1 - retention) * expect _ exposure ≤ (1 - retention) * exposure history
      change (_ : ℝ) + expect _ exposure = exposure history at drift
      nlinarith)
    (by
      rintro history ⟨fuel, reached⟩ _ _
      exact onePacket_step_withinTV_honest setup leaks bounds initial horizon scheduler assessment
        profile history nonnegative le_one (fun who _ => dominates fuel history reached who))
    start ⟨0, by simp [InformationModel.runBehavioralFrom]⟩
  simpa only [expect_indicator] using estimate

/-- The bounded-payoff error counts actual honest responses before the stop.
Nature and padding themselves have zero charge; arbitrary scheduler changes
need not preserve the conditional number of responses. -/
theorem onePacket_stopped_expect_sub_le_expectedResponses
    (assessment : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories) (stopped : (E).History → Prop)
    (profile : ∀ who, (N).BehavioralPolicy who) (start : (E).History)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (dominates : DominatesHonestFrom setup leaks bounds initial horizon scheduler assessment
      retention profile start)
    (payoff : (E).History → ℝ) {bound : ℝ}
    (payoffBounded : ∀ history, |payoff history| ≤ bound) :
    |expect ((N).runBehavioralUntil certificate profile stopped start) payoff -
      expect ((N).runBehavioralUntil certificate
        (honestProfile setup leaks bounds initial horizon scheduler assessment) stopped start)
        payoff| ≤
      (2 * bound * (1 - retention)) * (menu).expectedResponses initial horizon scheduler
        certificate (honestProfile setup leaks bounds initial horizon scheduler assessment)
        stopped start := by
  have close := onePacket_stopped_withinTV_honest setup leaks bounds initial horizon scheduler
    assessment certificate stopped profile start nonnegative le_one dominates
  have interval : ∀ history : (E).History, -bound ≤ payoff history ∧
      payoff history ≤ -bound + 2 * bound := fun history => by
    have bounds := abs_le.mp (payoffBounded history)
    constructor <;> linarith [bounds.1, bounds.2]
  have first := close.expect_sub_le payoff (-bound) (2 * bound) (fun history _ => interval history)
  have second := close.symm.expect_sub_le payoff (-bound) (2 * bound)
    (fun history _ => interval history)
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

end Vegas
