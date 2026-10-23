/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.StoppedContinuationComparison
import Vegas.Game.OnePacketLawApproximation

/-! # Stopped one-packet continuations under retained honest choices

Choice retention is needed only on honest continuations. The comparison
therefore also applies when the target law stops before public failure or debt.
-/

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

local notation "N" => onePacketModel setup leaks bounds initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) initial horizon scheduler

/-- Retaining honest choices controls every bounded stopped continuation payoff. -/
theorem onePacket_stopped_expect_sub_le
    (assessment : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories) (stopped : (E).History → Prop)
    (profile : ∀ who, (N).BehavioralPolicy who) (start : (E).History)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (dominates : DominatesHonestFrom setup leaks bounds initial horizon scheduler assessment
      retention profile start)
    (payoff : (E).History → ℝ) {bound : ℝ} (boundNonneg : 0 ≤ bound)
    (payoffBounded : ∀ history, |payoff history| ≤ bound) :
    |expect ((N).runBehavioralUntil certificate profile stopped start) payoff -
      expect ((N).runBehavioralUntil certificate
        (honestProfile setup leaks bounds initial horizon scheduler assessment) stopped start)
        payoff| ≤
      (2 * bound * (Fintype.card Player * (1 - retention))) *
        (application setup leaks).rank horizon start.state := by
  classical
  let honest := honestProfile setup leaks bounds initial horizon scheduler assessment
  let inside := fun history => ∃ fuel, history ∈ ((N).runBehavioralFrom honest fuel start).support
  have closed : ∀ history next, inside history → ¬ stopped history →
      ¬ (E).terminal history.state → next ∈ ((N).runBehavioralFrom honest 1 history).support →
      inside next := by
    rintro history next ⟨fuel, reached⟩ _ _ member
    refine ⟨fuel + 1, ?_⟩
    rw [(N).runBehavioralFrom_add honest fuel 1, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨history, reached, member⟩
  have descends : ∀ history next, inside history → ¬ stopped history →
      ¬ (E).terminal history.state → next ∈ ((N).runBehavioralFrom honest 1 history).support →
      (application setup leaks).rank horizon next.state + 1 ≤
        (application setup leaks).rank horizon history.state := by
    intro history next _ _ running member
    obtain ⟨⟨joint, _legal, realized⟩, _⟩ :=
      (N).mem_support_runBehavioralFrom_one honest running member
    exact (application setup leaks).rank_step initial horizon scheduler history.state next.state
      joint running realized
  have close : ∀ history, inside history → ¬ stopped history → ¬ (E).terminal history.state →
      PMF.WithinTV (Fintype.card Player * (1 - retention))
        ((N).runBehavioralFrom honest 1 history) ((N).runBehavioralFrom profile 1 history) := by
    rintro history ⟨fuel, reached⟩ _ _
    apply PMF.WithinTV.mono (one_sub_pow_le_mul nonnegative (Fintype.card Player))
    apply PMF.WithinTV.of_domination _ _ _ (pow_le_one₀ nonnegative le_one)
    exact (N).runBehavioralFrom_one_domination_of_choices honest profile retention nonnegative
      history (dominates fuel history reached)
  rw [abs_sub_comm]
  exact (N).abs_expect_runBehavioralUntil_sub_le_of_stepTV certificate honest profile stopped
    inside payoff boundNonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr le_one))
    payoffBounded (fun history => (application setup leaks).rank horizon history.state)
    closed descends close start ⟨0, by simp [InformationModel.runBehavioralFrom]⟩

end Vegas
