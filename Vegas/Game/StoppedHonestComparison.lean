/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.StoppedContinuationComparison
import Vegas.Game.OnePacketLawApproximation
import Interaction.ReactiveDecisionBudget

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
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (application setup runtime leaks).State)
  (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)

local notation "N" =>
  onePacketModel (runtime := runtime) setup leaks bounds initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) initial horizon scheduler

/-- The actual reactive protocol samples at most one player response. All
initialization and scheduler kernels have zero local error. -/
theorem onePacket_step_withinTV_honest
    (assessment : setup.intendedModel.BehavioralAssessment)
    (profile : ∀ who, (N).BehavioralPolicy who) (history : (E).History)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (lower : ∀ who, (E).active history.state who → ∀ choice,
      retention * ((honestProfile (runtime := runtime) setup leaks bounds initial
        horizon scheduler assessment who
        ((N).infoOf who history.trace)) choice).toReal ≤
          ((profile who ((N).infoOf who history.trace)) choice).toReal) :
    PMF.WithinTV ((1 - retention) *
        (application setup runtime leaks).responseCharge history.state)
      ((N).runBehavioralFrom
        (honestProfile (runtime := runtime) setup leaks bounds initial horizon
          scheduler assessment) 1 history)
      ((N).runBehavioralFrom profile 1 history) := by
  classical
  have domination := (N).runBehavioralFrom_one_domination_of_active_choices
    (honestProfile (runtime := runtime) setup leaks bounds initial horizon
      scheduler assessment) profile retention
    nonnegative history lower
  have count := (bounds.onePacketMenu runtime leaks).active_card initial horizon scheduler
  rw [count] at domination
  apply (PMF.WithinTV.of_domination _ _ _ (pow_le_one₀ nonnegative le_one) domination).mono
  have estimate := one_sub_pow_le_mul nonnegative
    ((application setup runtime leaks).responseCharge history.state)
  nlinarith

/-- History-dependent honest-choice losses are paid only at genuine response
steps. The potential premises concern actual honest-supported continuations. -/
theorem onePacket_stopped_expect_sub_le_of_potential
    (assessment : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories) (stopped : (E).History → Prop)
    (profile : ∀ who, (N).BehavioralPolicy who) (start : (E).History)
    (retention : (E).History → ℝ)
    (nonnegative : ∀ history, 0 ≤ retention history) (le_one : ∀ history, retention history ≤ 1)
    (lower : ∀ fuel history,
      history ∈ ((N).runBehavioralFrom
        (honestProfile (runtime := runtime) setup leaks bounds initial horizon
          scheduler assessment) fuel
        start).support →
      ∀ who, (E).active history.state who → ∀ choice,
        retention history *
          ((honestProfile (runtime := runtime) setup leaks bounds initial horizon
            scheduler assessment who
            ((N).infoOf who history.trace)) choice).toReal ≤
          ((profile who ((N).infoOf who history.trace)) choice).toReal)
    (payoff : (E).History → ℝ) {bound : ℝ} (boundNonneg : 0 ≤ bound)
    (payoffBounded : ∀ history, |payoff history| ≤ bound) (potential : (E).History → ℝ)
    (potentialNonnegative : ∀ fuel history,
      history ∈ ((N).runBehavioralFrom
        (honestProfile (runtime := runtime) setup leaks bounds initial horizon
          scheduler assessment) fuel
        start).support →
      0 ≤ potential history)
    (integrable : ∀ fuel history,
      history ∈ ((N).runBehavioralFrom
        (honestProfile (runtime := runtime) setup leaks bounds initial horizon
          scheduler assessment) fuel
        start).support →
      ¬ stopped history → ¬ (E).terminal history.state →
      PayoffIntegrable ((N).runBehavioralFrom
        (honestProfile (runtime := runtime) setup leaks bounds initial horizon
          scheduler assessment) 1 history)
        potential)
    (pays : ∀ fuel history,
      history ∈ ((N).runBehavioralFrom
        (honestProfile (runtime := runtime) setup leaks bounds initial horizon
          scheduler assessment) fuel
        start).support →
      ¬ stopped history → ¬ (E).terminal history.state →
      2 * bound * ((1 - retention history) *
          (application setup runtime leaks).responseCharge history.state) +
        expect ((N).runBehavioralFrom
          (honestProfile (runtime := runtime) setup leaks bounds initial horizon
            scheduler assessment) 1 history)
          potential ≤ potential history) :
    |expect ((N).runBehavioralUntil certificate profile stopped start) payoff -
      expect ((N).runBehavioralUntil certificate
        (honestProfile (runtime := runtime) setup leaks bounds initial horizon
          scheduler assessment) stopped start)
        payoff| ≤ potential start := by
  classical
  let honest := honestProfile (runtime := runtime) setup leaks bounds initial
    horizon scheduler assessment
  let inside := fun history => ∃ fuel, history ∈ ((N).runBehavioralFrom honest fuel start).support
  have closed : ∀ history next, inside history → ¬ stopped history →
      ¬ (E).terminal history.state → next ∈ ((N).runBehavioralFrom honest 1 history).support →
      inside next := by
    rintro history next ⟨fuel, reached⟩ _ _ member
    refine ⟨fuel + 1, ?_⟩
    rw [(N).runBehavioralFrom_add honest fuel 1, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨history, reached, member⟩
  rw [abs_sub_comm]
  apply (N).abs_expect_runBehavioralUntil_sub_le_of_stepTV_potential certificate honest profile
    stopped inside payoff boundNonneg payoffBounded
    (fun history => (1 - retention history) *
      (application setup runtime leaks).responseCharge history.state) potential
    (by rintro history ⟨fuel, reached⟩; exact potentialNonnegative fuel history reached)
    closed
    (by
      rintro history ⟨fuel, reached⟩ halt running
      exact integrable fuel history reached halt running)
    (by rintro history ⟨fuel, reached⟩ halt running; exact pays fuel history reached halt running)
    (by
      rintro history ⟨fuel, reached⟩ _ _
      exact onePacket_step_withinTV_honest (runtime := runtime) setup leaks bounds initial
        horizon scheduler assessment
        profile history (nonnegative history) (le_one history) (lower fuel history reached))
    start ⟨0, by simp [InformationModel.runBehavioralFrom]⟩

/-- A uniform retained fraction pays for remaining possible player responses,
independently of the player population. Environment steps have zero charge. -/
theorem onePacket_stopped_expect_sub_le_remainingResponses
    (assessment : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories) (stopped : (E).History → Prop)
    (profile : ∀ who, (N).BehavioralPolicy who) (start : (E).History)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (dominates : DominatesHonestFrom (runtime := runtime) setup leaks bounds
      initial horizon scheduler assessment
      retention profile start)
    (payoff : (E).History → ℝ) {bound : ℝ} (boundNonneg : 0 ≤ bound)
    (payoffBounded : ∀ history, |payoff history| ≤ bound) :
    |expect ((N).runBehavioralUntil certificate profile stopped start) payoff -
      expect ((N).runBehavioralUntil certificate
        (honestProfile (runtime := runtime) setup leaks bounds initial horizon
          scheduler assessment) stopped start)
        payoff| ≤
      (2 * bound * (1 - retention)) *
        (application setup runtime leaks).remainingResponses horizon start.state := by
  classical
  let cost := 2 * bound * (1 - retention)
  have costNonnegative : 0 ≤ cost := by dsimp [cost]; positivity
  let potential := fun history : (E).History => cost *
    (application setup runtime leaks).remainingResponses horizon history.state
  have bounded : ∀ history, |potential history| ≤ cost * (horizon + 1) := by
    intro history
    dsimp only [potential]
    rw [abs_mul, abs_of_nonneg costNonnegative, abs_of_nonneg (Nat.cast_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ costNonnegative
    exact_mod_cast ReactiveApplication.ResponseMenu.remainingResponses_le_horizon_add_one
      (bounds.onePacketMenu runtime leaks) initial horizon scheduler history
  apply onePacket_stopped_expect_sub_le_of_potential (runtime := runtime) setup leaks bounds
    initial horizon scheduler
    assessment certificate stopped profile start (fun _ => retention) (fun _ => nonnegative)
    (fun _ => le_one) (fun fuel history reached who _ => dominates fuel history reached who)
    payoff boundNonneg payoffBounded potential
    (fun _ _ _ => mul_nonneg costNonnegative (Nat.cast_nonneg _))
    (fun _ _ _ _ _ => payoffIntegrable_of_bounded _ _ bounded)
  intro fuel history _ _ running
  have stepBound : ∀ next ∈ ((N).runBehavioralFrom
      (honestProfile (runtime := runtime) setup leaks bounds initial horizon
        scheduler assessment) 1 history).support,
      potential next ≤ potential history - cost *
        (application setup runtime leaks).responseCharge history.state := by
    intro next member
    obtain ⟨⟨joint, _, realized⟩, _⟩ := (N).mem_support_runBehavioralFrom_one
      (honestProfile (runtime := runtime) setup leaks bounds initial horizon
        scheduler assessment) running member
    have progress := (application setup runtime leaks).remainingResponses_step
      initial horizon scheduler
      history.state next.state joint realized
    have progressReal :
        ((application setup runtime leaks).remainingResponses horizon next.state
          : ℝ) +
          (application setup runtime leaks).responseCharge history.state ≤
            (application setup runtime leaks).remainingResponses horizon
              history.state := by
      exact_mod_cast progress
    dsimp only [potential]
    nlinarith
  have expected := expect_le_const _ potential
    (payoffIntegrable_of_bounded _ _ bounded)
    (potential history - cost * (application setup runtime leaks).responseCharge
      history.state) stepBound
  change 2 * bound * ((1 - retention) * _) + expect _ potential ≤ potential history
  dsimp only [cost] at expected
  nlinarith

/-- Retaining honest choices controls every bounded stopped continuation payoff. -/
theorem onePacket_stopped_expect_sub_le
    (assessment : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories) (stopped : (E).History → Prop)
    (profile : ∀ who, (N).BehavioralPolicy who) (start : (E).History)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (dominates : DominatesHonestFrom (runtime := runtime) setup leaks bounds
      initial horizon scheduler assessment
      retention profile start)
    (payoff : (E).History → ℝ) {bound : ℝ} (boundNonneg : 0 ≤ bound)
    (payoffBounded : ∀ history, |payoff history| ≤ bound) :
    |expect ((N).runBehavioralUntil certificate profile stopped start) payoff -
      expect ((N).runBehavioralUntil certificate
        (honestProfile (runtime := runtime) setup leaks bounds initial horizon
          scheduler assessment) stopped start)
        payoff| ≤
      (2 * bound * (Fintype.card Player * (1 - retention))) *
        (application setup runtime leaks).rank horizon start.state := by
  classical
  by_cases inhabited : Nonempty Player
  · have sharp := onePacket_stopped_expect_sub_le_remainingResponses (runtime := runtime) setup
      leaks bounds initial
      horizon scheduler assessment certificate stopped profile start nonnegative le_one dominates
      payoff boundNonneg payoffBounded
    have players : 0 < Fintype.card Player := Fintype.card_pos_iff.mpr inhabited
    have budget := ((application setup runtime leaks).remainingResponses_le_rank
      horizon start.state).trans
      (Nat.le_mul_of_pos_left _ players)
    have nonneg : 0 ≤ 2 * bound * (1 - retention) := by positivity
    apply sharp.trans
    have budgetReal :
        ((application setup runtime leaks).remainingResponses horizon start.state
          : ℝ) ≤
        Fintype.card Player * (application setup runtime leaks).rank horizon
          start.state := by
      exact_mod_cast budget
    have estimate := mul_le_mul_of_nonneg_left budgetReal nonneg
    convert estimate using 1
    ring
  · have same : profile =
        honestProfile (runtime := runtime) setup leaks bounds initial horizon
          scheduler assessment := by
      funext who
      exact (inhabited ⟨who⟩).elim
    rw [same, sub_self, abs_zero]
    positivity

end Vegas
