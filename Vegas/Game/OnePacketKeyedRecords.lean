/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketFactorization
import GameTheoryExtensions.Math.Probability.SwapTransport

/-! # Record laws at sites with a common late-delivery key

At an information site of the owner `who`, a Bayes belief is the normalized
reach of the site's histories. By the operational factorization, the reach of a
regular history is, up to a relative error, the owner mass of the site's recall,
which is the same for every history of the site, times a base weight: the
source weight times the operational weight of the record
(`Vegas.reach_near_factorization`). So if the normalized base weights of the
regular histories of two sites give every unit payoff of the operational record
the same expectation (`Vegas.BaseLawAgrees`), and the irregular histories carry
little reach, the two sites' belief laws of operational records are close on
unit payoffs (`Vegas.recordLaw_near_of_baseLaw`). This is the `keyed` field of
`Vegas.LateDeliveryBlindness` for sites with the same late-delivery key.

Base agreement asks less than a weight-preserving bijection between the sites'
histories, and holds with correlated priors: within a site, records differ only
in parts the other players' hidden values do not reach, so the base fibers of
two sites are proportional.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

open Classical in
/-- **Agreeing base laws.** The normalized base weights of the regular histories
of two sites give a payoff of the operational record the same expectation. -/
def BaseLawAgrees {who : Player}
    [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History]
    (base : (onePacketProtocol setup leaks bounds horizon scheduler).History → ℝ)
    (regular : (onePacketProtocol setup leaks bounds horizon scheduler).History → Prop)
    (first second : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who)
    (payoff : List (Option (OperationalState setup leaks)) → ℝ) : Prop :=
  let := Fintype.ofFinite ((onePacketInformation setup leaks bounds horizon
    scheduler).InformationHistory who first.1)
  let := Fintype.ofFinite ((onePacketInformation setup leaks bounds horizon
    scheduler).InformationHistory who second.1)
  (∑ b : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      second.1, (if regular b.1 then base b.1 else 0) /
      (∑ c : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
        second.1, if regular c.1 then base c.1 else 0) *
      payoff (operationalRecord setup leaks bounds horizon scheduler b.1.trace)) =
    ∑ a : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      first.1, (if regular a.1 then base a.1 else 0) /
      (∑ c : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
        first.1, if regular c.1 then base c.1 else 0) *
      payoff (operationalRecord setup leaks bounds horizon scheduler a.1.trace)

open Classical in
/-- **Record laws at two sites.** Suppose the beliefs at two sites of `who` are
the normalized reach weights of their histories; at every regular history the
reach is within relative error `ε < 1` of a positive site constant times a base
weight; the regular base weights of each site have positive total and those of the
first agree in law with the second's on a unit payoff of the record; and the
irregular histories of each site carry at most `ρ` times its regular reach. Then
the two beliefs give that payoff of the record expectations within
`4 ρ + 4 ε / (1 - ε)`. -/
theorem recordLaw_near_of_baseLaw {who : Player}
    [Finite (onePacketProtocol setup leaks bounds horizon scheduler).History]
    (assessment : (onePacketInformation setup leaks bounds horizon
      scheduler).BehavioralAssessment)
    (first second : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who)
    (reach base : (onePacketProtocol setup leaks bounds horizon scheduler).History → ℝ)
    (regular : (onePacketProtocol setup leaks bounds horizon scheduler).History → Prop)
    (reach_nonneg : ∀ history, 0 ≤ reach history)
    (base_nonneg : ∀ history, regular history → 0 ≤ base history)
    (bayes : ∀ (site : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationSite who) (history : (onePacketInformation setup leaks bounds
        horizon scheduler).InformationHistory who site.1), site = first ∨ site = second →
      (assessment.belief who site history).toReal = reach history.1 /
        ∑' other : (onePacketInformation setup leaks bounds horizon
          scheduler).InformationHistory who site.1, reach other.1)
    (scale₁ scale₂ ε ρ : ℝ) (scale₁_pos : 0 < scale₁) (scale₂_pos : 0 < scale₂) (ε_lt : ε < 1)
    (close₁ : ∀ history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who first.1, regular history.1 →
      |reach history.1 - scale₁ * base history.1| ≤ ε * (scale₁ * base history.1))
    (close₂ : ∀ history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who second.1, regular history.1 →
      |reach history.1 - scale₂ * base history.1| ≤ ε * (scale₂ * base history.1))
    (irregular₁ : ∑' history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who first.1,
        (if regular history.1 then 0 else reach history.1) ≤
      ρ * ∑' history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who first.1,
        if regular history.1 then reach history.1 else 0)
    (irregular₂ : ∑' history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who second.1,
        (if regular history.1 then 0 else reach history.1) ≤
      ρ * ∑' history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who second.1,
        if regular history.1 then reach history.1 else 0)
    (payoff : List (Option (OperationalState setup leaks)) → ℝ)
    (unit : ∀ record, 0 ≤ payoff record ∧ payoff record ≤ 1)
    (base₁_pos : 0 < ∑' history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who first.1,
        (if regular history.1 then base history.1 else 0))
    (base₂_pos : 0 < ∑' history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who second.1,
        (if regular history.1 then base history.1 else 0))
    (agree : BaseLawAgrees base regular first second payoff) :
    |expect ((assessment.belief who first).map fun history =>
        operationalRecord setup leaks bounds horizon scheduler history.1.trace) payoff -
      expect ((assessment.belief who second).map fun history =>
        operationalRecord setup leaks bounds horizon scheduler history.1.trace) payoff| ≤
      4 * ρ + 4 * ε / (1 - ε) := by
  let := Fintype.ofFinite ((onePacketInformation setup leaks bounds horizon
    scheduler).InformationHistory who first.1)
  let := Fintype.ofFinite ((onePacketInformation setup leaks bounds horizon
    scheduler).InformationHistory who second.1)
  simp only [tsum_fintype] at irregular₁ irregular₂ base₁_pos base₂_pos
  rw [expect_map, expect_map, expect_eq_sum, expect_eq_sum]
  have firstSum : (∑ history, (assessment.belief who first history).toReal *
      (payoff ∘ fun history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who first.1 =>
        operationalRecord setup leaks bounds horizon scheduler history.1.trace) history) =
      ∑ history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory
        who first.1, reach history.1 / (∑ other : (onePacketInformation setup leaks bounds
          horizon scheduler).InformationHistory who first.1, reach other.1) *
        payoff (operationalRecord setup leaks bounds horizon scheduler history.1.trace) :=
    Finset.sum_congr rfl fun history _ => by
      rw [bayes first history (Or.inl rfl), tsum_fintype]
      rfl
  have secondSum : (∑ history, (assessment.belief who second history).toReal *
      (payoff ∘ fun history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who second.1 =>
        operationalRecord setup leaks bounds horizon scheduler history.1.trace) history) =
      ∑ history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory
        who second.1, reach history.1 / (∑ other : (onePacketInformation setup leaks bounds
          horizon scheduler).InformationHistory who second.1, reach other.1) *
        payoff (operationalRecord setup leaks bounds horizon scheduler history.1.trace) :=
    Finset.sum_congr rfl fun history _ => by
      rw [bayes second history (Or.inr rfl), tsum_fintype]
      rfl
  rw [firstSum, secondSum]
  exact abs_normalized_sub_le_of_base_agree
    (α := (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory
      who first.1)
    (β := (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory
      who second.1)
    (fun history => reach history.1) (fun history => reach history.1)
    (fun history => base history.1) (fun history => base history.1)
    (fun history => regular history.1) (fun history => regular history.1)
    (fun history => operationalRecord setup leaks bounds horizon scheduler history.1.trace)
    (fun history => operationalRecord setup leaks bounds horizon scheduler history.1.trace)
    (fun history => reach_nonneg _) (fun history => reach_nonneg _)
    (fun history => base_nonneg _) (fun history => base_nonneg _) scale₁ scale₂ scale₁_pos
    scale₂_pos ε ρ ε_lt close₁ close₂ base₁_pos base₂_pos irregular₁ irregular₂ payoff unit
    agree

end Vegas
