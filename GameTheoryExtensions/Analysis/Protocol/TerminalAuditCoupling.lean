/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.TerminalAudit
import GameTheory.Math.Probability.Bounds
import GameTheoryExtensions.Math.Probability.Expectation

/-! # Terminal audit comparison from a stopped execution coupling

Before a departure, paired executions have the same base result, or the
repaired execution is better. On the departure branch only a bounded payoff
gap is required. Incremental collection probability pays for that branch.
The result compares actual randomized settlements and assumes no optimality
or independence of the audit. Constructing the coupling is a separate task.
-/

noncomputable section

namespace GameTheory.Enforcement.TerminalAudit

open Math.Probability

variable {Player Outcome Observation Joint : Type}

/-- A joint execution law gives the terminal incentive comparison once its
departure mass bounds both the possible gain and the extra collected sanction.
Using incremental collection retains the obligation when either side already
faces a charge; an already certain fine cannot be counted twice. The base
payoff must have a finite expectation under both coupled executions. -/
theorem settlement_le_of_departure_coupling
    (coupled : PMF Joint) (original repaired : Joint → Outcome)
    (base : Outcome → Player → ℝ) (observe : Outcome → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    (who : Player) (departed : Set Joint) (gap coverage : ℝ)
    (originalIntegrable : PayoffIntegrable coupled fun pair => base (original pair) who)
    (repairedIntegrable : PayoffIntegrable coupled fun pair => base (repaired pair) who)
    (outside : ∀ pair ∈ coupled.support, pair ∉ departed →
      base (original pair) who ≤ base (repaired pair) who)
    (inside : ∀ pair ∈ coupled.support, pair ∈ departed →
      base (original pair) who ≤ base (repaired pair) who + gap)
    (collection : (coupled.toOuterMeasure departed).toReal * coverage ≤
      expect (coupled.map original) (fun outcome => charge observe audit outcome who) -
        expect (coupled.map repaired) (fun outcome => charge observe audit outcome who))
    (nonnegative : 0 ≤ deposit who) (sufficient : gap ≤ coverage * deposit who) :
    expect ((coupled.map original).bind (settlement base observe audit deposit))
        (fun payoffs => payoffs who) ≤
      expect ((coupled.map repaired).bind (settlement base observe audit deposit))
        (fun payoffs => payoffs who) := by
  have chargeBounded (outcome : Outcome) :
      |charge observe audit outcome who * deposit who| ≤ |deposit who| := by
    rw [abs_mul, charge, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_left (abs_nonneg _) (pmf_toReal_apply_le_one _ _)
  have settled (joint : Joint → Outcome)
      (integrable : PayoffIntegrable coupled fun pair => base (joint pair) who) :
      expect ((coupled.map joint).bind (settlement base observe audit deposit))
          (fun payoffs => payoffs who) =
        expect coupled (fun pair => base (joint pair) who) -
          expect coupled (fun pair => charge observe audit (joint pair) who) * deposit who := by
    have mapped : PayoffIntegrable (coupled.map joint) fun outcome => base outcome who :=
      (payoffIntegrable_map_iff _ _ _).mpr integrable
    have bound (outcome : Outcome) (_ : outcome ∈ (coupled.map joint).support)
        (payoffs : Player → ℝ)
        (supported : payoffs ∈ (settlement base observe audit deposit outcome).support) :
        |payoffs who| ≤ |base outcome who| + |deposit who| := by
      obtain ⟨verdict, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
      split <;> simp
    rw [expect_bind_tower _ _ _ (payoffIntegrable_bind_of_abs_le _ _ _ _ _ mapped bound)]
    simp only [settlement_expect, utility, expect_map, Function.comp_def]
    rw [expect_sub integrable (payoffIntegrable_of_bounded _ _ fun pair => chargeBounded _),
      expect_mul_const]
  have gain := expect_le_add_event_gap coupled departed
    (fun pair => base (repaired pair) who) (fun pair => base (original pair) who)
    gap repairedIntegrable originalIntegrable outside inside
  have massNonnegative : 0 ≤ (coupled.toOuterMeasure departed).toReal := ENNReal.toReal_nonneg
  have enough := mul_le_mul_of_nonneg_left sufficient massNonnegative
  have collected := mul_le_mul_of_nonneg_right collection nonnegative
  simp only [expect_map, Function.comp_def] at collected
  rw [settled original originalIntegrable, settled repaired repairedIntegrable]
  nlinarith

end GameTheory.Enforcement.TerminalAudit
