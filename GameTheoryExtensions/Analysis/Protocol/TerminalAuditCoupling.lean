/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.TerminalAudit
import GameTheory.Math.Probability.Bounds

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
faces a charge; an already certain fine cannot be counted twice. -/
theorem settlement_le_of_departure_coupling
    (coupled : PMF Joint) (original repaired : Joint → Outcome)
    (base : Outcome → Player → ℝ) (observe : Outcome → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    (who : Player) (departed : Set Joint) (gap coverage : ℝ)
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
  have gain := coupled.expect_le_add_event_gap departed
    (fun pair => base (repaired pair) who) (fun pair => base (original pair) who)
    gap outside inside
  have massNonnegative : 0 ≤ (coupled.toOuterMeasure departed).toReal := ENNReal.toReal_nonneg
  have enough := mul_le_mul_of_nonneg_left sufficient massNonnegative
  have collected := mul_le_mul_of_nonneg_right collection nonnegative
  simp only [expect_map] at collected
  simp only [FinDist.expect_bind, settlement_expect, utility, FinDist.expect_sub,
    FinDist.expect_mul_const, expect_map]
  nlinarith

end GameTheory.Enforcement.TerminalAudit
