/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.TerminalAudit

/-! # Deterministic settlement without deductions

Binary collection at fixed deposits cannot cancel within a player's payoff.
Zero expected deductions therefore characterize the exact unchanged joint
settlement law, including zero deposits and correlated audit verdicts.
-/

noncomputable section

namespace GameTheory.Enforcement.TerminalAudit

open Math.Probability

/-- The realized settlement is the base payoff vector exactly when every
expected deduction vanishes. Deposits may be zero or negative. -/
theorem settlement_eq_pure_iff_zero_deductions {Player Outcome Observation : Type}
    (base : Outcome → Player → ℝ) (observe : Outcome → Observation)
    (audit : Observation → PMF (Player → Bool)) (deposit : Player → ℝ)
    (outcome : Outcome) :
    settlement base observe audit deposit outcome = PMF.pure (base outcome) ↔
      ∀ who, charge observe audit outcome who * deposit who = 0 := by
  constructor
  · intro same who
    have expected := settlement_expect base observe audit deposit outcome who
    rw [same, expect_pure] at expected
    unfold utility at expected
    linarith
  · intro deductions
    have unchanged (verdict : Player → Bool)
        (supported : verdict ∈ (audit (observe outcome)).support) (who : Player) :
        (if verdict who then deposit who else 0) = 0 := by
      by_cases zero : deposit who = 0
      · simp [zero]
      · have uncharged := (mul_eq_zero.mp (deductions who)).resolve_right zero
        cases selected : verdict who with
        | false => simp
        | true =>
          have possible : true ∈
              ((audit (observe outcome)).map (fun result => result who)).support := by
            rw [PMF.support_map]
            exact ⟨verdict, supported, selected⟩
          have positive := pmf_toReal_pos_iff.mpr possible
          change 0 < charge observe audit outcome who at positive
          rw [uncharged] at positive
          exact (lt_irrefl 0 positive).elim
    unfold settlement
    calc
      _ = (audit (observe outcome)).map (fun _ => base outcome) := by
        apply map_congr_on_support _
        intro verdict supported
        funext who
        rw [unchanged verdict supported who, sub_zero]
      _ = _ := by simp only [← PMF.bind_pure_comp, Function.comp_def, PMF.bind_const]

end GameTheory.Enforcement.TerminalAudit
