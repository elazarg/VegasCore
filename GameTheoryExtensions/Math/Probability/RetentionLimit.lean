module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import GameTheory.Math.Probability.Convergence

@[expose] public section

/-! # Exact limits from asymptotically retained probability mass -/

namespace GameTheory.Math.Probability

open Filter

/-- If one converging law retains an asymptotically full fraction of another,
their limits agree. No finiteness assumption on the carrier is needed. -/
theorem pmf_limit_eq_of_retained_mass
    {α : Type*} {pseq qseq : ℕ → PMF α} {p q : PMF α} {retention : ℕ → ℝ}
    (pconv : PMFConvergesPointwise pseq p)
    (qconv : PMFConvergesPointwise qseq q)
    (rconv : Tendsto retention atTop (nhds 1))
    (retained : ∀ n a, retention n * (qseq n a).toReal ≤ (pseq n a).toReal) : p = q := by
  have lower (a : α) : (q a).toReal ≤ (p a).toReal := by
    have lhs := rconv.mul (qconv.toReal a)
    simpa only [one_mul] using
      le_of_tendsto_of_tendsto lhs (pconv.toReal a)
        (Eventually.of_forall fun n => retained n a)
  apply PMF.ext
  intro a
  have same : (p a).toReal = (q a).toReal := by
    by_contra different
    have strict : (q a).toReal < (p a).toReal := lt_of_le_of_ne (lower a) (Ne.symm different)
    have impossible := (pmf_weight_summable q).tsum_lt_tsum lower strict (pmf_weight_summable p)
    simp only [pmf_weight_tsum_one, lt_self_iff_false] at impossible
  have mapped := congrArg ENNReal.ofReal same
  simpa only [ENNReal.ofReal_toReal (p.apply_ne_top a),
    ENNReal.ofReal_toReal (q.apply_ne_top a)] using mapped

end GameTheory.Math.Probability
