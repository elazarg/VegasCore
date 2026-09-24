/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Convergence
import GameTheory.Math.Probability.Simplex
import Mathlib.Topology.Sequences

/-! # Common subsequences of finite probability laws

A finite family of finite probability simplices is compact. Extracting once
from their product gives the same subsequence for every law and coordinate.
This does not assert convergence of the original sequence or uniqueness of
the limit.
-/

noncomputable section

namespace GameTheory.Math.Probability

open Filter

theorem FinDistConvergesPointwise.subsequence {α : Type*}
    {sequence : ℕ → FinDist α} {target : FinDist α}
    (converges : FinDistConvergesPointwise sequence target)
    {index : ℕ → ℕ} (increasing : StrictMono index) :
    FinDistConvergesPointwise (fun n => sequence (index n)) target :=
  fun value => (converges value).comp increasing.tendsto_atTop

/-- One strictly increasing subsequence works simultaneously for every law in
the finite dependent family. Limits remain probability laws on their carriers. -/
theorem FinDist.exists_common_subsequence {ι : Type*} [Finite ι]
    {α : ι → Type*} [∀ i, Finite (α i)]
    (sequence : ℕ → ∀ i, FinDist (α i)) :
    ∃ limit : ∀ i, FinDist (α i), ∃ index : ℕ → ℕ,
      StrictMono index ∧
      ∀ i, FinDistConvergesPointwise (fun n => sequence (index n) i) (limit i) := by
  let _ (i : ι) : Fintype (α i) := Fintype.ofFinite _
  have compact := isCompact_pi_infinite (fun i : ι => isCompact_simplexWeights (α i))
  obtain ⟨weights, membership, index, increasing, converges⟩ :=
    compact.tendsto_subseq (fun n i => (sequence n i).prob_mem_simplexWeights)
  refine ⟨fun i => FinDist.ofSimplex (membership i), index, increasing, ?_⟩
  intro i value
  simpa only [FinDist.prob_ofSimplex, Function.comp_apply] using
    (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp converges i) value)

end GameTheory.Math.Probability
