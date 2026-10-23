/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactivePolicyMixture

/-! # Exact response likelihoods under immutable private-policy mixtures -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal Memory : Type} (app : ReactiveApplication Principal)

/-- The actual recalled-response product equals the chronological indexed
product at the full original input of each recorded action. -/
theorem privateTranscriptFrom_product (policy : app.Policy)
    (earlier suffix : List app.PlayerEntry) :
    (((app.privateTranscriptFrom earlier suffix).map (fun record =>
      policy record.1.1 record.1.2 record.2)).prod).toReal =
      ∏ index : Fin suffix.length,
        (policy (earlier ++ suffix.take index.val) suffix[index.val].beforeView
          suffix[index.val].action).toReal := by
  induction suffix generalizing earlier with
  | nil => simp only [privateTranscriptFrom, List.map_nil, List.prod_nil, ENNReal.toReal_one,
      List.length_nil, Finset.univ_eq_empty, Finset.prod_empty]
  | cons entry suffix ih =>
      rw [privateTranscriptFrom, List.map_append, List.prod_append, ENNReal.toReal_mul, ih]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      simp only [List.length_cons]
      rw [Fin.prod_univ_succ]
      simp only [Fin.val_zero, List.take_zero, List.append_nil, List.getElem_cons_zero]
      rw [mul_comm]
      apply congrArg (fun rest => (policy earlier entry.beforeView entry.action).toReal * rest)
      apply Finset.prod_congr rfl
      intro index _member
      simp only [Fin.val_succ, List.take_succ_cons, List.getElem_cons_succ,
        List.append_assoc, List.singleton_append]

end Interaction.ReactiveApplication
