/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMixtureRecall

/-! # Supported immutable members generate supported behavioral recall -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal) {Index : Type}

/-- A member sampled from the original prior supports an entire own recall
only if the actual behavioral implementation supports it and retains that
same immutable member. No equal-atom or full-support assumption is needed. -/
theorem policyMixture_consistent_of_supported_member
    (initial : PMF Index) (family : Index → (app).Policy) (index : Index)
    (admitted : index ∈ initial.support) (past : List (app).PlayerEntry)
    (compatible : (family index).Consistent past) :
    ((app).policyMixture initial family).policy.Consistent past ∧
      index ∈ (((app).policyMixture initial family).posterior past).support := by
  induction compatible with
  | nil => exact ⟨.nil, admitted⟩
  | @snoc earlier entry previous supported ih =>
      let implementation := (app).policyMixture initial family
      have sampled : entry.action ∈ (implementation.policy earlier entry.beforeView).support := by
        rw [policyMixture_policy, PMF.support_bind]
        exact Set.mem_iUnion₂.mpr ⟨index, ih.2, supported⟩
      refine ⟨.snoc entry ih.1 sampled, ?_⟩
      let joint := (implementation.posterior earlier).bind fun saved =>
        implementation.respond saved (earlier, entry.beforeView)
      have produced : (entry.action, index) ∈ joint.support := by
        rw [PMF.support_bind]
        refine Set.mem_iUnion₂.mpr ⟨index, ih.2, ?_⟩
        change (entry.action, index) ∈
          ((family index earlier entry.beforeView).map (fun action => (action, index))).support
        exact (PMF.mem_support_map_iff ..).mpr ⟨entry.action, supported, rfl⟩
      have positive : entry.action ∈ (joint.map Prod.fst).support :=
        (PMF.mem_support_map_iff ..).mpr ⟨(entry.action, index), produced, rfl⟩
      rw [Implementation.posterior_snoc, PMF.support_map]
      refine ⟨(entry.action, index), ?_, rfl⟩
      rw [fiberPosterior_support _ _ _ positive]
      exact ⟨rfl, produced⟩

end Interaction.ReactiveApplication
