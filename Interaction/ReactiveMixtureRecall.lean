/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePolicyMixture
import Interaction.ReactiveRecovery

/-! # Possible policy members agree with the actual supported own recall -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal) {Index : Type}

/-- Every member still possible after a genuinely supported own transcript
supports every remembered response at its original full input. -/
theorem policyMixture_member_consistent (initial : PMF Index) (family : Index → app.Policy)
    (past : List app.PlayerEntry)
    (consistent : (app.policyMixture initial family).policy.Consistent past)
    (index : Index)
    (supported : index ∈ ((app.policyMixture initial family).posterior past).support) :
    (family index).Consistent past := by
  induction consistent generalizing index with
  | nil => exact .nil
  | @snoc earlier entry prior sampled ih =>
      obtain ⟨saved, previous, produced⟩ :=
        (app.policyMixture initial family).mem_support_posterior_snoc earlier entry sampled index
          supported
      obtain ⟨action, allowed, equal⟩ := PMF.support_map .. ▸ produced
      have savedEq : saved = index := congrArg Prod.snd equal
      subst saved
      have actionEq : action = entry.action := congrArg Prod.fst equal
      exact .snoc entry (ih index previous) (actionEq ▸ allowed)

end Interaction.ReactiveApplication
