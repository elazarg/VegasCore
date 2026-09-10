/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Strategy

/-! # Extending source policies from supported checkpoints

A back-translation often extracts one legal source action at each supported
runtime checkpoint, but a source behavioral policy must be total on every
visible environment. The construction here uses the extracted action when a
checkpoint representative is available and a reference source policy
otherwise. No terminal outcome or continuation is selected.
-/

noncomputable section

namespace Vegas

open GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Per-decision checkpoint representatives and their extracted source data. -/
structure SourcePolicyCheckpoints {Γ : VCtx P L} (prog : VegasCore P L Γ) (who : P) where
  Carrier : ∀ {Δ x b guard}, SourceDecisionSite who prog Δ x b guard → Type
  visible : ∀ {Δ x b guard} (site : SourceDecisionSite who prog Δ x b guard),
    Carrier site → Env L.Val (eraseVCtx (viewVCtx who Δ))
  action : ∀ {Δ x b guard} (site : SourceDecisionSite who prog Δ x b guard)
    (checkpoint : Carrier site),
    {value : L.Val b // evalGuard guard value (visible site checkpoint) = true}
  action_congr : ∀ {Δ x b guard} (site : SourceDecisionSite who prog Δ x b guard)
    (left right : Carrier site), visible site left = visible site right →
    (action site left).1 = (action site right).1

namespace SourcePolicyCheckpoints

/-- Totalize checkpoint-extracted actions with a reference policy away from
the supported checkpoint views. -/
def extend {Γ : VCtx P L} {prog : VegasCore P L Γ} {who : P}
    (checkpoints : SourcePolicyCheckpoints prog who)
    (reference : SourceBehavioralPolicy prog who) : SourceBehavioralPolicy prog who := by
  intro Δ x b guard site query
  if h : ∃ checkpoint : checkpoints.Carrier site,
      checkpoints.visible site checkpoint = query then
    let checkpoint := Classical.choose h
    have hvisible := Classical.choose_spec h
    exact FinDist.pure ⟨(checkpoints.action site checkpoint).1, by
      rw [← hvisible]
      exact (checkpoints.action site checkpoint).2⟩
  else
    exact reference site query

/-- At every selected checkpoint representative, the total policy is exactly
the pure extracted source action. -/
theorem extend_at_checkpoint {Γ : VCtx P L} {prog : VegasCore P L Γ} {who : P}
    (checkpoints : SourcePolicyCheckpoints prog who)
    (reference : SourceBehavioralPolicy prog who)
    {Δ x b guard} (site : SourceDecisionSite who prog Δ x b guard)
    (checkpoint : checkpoints.Carrier site) :
    checkpoints.extend reference site (checkpoints.visible site checkpoint) =
      FinDist.pure (checkpoints.action site checkpoint) := by
  have hexists : ∃ candidate : checkpoints.Carrier site,
      checkpoints.visible site candidate = checkpoints.visible site checkpoint :=
    ⟨checkpoint, rfl⟩
  unfold extend
  rw [dif_pos hexists]
  let selected := Classical.choose hexists
  have hvisible : checkpoints.visible site selected = checkpoints.visible site checkpoint :=
    Classical.choose_spec hexists
  have hvalue := checkpoints.action_congr site selected checkpoint hvisible
  apply congrArg FinDist.pure
  apply Subtype.ext
  exact hvalue

end SourcePolicyCheckpoints

end Vegas

/-- info: 'Vegas.SourcePolicyCheckpoints.extend_at_checkpoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourcePolicyCheckpoints.extend_at_checkpoint
