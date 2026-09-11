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

open GameTheory GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Representatives and extracted actions for one guarded source decision. -/
structure SourceDecisionCheckpoints (who : P) {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    (guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool) where
  Carrier : Type
  visible : Carrier → Env L.Val (eraseVCtx (viewVCtx who Γ))
  action : (checkpoint : Carrier) →
    {value : L.Val b // evalGuard guard value (visible checkpoint) = true}
  action_congr : ∀ left right, visible left = visible right →
    (action left).1 = (action right).1

namespace SourceDecisionCheckpoints

/-- Totalize the actions represented at one decision with a reference kernel
away from represented visible environments. -/
def extend {who : P} {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    (checkpoints : SourceDecisionCheckpoints who guard)
    (reference : (visible : Env L.Val (eraseVCtx (viewVCtx who Γ))) →
      FinDist {value : L.Val b // evalGuard guard value visible = true}) :
    (visible : Env L.Val (eraseVCtx (viewVCtx who Γ))) →
      FinDist {value : L.Val b // evalGuard guard value visible = true} := by
  intro query
  if h : ∃ checkpoint : checkpoints.Carrier,
      checkpoints.visible checkpoint = query then
    let checkpoint := Classical.choose h
    have hvisible := Classical.choose_spec h
    exact FinDist.pure ⟨(checkpoints.action checkpoint).1, by
      rw [← hvisible]
      exact (checkpoints.action checkpoint).2⟩
  else
    exact reference query

/-- The totalized kernel is pure at every represented checkpoint. -/
theorem extend_at_checkpoint {who : P} {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {guard : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    (checkpoints : SourceDecisionCheckpoints who guard)
    (reference : (visible : Env L.Val (eraseVCtx (viewVCtx who Γ))) →
      FinDist {value : L.Val b // evalGuard guard value visible = true})
    (checkpoint : checkpoints.Carrier) :
    checkpoints.extend reference (checkpoints.visible checkpoint) =
      FinDist.pure (checkpoints.action checkpoint) := by
  have hexists : ∃ candidate : checkpoints.Carrier,
      checkpoints.visible candidate = checkpoints.visible checkpoint :=
    ⟨checkpoint, rfl⟩
  unfold extend
  rw [dif_pos hexists]
  let selected := Classical.choose hexists
  have hvisible : checkpoints.visible selected = checkpoints.visible checkpoint :=
    Classical.choose_spec hexists
  apply congrArg FinDist.pure
  apply Subtype.ext
  exact checkpoints.action_congr selected checkpoint hvisible

end SourceDecisionCheckpoints

/-- A checkpoint family assigns representatives to every decision occurrence
of one source program. -/
def SourcePolicyCheckpoints {Γ : VCtx P L} (prog : VegasCore P L Γ) (who : P) :=
  ∀ {Δ x b guard}, (site : SourceDecisionSite who prog Δ x b guard) →
    SourceDecisionCheckpoints who guard

namespace SourcePolicyCheckpoints

/-- Totalize checkpoint-extracted actions with a reference policy away from
the supported checkpoint views. -/
def extend {Γ : VCtx P L} {prog : VegasCore P L Γ} {who : P}
    (checkpoints : SourcePolicyCheckpoints prog who)
    (reference : SourceBehavioralPolicy prog who) : SourceBehavioralPolicy prog who :=
  fun site => (checkpoints site).extend (reference site)

/-- At every selected checkpoint representative, the total policy is exactly
the pure extracted source action. -/
theorem extend_at_checkpoint {Γ : VCtx P L} {prog : VegasCore P L Γ} {who : P}
    (checkpoints : SourcePolicyCheckpoints prog who)
    (reference : SourceBehavioralPolicy prog who)
    {Δ x b guard} (site : SourceDecisionSite who prog Δ x b guard)
    (checkpoint : (checkpoints site).Carrier) :
    checkpoints.extend reference site ((checkpoints site).visible checkpoint) =
      FinDist.pure ((checkpoints site).action checkpoint) := by
  exact (checkpoints site).extend_at_checkpoint (reference site) checkpoint

/-- Lift checkpoints through a source sample. -/
def sample {Γ : VCtx P L} {sampleName : VarId} {sampleTy : L.Ty}
    {dist : L.DistExpr (erasePubVCtx Γ) sampleTy}
    {tail : VegasCore P L ((sampleName, .pub sampleTy) :: Γ)} {who : P}
    (child : SourcePolicyCheckpoints tail who) :
    SourcePolicyCheckpoints (.sample sampleName dist tail) who := by
  intro Δ x b guard site
  cases site with
  | sample inner => exact child inner

/-- Lift checkpoints through a source reveal. -/
def reveal {Γ : VCtx P L} {publicName : VarId} {actor : P} {sealedName : VarId}
    {revealTy : L.Ty} {source : VHasVar Γ sealedName (.sealed actor revealTy)}
    {tail : VegasCore P L ((publicName, .pub revealTy) :: Γ)} {who : P}
    (child : SourcePolicyCheckpoints tail who) :
    SourcePolicyCheckpoints (.reveal publicName actor sealedName source tail) who := by
  intro Δ x b guard site
  cases site with
  | reveal inner => exact child inner

/-- Glue checkpoints for an owned commitment head to its continuation. -/
def ownedCommit {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((name, .sealed who ty) :: Γ)}
    (head : SourceDecisionCheckpoints who guard)
    (child : SourcePolicyCheckpoints tail who) :
    SourcePolicyCheckpoints (.commit name who guard tail) who := by
  intro Δ x b innerGuard site
  cases site with
  | here => exact head
  | commit inner => exact child inner

/-- Lift checkpoints through a commitment owned by another principal. -/
def otherCommit {Γ : VCtx P L} {name : VarId} {actor who : P} (hne : actor ≠ who)
    {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx actor Γ)) L.bool}
    {tail : VegasCore P L ((name, .sealed actor ty) :: Γ)}
    (child : SourcePolicyCheckpoints tail who) :
    SourcePolicyCheckpoints (.commit name actor guard tail) who := by
  intro Δ x b innerGuard site
  cases site with
  | here => exact False.elim (hne rfl)
  | commit inner => exact child inner

/-- The returned source program has no decision occurrences. -/
def ret {Γ : VCtx P L} {payouts : List (P × L.Expr (erasePubVCtx Γ) L.int)} {who : P} :
    SourcePolicyCheckpoints (.ret payouts) who := by
  intro Δ x b guard site
  cases site

/-- Updating one source player commutes with passage through a sample. -/
theorem update_extend_afterSample {Γ : VCtx P L} {sampleName : VarId} {sampleTy : L.Ty}
    {dist : L.DistExpr (erasePubVCtx Γ) sampleTy}
    {tail : VegasCore P L ((sampleName, .pub sampleTy) :: Γ)}
    (profile : SourceBehavioralProfile (.sample sampleName dist tail)) (focal : P)
    (child : SourcePolicyCheckpoints tail focal) :
    SourceBehavioralProfile.afterSample
      (Profile.update (sig := sourceGameSignature (.sample sampleName dist tail)) profile focal
        (SourcePolicyCheckpoints.extend (sample child) (profile focal))) =
        Profile.update (sig := sourceGameSignature tail) profile.afterSample focal
          (SourcePolicyCheckpoints.extend child (profile.afterSample focal)) := by
  funext who Δ x b innerGuard site visible
  by_cases hwho : who = focal
  · subst who
    simp [SourceBehavioralProfile.afterSample, SourcePolicyCheckpoints.extend,
      SourcePolicyCheckpoints.sample]
  · simp [SourceBehavioralProfile.afterSample, Profile.update_of_ne, hwho]

/-- Updating one source player commutes with passage through a reveal. -/
theorem update_extend_afterReveal {Γ : VCtx P L} {publicName sealedName : VarId}
    {actor focal : P} {revealTy : L.Ty}
    {source : VHasVar Γ sealedName (.sealed actor revealTy)}
    {tail : VegasCore P L ((publicName, .pub revealTy) :: Γ)}
    (profile : SourceBehavioralProfile (.reveal publicName actor sealedName source tail))
    (child : SourcePolicyCheckpoints tail focal) :
    SourceBehavioralProfile.afterReveal
      (Profile.update (sig := sourceGameSignature
          (.reveal publicName actor sealedName source tail)) profile focal
        (SourcePolicyCheckpoints.extend (reveal child) (profile focal))) =
        Profile.update (sig := sourceGameSignature tail) profile.afterReveal focal
          (SourcePolicyCheckpoints.extend child (profile.afterReveal focal)) := by
  funext who Δ x b innerGuard site visible
  by_cases hwho : who = focal
  · subst who
    simp [SourceBehavioralProfile.afterReveal, SourcePolicyCheckpoints.extend,
      SourcePolicyCheckpoints.reveal]
  · simp [SourceBehavioralProfile.afterReveal, Profile.update_of_ne, hwho]

/-- The continuation of an owned commitment receives the child checkpoint
extension of the updated profile. -/
theorem update_ownedCommit_afterCommit {Γ : VCtx P L} {name : VarId} {focal : P}
    {ty : L.Ty} {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx focal Γ)) L.bool}
    {tail : VegasCore P L ((name, .sealed focal ty) :: Γ)}
    (profile : SourceBehavioralProfile (.commit name focal guard tail))
    (head : SourceDecisionCheckpoints focal guard)
    (child : SourcePolicyCheckpoints tail focal) :
    SourceBehavioralProfile.afterCommit
      (Profile.update (sig := sourceGameSignature (.commit name focal guard tail)) profile focal
        (SourcePolicyCheckpoints.extend (ownedCommit head child) (profile focal))) =
        Profile.update (sig := sourceGameSignature tail) profile.afterCommit focal
          (SourcePolicyCheckpoints.extend child (profile.afterCommit focal)) := by
  funext who Δ x b innerGuard site visible
  by_cases hwho : who = focal
  · subst who
    simp [SourceBehavioralProfile.afterCommit, SourcePolicyCheckpoints.extend,
      SourcePolicyCheckpoints.ownedCommit]
  · simp [SourceBehavioralProfile.afterCommit, Profile.update_of_ne, hwho]

/-- The continuation of a commitment owned by another player receives the
child checkpoint extension of the updated focal profile. -/
theorem update_otherCommit_afterCommit {Γ : VCtx P L} {name : VarId} {actor focal : P}
    (hne : actor ≠ focal) {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx actor Γ)) L.bool}
    {tail : VegasCore P L ((name, .sealed actor ty) :: Γ)}
    (profile : SourceBehavioralProfile (.commit name actor guard tail))
    (child : SourcePolicyCheckpoints tail focal) :
    SourceBehavioralProfile.afterCommit
      (Profile.update (sig := sourceGameSignature (.commit name actor guard tail)) profile focal
        (SourcePolicyCheckpoints.extend (otherCommit hne child) (profile focal))) =
        Profile.update (sig := sourceGameSignature tail) profile.afterCommit focal
          (SourcePolicyCheckpoints.extend child (profile.afterCommit focal)) := by
  funext who Δ x b innerGuard site visible
  by_cases hwho : who = focal
  · subst who
    simp [SourceBehavioralProfile.afterCommit, SourcePolicyCheckpoints.extend,
      SourcePolicyCheckpoints.otherCommit]
  · simp [SourceBehavioralProfile.afterCommit, Profile.update_of_ne, hwho]

/-- At an owned head, the updated profile evaluates to the totalized head
checkpoint kernel. -/
theorem update_ownedCommit_here {Γ : VCtx P L} {name : VarId} {focal : P}
    {ty : L.Ty} {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx focal Γ)) L.bool}
    {tail : VegasCore P L ((name, .sealed focal ty) :: Γ)}
    (profile : SourceBehavioralProfile (.commit name focal guard tail))
    (head : SourceDecisionCheckpoints focal guard)
    (child : SourcePolicyCheckpoints tail focal)
    (visible : Env L.Val (eraseVCtx (viewVCtx focal Γ))) :
    Profile.update (sig := sourceGameSignature (.commit name focal guard tail)) profile focal
        (SourcePolicyCheckpoints.extend (ownedCommit head child) (profile focal)) focal
          (.here guard tail) visible =
      SourceDecisionCheckpoints.extend head (profile focal (.here guard tail)) visible := by
  simp [SourcePolicyCheckpoints.extend, SourcePolicyCheckpoints.ownedCommit]

/-- Updating a different player leaves the commitment owner's head kernel
unchanged. -/
theorem update_otherCommit_here {Γ : VCtx P L} {name : VarId} {actor focal : P}
    (hne : actor ≠ focal) {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx actor Γ)) L.bool}
    {tail : VegasCore P L ((name, .sealed actor ty) :: Γ)}
    (profile : SourceBehavioralProfile (.commit name actor guard tail))
    (child : SourcePolicyCheckpoints tail focal)
    (visible : Env L.Val (eraseVCtx (viewVCtx actor Γ))) :
    Profile.update (sig := sourceGameSignature (.commit name actor guard tail)) profile focal
        (SourcePolicyCheckpoints.extend (otherCommit hne child) (profile focal)) actor
          (.here guard tail) visible =
      profile actor (.here guard tail) visible := by
  rw [Profile.update_of_ne (sig := sourceGameSignature (.commit name actor guard tail))
    profile _ hne]

end SourcePolicyCheckpoints

end Vegas

/-- info: 'Vegas.SourceDecisionCheckpoints.extend_at_checkpoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceDecisionCheckpoints.extend_at_checkpoint

/-- info: 'Vegas.SourcePolicyCheckpoints.extend_at_checkpoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourcePolicyCheckpoints.extend_at_checkpoint

/-- info: 'Vegas.SourcePolicyCheckpoints.update_extend_afterSample' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourcePolicyCheckpoints.update_extend_afterSample

/-- info: 'Vegas.SourcePolicyCheckpoints.update_extend_afterReveal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourcePolicyCheckpoints.update_extend_afterReveal

/-- info: 'Vegas.SourcePolicyCheckpoints.update_ownedCommit_afterCommit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourcePolicyCheckpoints.update_ownedCommit_afterCommit

/-- info: 'Vegas.SourcePolicyCheckpoints.update_otherCommit_afterCommit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourcePolicyCheckpoints.update_otherCommit_afterCommit
