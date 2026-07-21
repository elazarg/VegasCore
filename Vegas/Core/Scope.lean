/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.Obligations

/-!
# Visibility scoping and observation

This file records visibility predicates and observation-equivalence lemmas for
Vegas contexts. Commit guards in the core syntax are typed over the acting
player's view, so commit visibility is enforced by the guard type itself.

- `visibleVars who Γ` characterizes what player `who` can observe in context `Γ`

These predicates let us reason about visibility without re-encoding it into the
raw core syntax.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Variable identifiers publicly observable in a visibility context. -/
def publicVars : VCtx P L → Finset VarId
  | [] => ∅
  | (x, ⟨_, .pub⟩) :: Γ => insert x (publicVars Γ)
  | (_, ⟨_, .sealed _⟩) :: Γ => publicVars Γ

/-- Variable identifiers observable to player `who` in a visibility context. -/
def visibleVars (who : P) : VCtx P L → Finset VarId
  | [] => ∅
  | (x, ⟨_, .pub⟩) :: Γ => insert x (visibleVars who Γ)
  | (x, ⟨_, .sealed owner⟩) :: Γ =>
      if who = owner then insert x (visibleVars who Γ) else visibleVars who Γ

/-- Public variables are visible to every player. -/
theorem publicVars_subset_visibleVars
    (who : P) {Γ : VCtx P L} :
    publicVars Γ ⊆ visibleVars (L := L) who Γ := by
  induction Γ with
  | nil =>
      intro _ hx
      simp [publicVars] at hx
  | cons hd tl ih =>
      obtain ⟨z, τ⟩ := hd
      match τ with
      | ⟨b, .pub⟩ =>
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (ih hy)
      | ⟨b, .sealed owner⟩ =>
          by_cases hown : who = owner
          · intro y hy
            simpa [visibleVars, hown] using Finset.mem_insert_of_mem (ih hy)
          · simpa [publicVars, visibleVars, hown] using ih

/-- Every visible variable comes from the ambient visibility context. -/
theorem mem_visibleVars_map_fst
    {who : P} {Γ : VCtx P L} {x : VarId} :
    x ∈ visibleVars (L := L) who Γ → x ∈ Γ.map Prod.fst := by
  induction Γ with
  | nil =>
      intro hx
      simp [visibleVars] at hx
  | cons hd tl ih =>
      obtain ⟨z, τ⟩ := hd
      match τ with
      | ⟨b, .pub⟩ =>
          intro hx
          rcases Finset.mem_insert.mp (by simpa [visibleVars] using hx) with rfl | htl
          · simp
          · exact List.mem_cons_of_mem _ (ih htl)
      | ⟨b, .sealed owner⟩ =>
          by_cases hown : who = owner
          · intro hx
            subst hown
            rcases Finset.mem_insert.mp (by simpa [visibleVars] using hx) with rfl | htl
            · simp
            · exact List.mem_cons_of_mem _ (ih htl)
          · intro hx
            exact List.mem_cons_of_mem _ (ih (by simpa [visibleVars, hown] using hx))

/-- Every visible variable also appears in the projected view's name list. -/
theorem mem_viewVCtx_map_fst_of_visible
    {who : P} {Γ : VCtx P L} {x : VarId}
    (hx : x ∈ visibleVars (L := L) who Γ) :
    x ∈ (viewVCtx who Γ).map Prod.fst := by
  induction Γ with
  | nil => simp [visibleVars] at hx
  | cons hd tl ih =>
    obtain ⟨z, σ⟩ := hd
    match σ with
    | ⟨υ, .pub⟩ =>
      simp only [visibleVars] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp [viewVCtx, canSee]
      · have := ih hx; simp [viewVCtx, canSee, this]
    | ⟨υ, .sealed owner⟩ =>
      by_cases hown : who = owner
      · subst hown
        simp only [visibleVars, ite_true] at hx
        have hsee :
            canSee (L := L) who (.sealed who υ : BindTy P L) = true := by
          simp [canSee, Visibility.canSee]
        simp only [viewVCtx, hsee, if_true, List.map_cons, List.mem_cons]
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (by simpa using ih hx)
      · simp only [visibleVars, hown, ite_false] at hx
        have hsee :
            canSee (L := L) who (.sealed owner υ : BindTy P L) = false := by
          simp [canSee, Visibility.canSee, hown]
        simp only [viewVCtx, hsee]
        simpa using ih hx

/-- Every variable in a projected view is visible in the original context. -/
theorem mem_visibleVars_of_viewVCtx_map_fst
    {who : P} {Γ : VCtx P L} {x : VarId}
    (hx : x ∈ (viewVCtx who Γ).map Prod.fst) :
    x ∈ visibleVars (L := L) who Γ := by
  induction Γ with
  | nil =>
      simp [viewVCtx] at hx
  | cons hd tl ih =>
      obtain ⟨z, σ⟩ := hd
      match σ with
      | ⟨υ, .pub⟩ =>
          simp only [viewVCtx, canSee, Visibility.canSee_pub, if_true,
            List.map_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp [visibleVars]
          · exact Finset.mem_insert_of_mem (ih hx)
      | ⟨υ, .sealed owner⟩ =>
          by_cases hown : who = owner
          · subst owner
            have hsee :
                canSee (L := L) who (.sealed who υ : BindTy P L) = true := by
              simp [canSee, Visibility.canSee]
            simp only [viewVCtx, hsee, if_true, List.map_cons,
              List.mem_cons] at hx
            rcases hx with rfl | hx
            · simp [visibleVars]
            · simpa [visibleVars] using Finset.mem_insert_of_mem (ih hx)
          · have hsee :
                canSee (L := L) who (.sealed owner υ : BindTy P L) = false := by
              simp [canSee, Visibility.canSee, hown]
            simp only [viewVCtx, hsee] at hx
            simpa [visibleVars, hown] using ih hx

/-- A freshly introduced sealed variable owned by another player is not visible
    in the extended context. -/
theorem not_mem_visibleVars_sealed_other
    {Γ : VCtx P L} {x : VarId} {who owner : P} {τ : L.Ty}
    (hfresh : Fresh x Γ)
    (hneq : who ≠ owner) :
    x ∉ visibleVars (L := L) who ((x, .sealed owner τ) :: Γ) := by
  intro hx
  apply hfresh
  exact mem_visibleVars_map_fst (L := L) (who := who) (by simpa [visibleVars, hneq] using hx)

end Vegas
