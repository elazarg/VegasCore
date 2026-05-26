/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.WF

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
  | (_, ⟨_, .hidden _⟩) :: Γ => publicVars Γ

/-- Variable identifiers observable to player `who` in a visibility context. -/
def visibleVars (who : P) : VCtx P L → Finset VarId
  | [] => ∅
  | (x, ⟨_, .pub⟩) :: Γ => insert x (visibleVars who Γ)
  | (x, ⟨_, .hidden owner⟩) :: Γ =>
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
      | ⟨b, .hidden owner⟩ =>
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
      | ⟨b, .hidden owner⟩ =>
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
    | ⟨υ, .hidden owner⟩ =>
      by_cases hown : who = owner
      · subst hown
        simp only [visibleVars, ite_true] at hx
        have hsee :
            canSee (L := L) who (.hidden who υ : BindTy P L) = true := by
          simp [canSee, Visibility.canSee]
        simp only [viewVCtx, hsee, if_true, List.map_cons, List.mem_cons]
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (by simpa using ih hx)
      · simp only [visibleVars, hown, ite_false] at hx
        have hsee :
            canSee (L := L) who (.hidden owner υ : BindTy P L) = false := by
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
      | ⟨υ, .hidden owner⟩ =>
          by_cases hown : who = owner
          · subst owner
            have hsee :
                canSee (L := L) who (.hidden who υ : BindTy P L) = true := by
              simp [canSee, Visibility.canSee]
            simp only [viewVCtx, hsee, if_true, List.map_cons,
              List.mem_cons] at hx
            rcases hx with rfl | hx
            · simp [visibleVars]
            · simpa [visibleVars] using Finset.mem_insert_of_mem (ih hx)
          · have hsee :
                canSee (L := L) who (.hidden owner υ : BindTy P L) = false := by
              simp [canSee, Visibility.canSee, hown]
            simp only [viewVCtx, hsee] at hx
            simpa [visibleVars, hown] using ih hx

/-- Two erased environments are observationally equivalent for player `who`
    when they agree on every variable visible to `who`. -/
def ObsEq {Γ : VCtx P L} (who : P)
    (ρ₁ ρ₂ : Env L.Val (eraseVCtx Γ)) : Prop :=
  AgreesOn ρ₁ ρ₂ (visibleVars (L := L) who Γ)

theorem ObsEq.refl {Γ : VCtx P L} (who : P)
    (ρ : Env L.Val (eraseVCtx Γ)) :
    ObsEq (L := L) (Γ := Γ) who ρ ρ :=
  fun _ _ _ _ => rfl

theorem ObsEq.symm {Γ : VCtx P L} {who : P}
    {ρ₁ ρ₂ : Env L.Val (eraseVCtx Γ)}
    (h : ObsEq (L := L) (Γ := Γ) who ρ₁ ρ₂) :
    ObsEq (L := L) (Γ := Γ) who ρ₂ ρ₁ := by
  intro x τ hx hmem
  exact (h x τ hx hmem).symm

theorem ObsEq.trans {Γ : VCtx P L} {who : P}
    {ρ₁ ρ₂ ρ₃ : Env L.Val (eraseVCtx Γ)}
    (h₁₂ : ObsEq (L := L) (Γ := Γ) who ρ₁ ρ₂)
    (h₂₃ : ObsEq (L := L) (Γ := Γ) who ρ₂ ρ₃) :
    ObsEq (L := L) (Γ := Γ) who ρ₁ ρ₃ := by
  intro x τ hx hmem
  exact Eq.trans (h₁₂ x τ hx hmem) (h₂₃ x τ hx hmem)

/-- Full structural well-formedness: fresh bindings and reveal completeness. -/
def WF {Γ : VCtx P L} (p : VegasCore P L Γ) : Prop :=
  FreshBindings p ∧ RevealComplete [] p

/-- Chosen witness for `IExpr.extendAfterHead`. -/
noncomputable def extendAfterHeadExpr
    {Γ : Ctx L.Ty} {x y : VarId} {τ σ b : L.Ty}
    (e : L.Expr ((x, τ) :: Γ) b) :
    L.Expr ((x, τ) :: (y, σ) :: Γ) b :=
  Classical.choose (L.extendAfterHead e)

theorem eval_extendAfterHeadExpr
    {Γ : Ctx L.Ty} {x y : VarId} {τ σ b : L.Ty}
    (e : L.Expr ((x, τ) :: Γ) b)
    (vx : L.Val τ) (vy : L.Val σ) (env : Env L.Val Γ) :
    L.eval (extendAfterHeadExpr (L := L) (x := x) (y := y) (τ := τ) (σ := σ) e)
      (Env.cons (x := x) vx (Env.cons (x := y) vy env)) =
    L.eval e (Env.cons (x := x) vx env) :=
  (Classical.choose_spec (L.extendAfterHead e)) vx vy env

/-- Chosen witness for `IExpr.dropAfterHead`. -/
noncomputable def dropAfterHeadExpr
    {Γ : Ctx L.Ty} {x y : VarId} {τ σ b : L.Ty}
    (e : L.Expr ((x, τ) :: (y, σ) :: Γ) b)
    (hy : y ∉ L.exprDeps e) :
    L.Expr ((x, τ) :: Γ) b :=
  Classical.choose (L.dropAfterHead e hy)

theorem eval_dropAfterHeadExpr
    {Γ : Ctx L.Ty} {x y : VarId} {τ σ b : L.Ty}
    (e : L.Expr ((x, τ) :: (y, σ) :: Γ) b)
    (hy : y ∉ L.exprDeps e)
    (vx : L.Val τ) (vy : L.Val σ) (env : Env L.Val Γ) :
    L.eval (dropAfterHeadExpr (L := L) (x := x) (y := y) (τ := τ) (σ := σ) e hy)
      (Env.cons (x := x) vx env) =
    L.eval e (Env.cons (x := x) vx (Env.cons (x := y) vy env)) :=
  (Classical.choose_spec (L.dropAfterHead e hy)) vx vy env

/-- A freshly introduced hidden variable owned by another player is not visible
    in the extended context. -/
theorem not_mem_visibleVars_hidden_other
    {Γ : VCtx P L} {x : VarId} {who owner : P} {τ : L.Ty}
    (hfresh : Fresh x Γ)
    (hneq : who ≠ owner) :
    x ∉ visibleVars (L := L) who ((x, .hidden owner τ) :: Γ) := by
  intro hx
  apply hfresh
  exact mem_visibleVars_map_fst (L := L) (who := who) (by simpa [visibleVars, hneq] using hx)

end Vegas
