import Mathlib.Probability.ProbabilityMassFunction.Basic
import Vegas.Scope

/-!
# Vegas view kernels

Reusable view-indexed kernel primitives for Vegas strategies.

The user-facing strategic objects now live in the fixed-program modules
`Vegas.Strategic` and `Vegas.PureStrategic`. This file keeps only the common
view/projection machinery they share.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The visible erased environment available to player `who` in context `Γ`. -/
abbrev ViewEnv (who : P) (Γ : VCtx P L) : Type :=
  Env L.Val (eraseVCtx (viewVCtx who Γ))

/-- A deterministic choice rule indexed by a player's actual view. -/
abbrev PureKernel (who : P) (Γ : VCtx P L) (b : L.Ty) : Type :=
  ViewEnv (P := P) (L := L) who Γ → L.Val b

/-- A behavioral choice rule indexed by a player's actual view. -/
abbrev BehavioralKernel (who : P) (Γ : VCtx P L) (b : L.Ty) : Type :=
  ViewEnv (P := P) (L := L) who Γ → FDist (L.Val b)

private theorem visibleVars_cons_of_canSee_true
    {who : P} {y : VarId} {σ : BindTy P L} {Γ : VCtx P L}
    (hsee : canSee who σ = true) :
    visibleVars (L := L) who ((y, σ) :: Γ) =
      insert y (visibleVars (L := L) who Γ) := by
  cases σ with
  | pub b =>
      simp [visibleVars]
  | hidden owner b =>
      by_cases hown : who = owner
      · simp [visibleVars, hown]
      · simp [canSee, hown] at hsee

private theorem visibleVars_cons_of_canSee_false
    {who : P} {y : VarId} {σ : BindTy P L} {Γ : VCtx P L}
    (hsee : canSee who σ = false) :
    visibleVars (L := L) who ((y, σ) :: Γ) =
      visibleVars (L := L) who Γ := by
  cases σ with
  | pub b =>
      simp [canSee] at hsee
  | hidden owner b =>
      by_cases hown : who = owner
      · simp [canSee, hown] at hsee
      · simp [visibleVars, hown]

private theorem mem_visibleVars_of_view_member
    {who : P} {Γ : VCtx P L} {x : VarId} :
    x ∈ (viewVCtx who Γ).map Prod.fst →
      x ∈ visibleVars (L := L) who Γ := by
  induction Γ with
  | nil =>
      intro hx
      simp [viewVCtx] at hx
  | cons hd tl ih =>
      obtain ⟨y, σ⟩ := hd
      cases hsee : canSee who σ with
      | true =>
        intro hx
        have hview : viewVCtx who ((y, σ) :: tl) = (y, σ) :: viewVCtx who tl := by
          simp [viewVCtx, hsee]
        rw [hview] at hx
        simp only [List.map, List.mem_cons] at hx
        rcases hx with rfl | htl
        · rw [visibleVars_cons_of_canSee_true (L := L) hsee]
          exact Finset.mem_insert_self _ _
        · rw [visibleVars_cons_of_canSee_true (L := L) hsee]
          exact Finset.mem_insert_of_mem (ih htl)
      | false =>
        intro hx
        have hview : viewVCtx who ((y, σ) :: tl) = viewVCtx who tl := by
          simp [viewVCtx, hsee]
        rw [hview] at hx
        rw [visibleVars_cons_of_canSee_false (L := L) hsee]
        exact ih hx

private theorem view_member_visible
    {who : P} {Γ : VCtx P L} {x : VarId} {τ : BindTy P L}
    (h : VHasVar (L := L) (viewVCtx who Γ) x τ) :
    x ∈ visibleVars (L := L) who Γ :=
  mem_visibleVars_of_view_member (L := L) (VHasVar.mem_map_fst h)

/-- Project a full erased environment to the visible erased environment for
player `who`. Defined recursively on the context for clean reduction. -/
noncomputable def projectViewEnv (who : P) {Γ : VCtx P L}
    (env : Env L.Val (eraseVCtx Γ)) :
    ViewEnv (P := P) (L := L) who Γ := by
  intro x τ h
  rcases HasVar.toVHasVar (Player := P) (L := L) (Γ := viewVCtx who Γ) h with
    ⟨σ, hv, ⟨hτ⟩⟩
  cases hτ
  exact env _ _ (VHasVar.toErased (Player := P) (L := L) (VHasVar.ofViewVCtx (p := who) hv))

theorem projectViewEnv_eq_of_obsEq
    {who : P} {Γ : VCtx P L}
    {ρ₁ ρ₂ : Env L.Val (eraseVCtx Γ)}
    (hobs : ObsEq (L := L) (Γ := Γ) who ρ₁ ρ₂) :
    projectViewEnv (P := P) (L := L) who ρ₁ =
      projectViewEnv (P := P) (L := L) who ρ₂ := by
  funext x τ h
  dsimp [projectViewEnv]
  rcases HasVar.toVHasVar (Player := P) (L := L) (Γ := viewVCtx who Γ) h with
    ⟨σ, hv, ⟨hτ⟩⟩
  cases hτ
  exact hobs x σ.base
    (VHasVar.toErased (Player := P) (L := L) (VHasVar.ofViewVCtx (p := who) hv))
    (view_member_visible (L := L) hv)

/-- If the views through `VEnv.cons v₁ env₁` and `VEnv.cons v₂ env₂` agree,
then the views through `env₁` and `env₂` agree (on old variables). -/
theorem projectViewEnv_cons_eq
    {who : P} {Γ : VCtx P L} {x : VarId} {τ : BindTy P L}
    {env₁ env₂ : VEnv (Player := P) L Γ}
    {v₁ v₂ : L.Val τ.base}
    (hnodup : (((x, τ) :: Γ).map Prod.fst).Nodup)
    (h : projectViewEnv (P := P) (L := L) who
        (VEnv.eraseEnv (VEnv.cons (L := L) (x := x) (τ := τ) v₁ env₁)) =
      projectViewEnv (P := P) (L := L) who
        (VEnv.eraseEnv (VEnv.cons (L := L) (x := x) (τ := τ) v₂ env₂))) :
    projectViewEnv (P := P) (L := L) who
        (VEnv.eraseEnv env₁) =
      projectViewEnv (P := P) (L := L) who
        (VEnv.eraseEnv env₂) := by
  -- Step 1: projectViewEnv eq → ObsEq for extended context
  -- (converse of projectViewEnv_eq_of_obsEq — needs viewVCtx/HasVar infrastructure)
  -- nodup of erased context names (from hnodup + eraseVCtx preserves names)
  have hnodup_e : ((eraseVCtx ((x, τ) :: Γ)).map Prod.fst).Nodup := by
    rwa [eraseVCtx_map_fst]
  have hobs_ext : ObsEq (L := L) (Γ := (x, τ) :: Γ) who
      (VEnv.eraseEnv (VEnv.cons v₁ env₁)) (VEnv.eraseEnv (VEnv.cons v₂ env₂)) := by
    intro y' σ₀ hy' hvis'
    -- y' is visible → construct HasVar in eraseVCtx(viewVCtx) via Classical
    have hmem : y' ∈ ((x, τ) :: Γ).map Prod.fst :=
      mem_visibleVars_map_fst hvis'
    have hmem_view : y' ∈ (viewVCtx who ((x, τ) :: Γ)).map Prod.fst := by
      sorry -- mem_viewVCtx_map_fst_of_visible (not in scope)
    -- From name membership, get (y', σ_v) ∈ viewVCtx
    rcases List.mem_map.mp hmem_view with ⟨⟨_, σ_v⟩, hmem_v, hfst⟩
    simp at hfst; subst hfst
    -- Construct HasVar in eraseVCtx(viewVCtx) using classical choice
    have h_view : HasVar (eraseVCtx (viewVCtx who ((x, τ) :: Γ))) y' σ_v.base :=
      (VHasVar.ofMem hmem_v).toErased
    -- Extract from projectViewEnv equality
    have h_pt := congr_fun (congr_fun (congr_fun h y') σ_v.base) h_view
    -- dsimp to expose the Env lookup
    dsimp [projectViewEnv] at h_pt
    -- h_pt gives equality at a specific HasVar proof from toVHasVar chain.
    -- By HasVar.type_unique (nodup): σ₀ = the type from the chain.
    -- By HasVar.eq_of_nodup (nodup): the HasVar proofs are equal.
    -- So env values agree at hy'.
    sorry -- final HasVar proof matching via eq_of_nodup
  -- Step 2: ObsEq for (x,τ)::Γ restricted to old vars → ObsEq for Γ
  have hobs : ObsEq (L := L) (Γ := Γ) who (VEnv.eraseEnv env₁) (VEnv.eraseEnv env₂) := by
    intro y' σ₀ hy' hvis'
    have hvis_ext : y' ∈ visibleVars (L := L) who ((x, τ) :: Γ) := by
      cases τ with
      | pub b => simp [visibleVars, hvis']
      | hidden owner b =>
        simp only [visibleVars]
        split <;> simp_all [Finset.mem_insert]
    have := hobs_ext y' σ₀ (.there hy') hvis_ext
    simp only [VEnv.eraseEnv, Env.cons] at this
    exact this
  exact projectViewEnv_eq_of_obsEq hobs

end Vegas
