import Vegas.Scope
import Vegas.ViewKernel

/-!
# View projection lemmas

Low-level facts relating equality of projected player views to observation
equivalence and guard evaluation. These are used by both the canonical cursor
execution layer and the syntax-facing strategy existence helpers.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Membership in a mapped list unpacks to a pair with matching first
component. Local helper. -/
private theorem exists_pair_of_mem_map_fst {α β : Type}
    {L : List (α × β)} {y : α} (h : y ∈ L.map Prod.fst) :
    ∃ τ : β, (y, τ) ∈ L := by
  rcases List.mem_map.1 h with ⟨⟨a, b⟩, hmem, hfst⟩
  refine ⟨b, ?_⟩
  have : a = y := hfst
  subst this
  exact hmem

/-- `HasVar Γ x τ` implies `(x, τ) ∈ Γ`. Local helper. -/
private theorem mem_of_hasVar {Ty : Type} :
    ∀ {Γ : Ctx Ty} {x : VarId} {τ : Ty}, HasVar Γ x τ → (x, τ) ∈ Γ
  | _ :: _, _, _, .here => List.mem_cons_self ..
  | _ :: _, _, _, .there h => List.mem_cons_of_mem _ (mem_of_hasVar h)

/-- Under `Nodup (L.map Prod.fst)`, the type bound to a name in a
pair list is unique. Local helper. -/
private theorem pair_snd_unique_of_nodup_map_fst {α β : Type}
    : ∀ {L : List (α × β)},
      (L.map Prod.fst).Nodup →
      ∀ {y : α} {τ₁ τ₂ : β},
        (y, τ₁) ∈ L → (y, τ₂) ∈ L → τ₁ = τ₂
  | [], _, _, _, _, h, _ => absurd h (by simp)
  | (a, b) :: tl, hnd, y, τ₁, τ₂, h₁, h₂ => by
      simp only [List.map, List.nodup_cons] at hnd
      rcases List.mem_cons.mp h₁ with heq₁ | htl₁
      · rcases List.mem_cons.mp h₂ with heq₂ | htl₂
        · -- Both hit head: (y, τ₁) = (a, b) and (y, τ₂) = (a, b).
          have e₁ : τ₁ = b := (Prod.mk.inj heq₁).2
          have e₂ : τ₂ = b := (Prod.mk.inj heq₂).2
          exact e₁.trans e₂.symm
        · exfalso
          have hy_a : y = a := (Prod.mk.inj heq₁).1
          apply hnd.1
          exact List.mem_map.2 ⟨(y, τ₂), htl₂, hy_a⟩
      · rcases List.mem_cons.mp h₂ with heq₂ | htl₂
        · exfalso
          have hy_a : y = a := (Prod.mk.inj heq₂).1
          apply hnd.1
          exact List.mem_map.2 ⟨(y, τ₁), htl₁, hy_a⟩
        · exact pair_snd_unique_of_nodup_map_fst hnd.2 htl₁ htl₂

/-- Structural converse of `projectViewEnv_eq_of_obsEq` at the
`AgreesOn` level: from equality of view projections and `WFCtx Γ`
(distinct variable names), derive that the two environments agree on
every visible variable.

Proof: `HasVar` is subsingleton under `Nodup` (via
`HasVar.eq_of_nodup`); different HasVar proofs in the erased context
collapse. Type-uniqueness for a given name is derived from `Nodup` of
the name projection. -/
theorem obsEq_of_projectViewEnv_eq
    {Γ : VCtx P L} {who : P}
    (hctx : WFCtx (L := L) Γ)
    {ρ₁ ρ₂ : Env L.Val (eraseVCtx Γ)}
    (hview : projectViewEnv who ρ₁ = projectViewEnv who ρ₂) :
    ObsEq (L := L) (Γ := Γ) who ρ₁ ρ₂ := by
  have hnodup_erase : (eraseVCtx Γ).map Prod.fst |>.Nodup := by
    rw [eraseVCtx_map_fst]; exact hctx
  intro y τ hy hvis
  have hmem_view : y ∈ (viewVCtx who Γ).map Prod.fst :=
    mem_viewVCtx_map_fst_of_visible (L := L) hvis
  have hmem_erase_view : y ∈ (eraseVCtx (viewVCtx who Γ)).map Prod.fst := by
    rw [eraseVCtx_map_fst]; exact hmem_view
  obtain ⟨τ', hpair⟩ := exists_pair_of_mem_map_fst hmem_erase_view
  have h_view : HasVar (eraseVCtx (viewVCtx who Γ)) y τ' :=
    HasVar.ofMem hpair
  rcases projectViewEnv_apply ρ₁ h_view with ⟨hy₁, hp₁⟩
  rcases projectViewEnv_apply ρ₂ h_view with ⟨hy₂, hp₂⟩
  have hview_pt : projectViewEnv who ρ₁ y τ' h_view =
      projectViewEnv who ρ₂ y τ' h_view := by rw [hview]
  rw [hp₁, hp₂] at hview_pt
  -- Extract pair memberships from HasVar proofs.
  have hmem1 : (y, τ') ∈ eraseVCtx Γ := mem_of_hasVar hy₁
  have hmem2 : (y, τ) ∈ eraseVCtx Γ := mem_of_hasVar hy
  have hτ_eq : τ' = τ :=
    pair_snd_unique_of_nodup_map_fst hnodup_erase hmem1 hmem2
  subst hτ_eq
  have h1 : hy₁ = hy := HasVar.eq_of_nodup hnodup_erase _ _
  have h2 : hy₂ = hy := HasVar.eq_of_nodup hnodup_erase _ _
  rw [h1, h2] at hview_pt
  exact hview_pt

/-- Guard evaluation is preserved under projections equality: if
two environments project to the same view (for the committer),
the guard evaluates identically on both. Combines
`obsEq_of_projectViewEnv_eq` with Scope's `evalGuard_eq_of_obsEq`. -/
theorem evalGuard_eq_of_projectViewEnv_eq
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    (hctx : WFCtx (L := L) Γ)
    (hfresh : Fresh x Γ)
    (hR : GuardUsesOnly (L := L) (Γ := Γ) (x := x) (who := who) R)
    {a : L.Val b}
    {ρ₁ ρ₂ : Env L.Val (eraseVCtx Γ)}
    (hview : projectViewEnv who ρ₁ = projectViewEnv who ρ₂) :
    evalGuard (Player := P) (L := L) R a ρ₁ =
      evalGuard (Player := P) (L := L) R a ρ₂ :=
  evalGuard_eq_of_obsEq hfresh hR (obsEq_of_projectViewEnv_eq hctx hview)

end Vegas
