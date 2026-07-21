/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.ExprSimple

/-!
# Vegas well-formedness and side conditions

Static predicates on Vegas protocols: SSA-style freshness, reveal completeness,
legality, admissibility, and normalization obligations.
-/

namespace Vegas

def Fresh {P : Type} {L : Vegas.IExpr}
    (x : VarId) (Γ : Vegas.VCtx P L) : Prop :=
  x ∉ Γ.map Prod.fst

def WFCtx {P : Type} {L : Vegas.IExpr}
    (Γ : Vegas.VCtx P L) : Prop :=
  (Γ.map Prod.fst).Nodup

instance {P : Type} {L : Vegas.IExpr} {x : VarId}
    {Γ : Vegas.VCtx P L} : Decidable (Fresh x Γ) :=
  inferInstanceAs (Decidable (x ∉ _))

def FreshBindings {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
:
    {Γ : Vegas.VCtx P L} → Vegas.VegasCore P L Γ → Prop
  | _, .ret _ => True
  | Γ, .sample x _ k => Fresh x Γ ∧ FreshBindings k
  | Γ, .commit x _ _ k => Fresh x Γ ∧ FreshBindings k
  | Γ, .reveal y _ _ _ k => Fresh y Γ ∧ FreshBindings k

def decidableFreshBindings {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
:
    {Γ : Vegas.VCtx P L} → (p : Vegas.VegasCore P L Γ) → Decidable (FreshBindings p)
  | _, .ret _ => .isTrue trivial
  | _, .sample _ _ k => @instDecidableAnd _ _ (inferInstance) (decidableFreshBindings k)
  | _, .commit _ _ _ k => @instDecidableAnd _ _ (inferInstance) (decidableFreshBindings k)
  | _, .reveal _ _ _ _ k => @instDecidableAnd _ _ (inferInstance) (decidableFreshBindings k)

instance {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
    {Γ : Vegas.VCtx P L} {p : Vegas.VegasCore P L Γ} :
    Decidable (FreshBindings p) := decidableFreshBindings p

/-- Every committed secret is revealed exactly once. `pending` tracks
    commit variables awaiting revelation. -/
def RevealComplete {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
:
    {Γ : Vegas.VCtx P L} → List VarId → Vegas.VegasCore P L Γ → Prop
  | _, pending, .ret _ => pending = []
  | _, pending, .sample _ _ k => RevealComplete pending k
  | _, pending, .commit x _ _ k => RevealComplete (x :: pending) k
  | _, pending, .reveal _ _ x _ k =>
    x ∈ pending ∧ RevealComplete (pending.filter (· ≠ x)) k

/-- Source variables introduced by commit sites. -/
def CommittedVars {P : Type} [DecidableEq P]
    {L : Vegas.IExpr} :
    {Γ : Vegas.VCtx P L} → Vegas.VegasCore P L Γ → List VarId
  | _, .ret _ => []
  | _, .sample _ _ k => CommittedVars k
  | _, .commit x _ _ k => x :: CommittedVars k
  | _, .reveal _ _ _ _ k => CommittedVars k

/-- Source variables opened by reveal sites. -/
def RevealedSources {P : Type} [DecidableEq P]
    {L : Vegas.IExpr} :
    {Γ : Vegas.VCtx P L} → Vegas.VegasCore P L Γ → List VarId
  | _, .ret _ => []
  | _, .sample _ _ k => RevealedSources k
  | _, .commit _ _ _ k => RevealedSources k
  | _, .reveal _ _ x _ k => x :: RevealedSources k

/-- Reveal completeness means every pending or later committed source variable
is opened by some later reveal site. -/
theorem RevealComplete.pending_or_committed_revealed
    {P : Type} [DecidableEq P] {L : Vegas.IExpr} :
    {Γ : Vegas.VCtx P L} → {pending : List VarId} →
      (p : Vegas.VegasCore P L Γ) →
      RevealComplete pending p →
      ∀ x, x ∈ pending ++ CommittedVars p → x ∈ RevealedSources p
  | _, pending, .ret _payoffs, hcomplete, x, hx => by
      have hxPending : x ∈ pending := by
        simpa only [CommittedVars, List.append_nil] using hx
      rw [hcomplete] at hxPending
      simp at hxPending
  | _, pending, .sample _ _ tail, hcomplete, x, hx => by
      exact
        RevealComplete.pending_or_committed_revealed
          tail hcomplete x (by simpa [CommittedVars] using hx)
  | _, pending, .commit name _ _ tail, hcomplete, x, hx => by
      have hxShape :
          x ∈ pending ∨ x = name ∨ x ∈ CommittedVars tail := by
        simpa only [CommittedVars, List.mem_append, List.mem_cons] using hx
      have hx' :
          x = name ∨ x ∈ pending ∨ x ∈ CommittedVars tail := by
        rcases hxShape with hpending | hname | hcommitted
        · exact Or.inr (Or.inl hpending)
        · exact Or.inl hname
        · exact Or.inr (Or.inr hcommitted)
      exact
        RevealComplete.pending_or_committed_revealed
          tail hcomplete x
          (by simpa [CommittedVars, List.mem_append] using hx')
  | _, pending, .reveal _ _ source _ tail, hcomplete, x, hx => by
      rcases hcomplete with ⟨_hsource, htail⟩
      by_cases hxs : x = source
      · simp [RevealedSources, hxs]
      · right
        apply
          RevealComplete.pending_or_committed_revealed
            tail htail x
        simpa [CommittedVars, List.mem_append, hxs] using hx

/-- Top-level reveal completeness: every committed source variable is opened
by a reveal site somewhere later in the source program. -/
theorem RevealComplete.committed_revealed
    {P : Type} [DecidableEq P] {L : Vegas.IExpr}
    {Γ : Vegas.VCtx P L} {p : Vegas.VegasCore P L Γ}
    (hcomplete : RevealComplete [] p) :
    ∀ x, x ∈ CommittedVars p → x ∈ RevealedSources p := by
  intro x hx
  exact
    RevealComplete.pending_or_committed_revealed
      p hcomplete x (by simpa using hx)

instance : DecidableEq VarId := inferInstanceAs (DecidableEq Nat)

def decidableRevealComplete {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
:
    {Γ : Vegas.VCtx P L} →
    (pending : List VarId) → (p : Vegas.VegasCore P L Γ) →
    Decidable (RevealComplete pending p)
  | _, _, .ret _ => inferInstanceAs (Decidable (_ = []))
  | _, pending, .sample _ _ k => decidableRevealComplete pending k
  | _, pending, .commit x _ _ k => decidableRevealComplete (x :: pending) k
  | _, pending, .reveal _ _ x _ k =>
    @instDecidableAnd _ _ (inferInstance) (decidableRevealComplete (pending.filter (· ≠ x)) k)

instance {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
    {pending : List VarId} {Γ : Vegas.VCtx P L} {p : Vegas.VegasCore P L Γ} :
    Decidable (RevealComplete pending p) := decidableRevealComplete pending p

@[simp] theorem WFCtx_nil {P : Type} {L : IExpr} :
    WFCtx (L := L) (P := P) [] := List.nodup_nil

theorem WFCtx.cons {P : Type} {L : IExpr}
    {x : VarId} {τ : BindTy P L} {Γ : VCtx P L}
    (hfresh : Fresh x Γ) (hwf : WFCtx Γ) :
    WFCtx ((x, τ) :: Γ) := by
  change (((x, τ) :: Γ).map Prod.fst).Nodup
  exact List.Nodup.cons hfresh hwf

theorem WFCtx.tail {P : Type} {L : IExpr}
    {x : VarId} {τ : BindTy P L} {Γ : VCtx P L} :
    WFCtx ((x, τ) :: Γ) → WFCtx Γ := by
  intro h; exact (List.nodup_cons.mp h).2

theorem WFCtx.fresh_head {P : Type} {L : IExpr}
    {x : VarId} {τ : BindTy P L} {Γ : VCtx P L} :
    WFCtx ((x, τ) :: Γ) → Fresh x Γ := by
  intro h; exact (List.nodup_cons.mp h).1

theorem Fresh_viewVCtx {P : Type} [DecidableEq P] {L : IExpr}
    {x : VarId} {p : P} {Γ : VCtx P L}
    (hfresh : Fresh x Γ) : Fresh x (viewVCtx p Γ) :=
  fun hmem => hfresh (viewVCtx_map_fst_sub hmem)

theorem WFCtx.viewVCtx {P : Type} [DecidableEq P] {L : IExpr}
    {p : P} {Γ : VCtx P L}
    (hctx : WFCtx Γ) : WFCtx (viewVCtx p Γ) := by
  induction Γ generalizing p with
  | nil => exact WFCtx_nil
  | cons hd tl ih =>
      obtain ⟨x, τ⟩ := hd
      have hfresh : Fresh x tl := WFCtx.fresh_head hctx
      have htail : WFCtx tl := WFCtx.tail hctx
      cases hsee : canSee p τ with
      | false =>
          change WFCtx (if canSee p τ then (x, τ) :: Vegas.viewVCtx p tl else Vegas.viewVCtx p tl)
          rw [hsee]
          exact ih (p := p) htail
      | true =>
          change WFCtx (if canSee p τ then (x, τ) :: Vegas.viewVCtx p tl else Vegas.viewVCtx p tl)
          rw [hsee]
          exact WFCtx.cons (Fresh_viewVCtx (p := p) hfresh) (ih (p := p) htail)

theorem pubVCtx_map_fst_sub {P : Type} {L : IExpr}
    {Γ : VCtx P L} {x : VarId} :
    x ∈ (pubVCtx Γ).map Prod.fst → x ∈ Γ.map Prod.fst := by
  induction Γ with
  | nil =>
      intro hx
      simp [pubVCtx] at hx
  | cons hd tl ih =>
      intro hx
      obtain ⟨y, τ⟩ := hd
      obtain ⟨base, visibility⟩ := τ
      cases visibility with
      | pub =>
          change x ∈ y :: (pubVCtx tl).map Prod.fst at hx
          change x ∈ y :: tl.map Prod.fst
          simp only [List.mem_cons] at hx ⊢
          exact hx.imp id ih
      | sealed owner =>
          change x ∈ (pubVCtx tl).map Prod.fst at hx
          change x ∈ y :: tl.map Prod.fst
          simp only [List.mem_cons]
          exact Or.inr (ih hx)

theorem Fresh_pubVCtx {P : Type} {L : IExpr}
    {x : VarId} {Γ : VCtx P L}
    (hfresh : Fresh x Γ) : Fresh x (pubVCtx Γ) :=
  fun hmem => hfresh (pubVCtx_map_fst_sub hmem)

theorem WFCtx.pubSubctx {P : Type} {L : IExpr}
    {Γ : VCtx P L}
    (hctx : WFCtx Γ) : WFCtx (pubVCtx Γ) := by
  induction Γ with
  | nil => exact WFCtx_nil
  | cons hd tl ih =>
      obtain ⟨x, τ⟩ := hd
      obtain ⟨base, visibility⟩ := τ
      have hfresh : Fresh x tl := WFCtx.fresh_head hctx
      have htail : WFCtx tl := WFCtx.tail hctx
      cases visibility with
      | pub =>
          change WFCtx ((x, ⟨base, .pub⟩) :: Vegas.pubVCtx tl)
          exact WFCtx.cons (Fresh_pubVCtx hfresh) (ih htail)
      | sealed owner =>
          change WFCtx (Vegas.pubVCtx tl)
          exact ih htail

theorem WFCtx.eraseVCtx {P : Type} {L : IExpr}
    {Γ : VCtx P L}
    (hctx : WFCtx Γ) : ((eraseVCtx Γ).map Prod.fst).Nodup := by
  rw [eraseVCtx_map_fst]
  exact hctx

theorem WFCtx.erasePubVCtx {P : Type} {L : IExpr}
    {Γ : VCtx P L}
    (hctx : WFCtx Γ) : ((erasePubVCtx Γ).map Prod.fst).Nodup := by
  rw [← eraseVCtx_pubVCtx, eraseVCtx_map_fst]
  exact WFCtx.pubSubctx hctx

def Legal {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
:
    {Γ : Vegas.VCtx P L} → Vegas.VegasCore P L Γ → Prop
  | _, .ret _ => True
  | _, .sample _ _ k => Legal k
  | Γ, .commit _ who (b := b) R k =>
    (∀ env : Env L.Val (Vegas.eraseVCtx (viewVCtx who Γ)),
        ∃ a : L.Val b, Vegas.evalGuard (Player := P) (L := L) R a env = true) ∧
    Legal k
  | _, .reveal _ _ _ _ k => Legal k

namespace DistExpr

abbrev Normalized {Γ : VCtxSimple} {b : BaseTy}
    (D : DistExpr (erasePubVCtx Γ) b) : Prop :=
  ∀ depEnv : (x : VarId) → (τ : BaseTy) →
      HasVar (erasePubVCtx Γ) x τ → x ∈ distExprDeps D → Val τ,
    FWeight.totalWeight (evalDistExprDeps D depEnv) = 1

end DistExpr

def NormalizedDists {P : Type} [DecidableEq P]
    {L : Vegas.IExpr}
:
    {Γ : Vegas.VCtx P L} → Vegas.VegasCore P L Γ → Prop
  | _, .ret _ => True
  | Γ, .sample _ D' k =>
    (∀ depEnv : (x : VarId) → (τ : L.Ty) →
        HasVar (Vegas.erasePubVCtx Γ) x τ →
          x ∈ L.distDeps D' → L.Val τ,
      FWeight.totalWeight (L.evalDistDeps D' depEnv) = 1) ∧
    NormalizedDists k
  | _, .commit _ _ _ k => NormalizedDists k
  | _, .reveal _ _ _ _ k => NormalizedDists k

theorem DistExpr.Normalized_ite {Γ : CtxSimple} {b : BaseTy}
    {c : Expr Γ .bool} {t f : DistExpr Γ b}
    (ht : ∀ depEnv : (x : VarId) → (τ : BaseTy) → HasVar Γ x τ →
        x ∈ distExprDeps t → Val τ,
      FWeight.totalWeight (evalDistExprDeps t depEnv) = 1)
    (hf : ∀ depEnv : (x : VarId) → (τ : BaseTy) → HasVar Γ x τ →
        x ∈ distExprDeps f → Val τ,
      FWeight.totalWeight (evalDistExprDeps f depEnv) = 1) :
    ∀ depEnv : (x : VarId) → (τ : BaseTy) → HasVar Γ x τ →
        x ∈ distExprDeps (.ite c t f) → Val τ,
      FWeight.totalWeight (evalDistExprDeps (.ite c t f) depEnv) = 1 := by
  intro depEnv
  by_cases hc :
      evalExprDeps c
        (fun x τ h hx => depEnv x τ h (by simp [distExprDeps, hx]))
  · simp only [evalDistExprDeps, hc]
    exact ht (fun x τ h hx => depEnv x τ h (by simp [distExprDeps, hx]))
  · simp only [evalDistExprDeps, hc]
    exact hf (fun x τ h hx => depEnv x τ h (by simp [distExprDeps, hx]))

end Vegas
