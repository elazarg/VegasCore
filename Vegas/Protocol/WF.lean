import Vegas.Protocol.Syntax

/-!
# Protocol well-formedness and side conditions

Static predicates on Vegas protocols: SSA-style freshness, reveal completeness,
legality, admissibility, and normalization obligations.
-/

def Fresh {P : Type} {L : Vegas.ExprLanguage}
    (x : VarId) (Γ : Vegas.VisCtx P L) : Prop :=
  x ∉ Γ.map Prod.fst

def WFCtx {P : Type} {L : Vegas.ExprLanguage}
    (Γ : Vegas.VisCtx P L) : Prop :=
  (Γ.map Prod.fst).Nodup

instance {P : Type} {L : Vegas.ExprLanguage} {x : VarId}
    {Γ : Vegas.VisCtx P L} : Decidable (Fresh (P := P) (L := L) x Γ) :=
  inferInstanceAs (Decidable (x ∉ _))

def WF {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.VisExprKit P L]
    [D : Vegas.VisDistKit P L]
    [U : Vegas.VisPayoffKit P L] :
    {Γ : Vegas.VisCtx P L} → Vegas.Prog P L Γ → Prop
  | _, .ret _ => True
  | Γ, .letExpr x _ k => Fresh x Γ ∧ WF k
  | Γ, .sample x _ _ _ k => Fresh x Γ ∧ WF k
  | Γ, .commit x _ _ _ k => Fresh x Γ ∧ WF k
  | Γ, .reveal y _ _ _ k => Fresh y Γ ∧ WF k

def decidableWF {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.VisExprKit P L]
    [D : Vegas.VisDistKit P L]
    [U : Vegas.VisPayoffKit P L] :
    {Γ : Vegas.VisCtx P L} → (p : Vegas.Prog P L Γ) → Decidable (WF p)
  | _, .ret _ => .isTrue trivial
  | _, .letExpr _ _ k => @instDecidableAnd _ _ (inferInstance) (decidableWF k)
  | _, .sample _ _ _ _ k => @instDecidableAnd _ _ (inferInstance) (decidableWF k)
  | _, .commit _ _ _ _ k => @instDecidableAnd _ _ (inferInstance) (decidableWF k)
  | _, .reveal _ _ _ _ k => @instDecidableAnd _ _ (inferInstance) (decidableWF k)

instance {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.VisExprKit P L]
    [D : Vegas.VisDistKit P L]
    [U : Vegas.VisPayoffKit P L]
    {Γ : Vegas.VisCtx P L} {p : Vegas.Prog P L Γ} :
    Decidable (WF p) := decidableWF p

/-- Every committed secret is revealed exactly once. `pending` tracks
    commit variables awaiting revelation. -/
def RevealComplete {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.VisExprKit P L]
    [D : Vegas.VisDistKit P L]
    [U : Vegas.VisPayoffKit P L] :
    {Γ : Vegas.VisCtx P L} → List VarId → Vegas.Prog P L Γ → Prop
  | _, pending, .ret _ => pending = []
  | _, pending, .letExpr _ _ k => RevealComplete pending k
  | _, pending, .sample _ _ _ _ k => RevealComplete pending k
  | _, pending, .commit x _ _ _ k => RevealComplete (x :: pending) k
  | _, pending, .reveal _ _ x _ k =>
    x ∈ pending ∧ RevealComplete (pending.filter (· ≠ x)) k

instance : DecidableEq VarId := inferInstanceAs (DecidableEq Nat)

def decidableRevealComplete {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.VisExprKit P L]
    [D : Vegas.VisDistKit P L]
    [U : Vegas.VisPayoffKit P L] :
    {Γ : Vegas.VisCtx P L} →
    (pending : List VarId) → (p : Vegas.Prog P L Γ) →
    Decidable (RevealComplete pending p)
  | _, _, .ret _ => inferInstanceAs (Decidable (_ = []))
  | _, pending, .letExpr _ _ k => decidableRevealComplete pending k
  | _, pending, .sample _ _ _ _ k => decidableRevealComplete pending k
  | _, pending, .commit x _ _ _ k => decidableRevealComplete (x :: pending) k
  | _, pending, .reveal _ _ x _ k =>
    @instDecidableAnd _ _ (inferInstance) (decidableRevealComplete (pending.filter (· ≠ x)) k)

instance {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.VisExprKit P L]
    [D : Vegas.VisDistKit P L]
    [U : Vegas.VisPayoffKit P L]
    {pending : List VarId} {Γ : Vegas.VisCtx P L} {p : Vegas.Prog P L Γ} :
    Decidable (RevealComplete pending p) := decidableRevealComplete pending p

/-- Full well-formedness: SSA freshness AND every committed secret is revealed. -/
def WFProg {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.VisExprKit P L]
    [D : Vegas.VisDistKit P L]
    [U : Vegas.VisPayoffKit P L]
    {Γ : Vegas.VisCtx P L}
    (p : Vegas.Prog P L Γ) : Prop :=
  WF p ∧ RevealComplete [] p

-- § 11a. Context lemmas

@[simp] theorem WFCtx_nil : WFCtx (P := Player) (L := exprLanguage) [] := List.nodup_nil

theorem WFCtx.cons {x : VarId} {τ : BindTy} {Γ : Ctx}
    (hfresh : Fresh x Γ) (hwf : WFCtx Γ) :
    WFCtx ((x, τ) :: Γ) := by
  change (((x, τ) :: Γ).map Prod.fst).Nodup
  exact List.Nodup.cons hfresh hwf

theorem WFCtx.tail {x : VarId} {τ : BindTy} {Γ : Ctx} :
    WFCtx ((x, τ) :: Γ) → WFCtx Γ := by
  intro h; exact (List.nodup_cons.mp h).2

theorem WFCtx.fresh_head {x : VarId} {τ : BindTy} {Γ : Ctx} :
    WFCtx ((x, τ) :: Γ) → Fresh x Γ := by
  intro h; exact (List.nodup_cons.mp h).1

theorem HasVar.mem_map_fst {Γ : Ctx} {x : VarId} {τ : BindTy} :
    HasVar Γ x τ → x ∈ Γ.map Prod.fst := by
  intro h; induction h with
  | here => simp
  | there _ ih => exact List.mem_cons_of_mem _ ih

theorem HasVar.unique {Γ : Ctx} {x : VarId} {τ₁ τ₂ : BindTy}
    (hwf : WFCtx Γ) (h1 : HasVar Γ x τ₁) (h2 : HasVar Γ x τ₂) :
    τ₁ = τ₂ := by
  induction h1 with
  | here =>
    match h2 with
    | .here => rfl
    | .there h2' => exact absurd (HasVar.mem_map_fst h2') hwf.fresh_head
  | there h1' ih =>
    match h2 with
    | .here => exact absurd (HasVar.mem_map_fst h1') hwf.fresh_head
    | .there h2' => exact ih hwf.tail h2'

-- § 11b. Fresh lemmas for subcontexts

theorem viewCtx_map_fst_sub {x : VarId} {p : Player} {Γ : Ctx} :
    x ∈ (viewCtx p Γ).map Prod.fst → x ∈ Γ.map Prod.fst := by
  induction Γ with
  | nil =>
    intro h
    have : False := by
      simp [Vegas.viewCtx] at h
    exact False.elim this
  | cons hd tl ih =>
    obtain ⟨y, τ⟩ := hd
    cases hsee : Vegas.canSee (Player := Player) (L := exprLanguage) p τ with
    | false =>
      intro h
      have hview : viewCtx p ((y, τ) :: tl) = viewCtx p tl := by
        simp [viewCtx, Vegas.viewCtx, hsee]
      rw [hview] at h
      exact List.mem_cons_of_mem _ (ih h)
    | true =>
      intro h
      have hview : viewCtx p ((y, τ) :: tl) = (y, τ) :: viewCtx p tl := by
        simp [viewCtx, Vegas.viewCtx, hsee]
      rw [hview] at h
      simp only [List.map, List.mem_cons] at h ⊢
      rcases h with rfl | htl
      · exact Or.inl rfl
      · exact Or.inr (ih htl)

theorem Fresh_viewCtx {x : VarId} {p : Player} {Γ : Ctx}
    (hfresh : Fresh x Γ) : Fresh x (viewCtx p Γ) :=
  fun hmem => hfresh (viewCtx_map_fst_sub hmem)

theorem Fresh_flattenCtx {x : VarId} {Γ : Ctx}
    (hfresh : Fresh x Γ) : Fresh x (flattenCtx Γ) := by
  unfold Fresh at *; rwa [flattenCtx_map_fst]

theorem WFCtx_flattenCtx {Γ : Ctx}
    (hwf : WFCtx Γ) : WFCtx (flattenCtx Γ) := by
  unfold WFCtx at *; rwa [flattenCtx_map_fst]

-- ============================================================================
-- § 12. Legality and admissibility
-- ============================================================================

def Legal {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.VisExprKit P L]
    [D : Vegas.VisDistKit P L]
    [U : Vegas.VisPayoffKit P L] :
    {Γ : Vegas.VisCtx P L} → Vegas.Prog P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => Legal k
  | _, .sample _ _ _ _ k => Legal k
  | Γ, .commit _ who acts R k =>
    (∀ view : Vegas.VisEnv (Player := P) L (Vegas.viewCtx who Γ),
        ∃ a ∈ acts, Vegas.evalGuard (Player := P) (L := L) E R a view = true) ∧ Legal k
  | _, .reveal _ _ _ _ k => Legal k

def DistinctActs {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.VisExprKit P L]
    [D : Vegas.VisDistKit P L]
    [U : Vegas.VisPayoffKit P L] :
    {Γ : Vegas.VisCtx P L} → Vegas.Prog P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => DistinctActs k
  | _, .sample _ _ _ _ k => DistinctActs k
  | _, .commit _ _ acts _ k => acts.Nodup ∧ DistinctActs k
  | _, .reveal _ _ _ _ k => DistinctActs k

def AdmissibleProfile {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.VisExprKit P L]
    [D : Vegas.VisDistKit P L]
    [U : Vegas.VisPayoffKit P L]
    (σ : Vegas.Profile P L) :
    {Γ : Vegas.VisCtx P L} → Vegas.Prog P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => AdmissibleProfile σ k
  | _, .sample _ _ _ _ k => AdmissibleProfile σ k
  | _, .commit x who acts R k =>
    (∀ view, FDist.Supported (σ.commit who x acts R view)
      (fun a => a ∈ acts ∧ Vegas.evalGuard (Player := P) (L := L) E R a view = true)) ∧
    AdmissibleProfile σ k
  | _, .reveal _ _ _ _ k => AdmissibleProfile σ k

theorem List.filter_ne_nil_of_exists {l : List α} {p : α → Bool}
    (h : ∃ a ∈ l, p a = true) : l.filter p ≠ [] := by
  obtain ⟨a, ha_mem, ha_p⟩ := h
  exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨ha_mem, ha_p⟩)

-- ============================================================================
-- § 13. Normalization predicates
-- ============================================================================

def DistExprNormalized {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [D : Vegas.VisDistKit P L]
    {Γ : Vegas.VisCtx P L} {b : L.Ty}
    (D' : D.DistExpr Γ b) : Prop :=
  ∀ env : Vegas.VisEnv (Player := P) L Γ, FDist.totalWeight (D.eval D' env) = 1

namespace DistExpr

abbrev Normalized (D : DistExpr Γ b) : Prop :=
  DistExprNormalized (P := Player) (L := exprLanguage) D

end DistExpr

def NormalizedDists {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.VisExprKit P L]
    [D : Vegas.VisDistKit P L]
    [U : Vegas.VisPayoffKit P L] :
    {Γ : Vegas.VisCtx P L} → Vegas.Prog P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => NormalizedDists k
  | _, .sample _ _ _ D' k => DistExprNormalized (P := P) (L := L) D' ∧ NormalizedDists k
  | _, .commit _ _ _ _ k => NormalizedDists k
  | _, .reveal _ _ _ _ k => NormalizedDists k

def Vegas.Profile.NormalizedOn {P : Type} [DecidableEq P]
    {L : Vegas.ExprLanguage}
    [E : Vegas.VisExprKit P L]
    [D : Vegas.VisDistKit P L]
    [U : Vegas.VisPayoffKit P L]
    (σ : Vegas.Profile P L) :
    {Γ : Vegas.VisCtx P L} → Vegas.Prog P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => σ.NormalizedOn k
  | _, .sample _ _ _ _ k => σ.NormalizedOn k
  | _, .commit x who acts R k =>
    (∀ view, FDist.totalWeight (σ.commit who x acts R view) = 1) ∧ σ.NormalizedOn k
  | _, .reveal _ _ _ _ k => σ.NormalizedOn k

theorem DistExpr.Normalized_ite {Γ : Ctx} {b : BaseTy}
    {c : Expr Γ .bool} {t f : DistExpr Γ b}
    (ht : t.Normalized) (hf : f.Normalized) :
    (DistExpr.ite c t f).Normalized := by
  intro env
  change FDist.totalWeight (evalDistExpr (DistExpr.ite c t f) env) = 1
  by_cases hc : evalExpr c env
  · simp only [evalDistExpr, hc]
    exact ht env
  · simp only [evalDistExpr, hc]
    exact hf env

