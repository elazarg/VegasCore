import Vegas.MAID.Compile

/-!
# Structural lemmas for MAIDCompileState

Lemmas about `lookupDeps`, `depsOfVars`, `ctxDeps`, `addNode`, `addVar`, and
`VarsSubCtx` — extracted from `Correctness.lean` so that downstream files
(e.g. `CompileV.lean`) can import lightweight structural facts without pulling
in the full correctness proof.
-/

namespace Vegas

open MAID

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {B : MAIDBackend Player L}

-- ────────────────────────────────────────────────
-- lookupDepsAux helper lemmas (no DecidableEq Player needed)
-- ────────────────────────────────────────────────

section
omit [DecidableEq Player]

theorem lookupDepsAux_append_singleton_eq_of_ne
    (vars : List (MAIDVarEntry Player L))
    (x y : VarId) (τ : BindTy Player L) (deps : Finset Nat)
    (hxy : y ≠ x) :
    MAIDCompileState.lookupDepsAux (vars ++ [(x, τ, deps)]) y =
      MAIDCompileState.lookupDepsAux vars y := by
  induction vars with
  | nil =>
    simp [MAIDCompileState.lookupDepsAux, hxy]
  | cons e rest ih =>
    rcases e with ⟨z, σ, deps'⟩
    by_cases hyz : y = z
    · subst hyz
      simp [MAIDCompileState.lookupDepsAux]
    · simp [MAIDCompileState.lookupDepsAux, hyz, ih]

theorem lookupDepsAux_append_singleton_eq_self_of_fresh
    (vars : List (MAIDVarEntry Player L))
    (x : VarId) (τ : BindTy Player L) (deps : Finset Nat)
    (hfresh : x ∉ vars.map Prod.fst) :
    MAIDCompileState.lookupDepsAux (vars ++ [(x, τ, deps)]) x = deps := by
  induction vars with
  | nil =>
    simp [MAIDCompileState.lookupDepsAux]
  | cons e rest ih =>
    rcases e with ⟨y, σ, deps'⟩
    have hxy : x ≠ y := by
      intro h
      apply hfresh
      simp [h]
    have hfresh' : x ∉ rest.map Prod.fst := by
      intro h
      apply hfresh
      simp [h]
    simp [MAIDCompileState.lookupDepsAux, hxy, ih, hfresh']

end

-- ────────────────────────────────────────────────
-- lookupDeps under addVar / addNode
-- ────────────────────────────────────────────────

theorem MAIDCompileState.lookupDeps_addVar_eq_of_ne
    (st : MAIDCompileState Player L B)
    (x : VarId) (τ : BindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId)
    {y : VarId} (hxy : y ≠ x) :
    (st.addVar x τ deps hdeps).lookupDeps y = st.lookupDeps y := by
  unfold MAIDCompileState.lookupDeps
  simpa [MAIDCompileState.addVar] using
    lookupDepsAux_append_singleton_eq_of_ne st.vars x y τ deps hxy

theorem MAIDCompileState.lookupDeps_addVar_eq_self_of_fresh
    (st : MAIDCompileState Player L B)
    (x : VarId) (τ : BindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId)
    (hfresh : x ∉ st.vars.map Prod.fst) :
    (st.addVar x τ deps hdeps).lookupDeps x = deps := by
  unfold MAIDCompileState.lookupDeps
  simpa [MAIDCompileState.addVar] using
    lookupDepsAux_append_singleton_eq_self_of_fresh st.vars x τ deps hfresh

theorem MAIDCompileState.lookupDeps_addNode
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hdeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) :
    (st.addNode nd hdeps).2.lookupDeps x = st.lookupDeps x := by
  simp [MAIDCompileState.lookupDeps, MAIDCompileState.addNode]

-- ────────────────────────────────────────────────
-- depsOfVars under addVar
-- ────────────────────────────────────────────────

theorem MAIDCompileState.depsOfVars_addVar_eq_of_fresh
    (st : MAIDCompileState Player L B)
    (x : VarId) (τ : BindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId)
    (xs : List VarId) (hfresh : x ∉ xs) :
    (st.addVar x τ deps hdeps).depsOfVars xs = st.depsOfVars xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    have hyx : y ≠ x := by intro h; apply hfresh; simp [h]
    have hfresh' : x ∉ ys := by intro h; apply hfresh; simp [h]
    simp [MAIDCompileState.depsOfVars,
      st.lookupDeps_addVar_eq_of_ne x τ deps hdeps hyx, ih hfresh']

theorem MAIDCompileState.depsOfVars_addVar_eq_of_not_mem
    (st : MAIDCompileState Player L B)
    (x : VarId) (τ : BindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId) (ys : List VarId) (hx : x ∉ ys) :
    (st.addVar x τ deps hdeps).depsOfVars ys = st.depsOfVars ys := by
  induction ys with
  | nil => simp [depsOfVars]
  | cons y ys ih =>
    simp only [depsOfVars]
    have hne : y ≠ x := fun heq => hx (heq ▸ .head _)
    rw [st.lookupDeps_addVar_eq_of_ne x τ deps hdeps hne,
      ih (fun hmem => hx (List.mem_cons_of_mem _ hmem))]

-- ────────────────────────────────────────────────
-- ctxDeps under addVar / addNode
-- ────────────────────────────────────────────────

theorem MAIDCompileState.ctxDeps_addVar_cons_eq_of_fresh
    (st : MAIDCompileState Player L B)
    (x : VarId) (τ : BindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId)
    {Γ : VCtx Player L}
    (hfreshΓ : Fresh x Γ)
    (hfreshVars : x ∉ st.vars.map Prod.fst) :
    (st.addVar x τ deps hdeps).ctxDeps ((x, τ) :: Γ) = deps ∪ st.ctxDeps Γ := by
  unfold MAIDCompileState.ctxDeps
  rw [List.map_cons, MAIDCompileState.depsOfVars,
    st.lookupDeps_addVar_eq_self_of_fresh x τ deps hdeps hfreshVars,
    st.depsOfVars_addVar_eq_of_fresh x τ deps hdeps (Γ.map Prod.fst) hfreshΓ]

theorem MAIDCompileState.ctxDeps_addNode_eq
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hdeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (Γ : VCtx Player L) :
    (st.addNode nd hdeps).2.ctxDeps Γ = st.ctxDeps Γ := by
  unfold MAIDCompileState.ctxDeps
  have haux : ∀ xs : List VarId,
      (st.addNode nd hdeps).2.depsOfVars xs = st.depsOfVars xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp [MAIDCompileState.depsOfVars, MAIDCompileState.lookupDeps_addNode, ih]
  exact haux (Γ.map Prod.fst)

-- ────────────────────────────────────────────────
-- lookupDeps / depsOfVars subset lemmas
-- ────────────────────────────────────────────────

theorem MAIDCompileState.lookupDeps_subset_depsOfVars_of_mem
    (st : MAIDCompileState Player L B)
    {xs : List VarId} {x : VarId}
    (hx : x ∈ xs) :
    st.lookupDeps x ⊆ st.depsOfVars xs := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    intro d hd
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp [MAIDCompileState.depsOfVars, hd]
    · have hd' : d ∈ st.depsOfVars ys := ih hx hd
      simp [MAIDCompileState.depsOfVars, hd']

theorem MAIDCompileState.lookupDeps_subset_ctxDeps_of_mem
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L} {x : VarId}
    (hx : x ∈ Γ.map Prod.fst) :
    st.lookupDeps x ⊆ st.ctxDeps Γ := by
  simpa [MAIDCompileState.ctxDeps] using
    st.lookupDeps_subset_depsOfVars_of_mem hx

theorem MAIDCompileState.lookupDeps_subset_ctxDeps_of_hasVar
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L}
    (hx : VHasVar (L := L) Γ x τ) :
    st.lookupDeps x ⊆ st.ctxDeps Γ :=
  st.lookupDeps_subset_ctxDeps_of_mem hx.mem_map_fst

theorem MAIDCompileState.depsOfVars_subset_of_subset
    (st : MAIDCompileState Player L B)
    (as bs : List VarId)
    (h : ∀ x, x ∈ as → x ∈ bs) :
    st.depsOfVars as ⊆ st.depsOfVars bs := by
  induction as with
  | nil =>
      exact Finset.empty_subset _
  | cons a as' ih =>
      change st.lookupDeps a ∪ st.depsOfVars as' ⊆ st.depsOfVars bs
      apply Finset.union_subset
      · exact st.lookupDeps_subset_depsOfVars_of_mem (h a (by simp))
      · exact ih (fun z hz => h z (by simp [hz]))

-- ────────────────────────────────────────────────
-- viewDeps / pubCtxDeps subset lemmas
-- ────────────────────────────────────────────────

theorem MAIDCompileState.viewDeps_sub_ctxDeps
    (st : MAIDCompileState Player L B) (who : Player) (Γ : VCtx Player L) :
    st.viewDeps who Γ ⊆ st.ctxDeps Γ := by
  unfold MAIDCompileState.viewDeps MAIDCompileState.ctxDeps
  exact st.depsOfVars_subset_of_subset _ _ (fun x hx => viewVCtx_map_fst_sub hx)

omit [DecidableEq Player] in
private theorem erasePubVCtx_map_fst_sub (Γ : VCtx Player L) :
    ∀ x, x ∈ (erasePubVCtx Γ).map Prod.fst → x ∈ Γ.map Prod.fst := by
  induction Γ with
  | nil => simp [erasePubVCtx]
  | cons a Γ' ih =>
    intro x hx
    match a with
    | (y, .pub b) =>
      simp only [erasePubVCtx_cons_pub, List.map_cons, List.mem_cons] at hx ⊢
      exact hx.elim .inl (fun h => .inr (ih x h))
    | (y, .hidden p b) =>
      simp only [erasePubVCtx_cons_hidden, List.map_cons, List.mem_cons] at hx ⊢
      exact .inr (ih x hx)

theorem MAIDCompileState.pubCtxDeps_sub_ctxDeps
    (st : MAIDCompileState Player L B) (Γ : VCtx Player L) :
    st.pubCtxDeps Γ ⊆ st.ctxDeps Γ := by
  unfold MAIDCompileState.pubCtxDeps MAIDCompileState.ctxDeps
  exact st.depsOfVars_subset_of_subset _ _ (erasePubVCtx_map_fst_sub Γ)

-- ────────────────────────────────────────────────
-- Compound ctxDeps step lemmas
-- ────────────────────────────────────────────────

theorem MAIDCompileState.ctxDeps_letExpr_step
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L} (x : VarId) {b : L.Ty}
    (hfreshΓ : Fresh x Γ)
    (hfreshVars : x ∉ st.vars.map Prod.fst) :
    (st.addVar x (.pub b) (st.pubCtxDeps Γ) (st.depsOfVars_lt _)).ctxDeps
      ((x, .pub b) :: Γ) = st.ctxDeps Γ := by
  rw [st.ctxDeps_addVar_cons_eq_of_fresh x (.pub b) (st.pubCtxDeps Γ)
    (st.depsOfVars_lt _) hfreshΓ hfreshVars]
  exact Finset.union_eq_right.mpr (st.pubCtxDeps_sub_ctxDeps Γ)

theorem MAIDCompileState.ctxDeps_addNode_addVar_singleton_cons_eq_of_fresh
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    {Γ : VCtx Player L}
    (x : VarId) (τ : BindTy Player L)
    (hfreshΓ : Fresh x Γ)
    (hfreshVars : x ∉ st.vars.map Prod.fst) :
    (((st.addNode nd hndeps).2).addVar x τ {st.nextId}
      (by
        intro d hd
        simp_all only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right, not_exists,
          Finset.mem_singleton]
        exact Nat.lt_add_one st.nextId)).ctxDeps ((x, τ) :: Γ) =
      {st.nextId} ∪ st.ctxDeps Γ := by
  have hfreshVars' : x ∉ ((st.addNode nd hndeps).2).vars.map Prod.fst := by
    simpa [MAIDCompileState.addNode] using hfreshVars
  rw [((st.addNode nd hndeps).2).ctxDeps_addVar_cons_eq_of_fresh x τ {st.nextId}
    (by
      intro d hd
      simp_all only [List.mem_map, Prod.exists, exists_and_right, exists_eq_right, not_exists,
        Finset.mem_singleton]
      exact Nat.lt_add_one st.nextId) hfreshΓ hfreshVars']
  rw [MAIDCompileState.ctxDeps_addNode_eq]

theorem MAIDCompileState.ctxDeps_reveal_step
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L}
    (y : VarId) (who : Player) (x : VarId) {b : L.Ty}
    (hx : VHasVar (L := L) Γ x (.hidden who b))
    (hfreshΓ : Fresh y Γ)
    (hfreshVars : y ∉ st.vars.map Prod.fst) :
    (st.addVar y (.pub b) (st.lookupDeps x) (st.lookupDeps_lt x)).ctxDeps
      ((y, .pub b) :: Γ) = st.ctxDeps Γ := by
  rw [st.ctxDeps_addVar_cons_eq_of_fresh y (.pub b) (st.lookupDeps x)
    (st.lookupDeps_lt x) hfreshΓ hfreshVars]
  apply Finset.union_eq_right.mpr
  exact st.lookupDeps_subset_ctxDeps_of_hasVar hx

-- ────────────────────────────────────────────────
-- VarsSubCtx definition and lemmas
-- ────────────────────────────────────────────────

def MAIDCompileState.VarsSubCtx
    (st : MAIDCompileState Player L B) (Γ : VCtx Player L) : Prop :=
  ∀ x, x ∈ st.vars.map Prod.fst → x ∈ Γ.map Prod.fst

theorem MAIDCompileState.VarsSubCtx_addNode
    (st : MAIDCompileState Player L B) {Γ : VCtx Player L}
    (hvars : st.VarsSubCtx Γ) (nd : CompiledNode Player L B)
    (hdeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId) :
    (st.addNode nd hdeps).2.VarsSubCtx Γ := by
  intro x
  simpa [VarsSubCtx, addNode] using hvars x

theorem MAIDCompileState.VarsSubCtx_addVar
    (st : MAIDCompileState Player L B) {Γ : VCtx Player L}
    (hvars : st.VarsSubCtx Γ) (x : VarId) (τ : BindTy Player L)
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId)
    (hfresh : Fresh x Γ) :
    (st.addVar x τ deps hdeps).VarsSubCtx ((x, τ) :: Γ) := by
  intro y hy
  have hy' : y ∈ st.vars.map Prod.fst ∨ y = x := by
    simpa [addVar, List.map_append] using hy
  simp only [List.map_cons, List.mem_cons, List.mem_map, Prod.exists, exists_and_right,
    exists_eq_right]
  rcases hy' with hy' | rfl
  · exact Or.inr (by simpa [List.mem_map] using hvars y hy')
  · exact Or.inl rfl

theorem MAIDCompileState.VarsSubCtx_letExpr_step
    (st : MAIDCompileState Player L B)
    {Γ : VCtx Player L}
    (hvars : st.VarsSubCtx Γ)
    (x : VarId) {b : L.Ty}
    (hfreshΓ : Fresh x Γ) :
    (st.addVar x (.pub b) (st.pubCtxDeps Γ) (st.depsOfVars_lt _)).VarsSubCtx
      ((x, .pub b) :: Γ) := by
  exact st.VarsSubCtx_addVar hvars x (.pub b) (st.pubCtxDeps Γ)
    (st.depsOfVars_lt _) hfreshΓ

theorem MAIDCompileState.VarsSubCtx_addNode_addVar_singleton_step
    (st : MAIDCompileState Player L B) {Γ : VCtx Player L}
    (hvars : st.VarsSubCtx Γ) (nd : CompiledNode Player L B)
    (hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (x : VarId) (τ : BindTy Player L) (hfreshΓ : Fresh x Γ) :
    (((st.addNode nd hndeps).2).addVar x τ {st.nextId}
      (by
        intro d hd
        simp_all only [Finset.mem_singleton]
        exact Nat.lt_add_one st.nextId)).VarsSubCtx ((x, τ) :: Γ) := by
  exact ((st.addNode nd hndeps).2).VarsSubCtx_addVar
    (st.VarsSubCtx_addNode hvars nd hndeps) x τ _ _ hfreshΓ

end Vegas
