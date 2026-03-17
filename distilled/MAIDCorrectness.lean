import distilled.MAIDFDistFold
import GameTheory.Languages.MAID.Prefix

namespace Distilled

open MAID

variable {Player : Type} [DecidableEq Player] {L : ExprLanguage}
variable [E : VisExprKit Player L] [D : VisDistKit Player L] [U : VisPayoffKit Player L]
variable {B : MAIDBackend Player L}

-- ============================================================================
-- § 1. RawNodeEnv helpers (proved)
-- ============================================================================

def RawNodeEnv.extend (raw : RawNodeEnv L) (nid : Nat) (tv : TaggedVal L) :
    RawNodeEnv L :=
  fun i => if i = nid then some tv else raw i

omit E D U in
theorem readVal_extend_self (raw : RawNodeEnv L) (nid : Nat) (τ : L.Ty)
    (v : L.Val τ) :
    MAIDCompileState.readVal (B := B) (raw.extend nid ⟨τ, v⟩) τ nid = v := by
  simp [RawNodeEnv.extend, MAIDCompileState.readVal]

omit E D U in
theorem readVal_extend_ne (raw : RawNodeEnv L) (nid nid' : Nat)
    (tv : TaggedVal L) (τ : L.Ty) (hne : nid' ≠ nid) :
    MAIDCompileState.readVal (B := B) (raw.extend nid tv) τ nid' =
    MAIDCompileState.readVal (B := B) raw τ nid' := by
  simp [RawNodeEnv.extend, hne, MAIDCompileState.readVal]

def InsensitiveTo (f : RawNodeEnv L → α) (nid : Nat) : Prop :=
  ∀ raw (tv : TaggedVal L), f (raw.extend nid tv) = f raw

-- ============================================================================
-- § 2. nativeOutcomeDist: direct FDist U.Outcome by induction on Prog
-- ============================================================================

/-- Direct computation of `FDist U.Outcome` by recursion on `Prog`,
threading a plain `RawNodeEnv L` argument. No `FDist (RawNodeEnv L)` appears.

Each `sample`/`commit` does `FDist.bind μ (fun v => recurse with extended raw)`.
The `FDist.bind` is over `FDist (L.Val τ)` → `FDist U.Outcome`, both of which
have computable `DecidableEq`. -/
noncomputable def nativeOutcomeDist
    (B : MAIDBackend Player L)
    (σ : Profile (Player := Player) (L := L)) :
    {Γ : VisCtx Player L} →
    (p : Prog Player L Γ) →
    (ρ : RawNodeEnv L → VisEnv (Player := Player) L Γ) →
    (nextId : Nat) →
    RawNodeEnv L → FDist U.Outcome
  | _, .ret u, ρ, _, raw =>
      FDist.pure (U.eval u (ρ raw))
  | _, .letExpr (b := b) x e k, ρ, nextId, raw =>
      nativeOutcomeDist B σ k
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := .pub b)
          (E.eval e (ρ raw)) (ρ raw))
        nextId raw
  | _, .sample x τ _m D' k, ρ, nextId, raw =>
      FDist.bind
        (D.eval D' (VisEnv.projectDist (Player := Player) (L := L) τ _ (ρ raw)))
        (fun v =>
          nativeOutcomeDist B σ k
            (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := τ)
              (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw))
            (nextId + 1) (raw.extend nextId ⟨τ.base, v⟩))
  | _, .commit (b := b) x who acts R k, ρ, nextId, raw =>
      FDist.bind
        (σ.commit who x acts R (VisEnv.toView (Player := Player) (L := L) who (ρ raw)))
        (fun v =>
          nativeOutcomeDist B σ k
            (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := .hidden who b)
              (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw))
            (nextId + 1) (raw.extend nextId ⟨b, v⟩))
  | _, .reveal (b := b) y _who _x hx k, ρ, nextId, raw =>
      nativeOutcomeDist B σ k
        (fun raw =>
          let v : L.Val b := VisEnv.get (Player := Player) (L := L) (ρ raw) hx
          VisEnv.cons (Player := Player) (L := L) (x := y) (τ := .pub b) v (ρ raw))
        nextId raw

-- ============================================================================
-- § 3. Core theorem: nativeOutcomeDist = outcomeDist
-- ============================================================================

/-- **Core theorem.** `nativeOutcomeDist` equals `outcomeDist` when ρ is
insensitive to all node ids ≥ nextId.

The proof is by structural induction on `Prog`. Each case uses
`readVal_extend_self` + `InsensitiveTo` for the ρ roundtrip. -/
theorem nativeOutcomeDist_eq_outcomeDist
    (B : MAIDBackend Player L)
    {Γ : VisCtx Player L}
    (p : Prog Player L Γ)
    (σ : Profile (Player := Player) (L := L))
    (ρ : RawNodeEnv L → VisEnv (Player := Player) L Γ)
    (nextId : Nat)
    (hρ : ∀ nid, nextId ≤ nid → InsensitiveTo ρ nid) :
    ∀ raw : RawNodeEnv L,
    nativeOutcomeDist B σ p ρ nextId raw = outcomeDist σ p (ρ raw) := by
  induction p generalizing nextId with
  | ret u =>
    intro raw
    simp only [nativeOutcomeDist, outcomeDist]
  | letExpr x e k ih =>
    intro raw
    simp only [nativeOutcomeDist, outcomeDist]
    exact ih _ nextId
      (fun nid hn raw tv => VisEnv.cons_ext (by rw [hρ nid hn raw tv]) (hρ nid hn raw tv))
      raw
  | sample x τ m D' k ih =>
    intro raw
    simp only [nativeOutcomeDist, outcomeDist]
    congr 1; funext v
    have hρ' : ∀ nid', nextId + 1 ≤ nid' → InsensitiveTo
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := τ)
          (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw)) nid' := by
      intro nid' hn' raw tv
      exact VisEnv.cons_ext
        (readVal_extend_ne raw nid' nextId tv τ.base (by omega))
        (hρ nid' (by omega) raw tv)
    rw [ih _ (nextId + 1) hρ']
    congr 1
    exact VisEnv.cons_ext (readVal_extend_self (B := B) raw nextId τ.base v)
      (hρ nextId (le_refl _) raw ⟨τ.base, v⟩)
  | @commit _ x who b acts R k ih =>
    intro raw
    simp only [nativeOutcomeDist, outcomeDist]
    congr 1; funext v
    have hρ' : ∀ nid', nextId + 1 ≤ nid' → InsensitiveTo
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := .hidden who b)
          (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw)) nid' := by
      intro nid' hn' raw tv
      exact VisEnv.cons_ext
        (readVal_extend_ne raw nid' nextId tv b (by omega))
        (hρ nid' (by omega) raw tv)
    rw [ih _ (nextId + 1) hρ']
    congr 1
    exact VisEnv.cons_ext (readVal_extend_self (B := B) raw nextId b v)
      (hρ nextId (le_refl _) raw ⟨b, v⟩)
  | reveal y who x hx k ih =>
    intro raw
    simp only [nativeOutcomeDist, outcomeDist]
    exact ih _ nextId
      (fun nid hn raw tv => VisEnv.cons_ext (by rw [hρ nid hn raw tv]) (hρ nid hn raw tv))
      raw

/-- Corollary: for the initial state (constant ρ), `nativeOutcomeDist` = `outcomeDist`. -/
theorem nativeOutcomeDist_eq_outcomeDist_init
    (B : MAIDBackend Player L)
    {Γ : VisCtx Player L}
    (p : Prog Player L Γ)
    (σ : Profile (Player := Player) (L := L))
    (env : VisEnv (Player := Player) L Γ)
    (raw₀ : RawNodeEnv L) :
    nativeOutcomeDist B σ p (fun _ => env) 0 raw₀ = outcomeDist σ p env := by
  exact nativeOutcomeDist_eq_outcomeDist B p σ (fun _ => env) 0
    (fun _ _ _ _ => rfl) raw₀

-- ============================================================================
-- § 4. Main theorem
-- ============================================================================

theorem compiled_naturalOrder (st : MAIDCompileState Player L B) :
    @Struct.NaturalOrder Player _ B.fintypePlayer st.nextId st.toStruct := by
  let _ : Fintype Player := B.fintypePlayer
  intro nd p hp
  rcases Finset.mem_image.mp hp with ⟨d, hd, rfl⟩
  exact st.descAt_parent_lt nd d.2

-- ============================================================================
-- § 4a. Bridge constructions
-- ============================================================================

/-- Deterministic outcome extraction: given a `RawNodeEnv`, replay the Prog
to reconstruct the final environment and evaluate the utility. -/
noncomputable def extractOutcome
    (B : MAIDBackend Player L) :
    {Γ : VisCtx Player L} →
    Prog Player L Γ →
    (RawNodeEnv L → VisEnv (Player := Player) L Γ) →
    Nat → (RawNodeEnv L → U.Outcome)
  | _, .ret u, ρ, _ => fun raw => U.eval u (ρ raw)
  | _, .letExpr (b := b) x e k, ρ, nextId =>
      extractOutcome B k
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := .pub b)
          (E.eval e (ρ raw)) (ρ raw))
        nextId
  | _, .sample x τ _m _D' k, ρ, nextId =>
      extractOutcome B k
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := τ)
          (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw))
        (nextId + 1)
  | _, .commit (b := b) x who _acts _R k, ρ, nextId =>
      extractOutcome B k
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := .hidden who b)
          (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw))
        (nextId + 1)
  | _, .reveal (b := b) y _who _x hx k, ρ, nextId =>
      extractOutcome B k
        (fun raw =>
          let v : L.Val b := VisEnv.get (Player := Player) (L := L) (ρ raw) hx
          VisEnv.cons (Player := Player) (L := L) (x := y) (τ := .pub b) v (ρ raw))
        nextId

/-- Convert a total MAID assignment to a `RawNodeEnv`. -/
noncomputable def rawOfTAssign (st : MAIDCompileState Player L B)
    (a : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct) : RawNodeEnv L :=
  let _ : Fintype Player := B.fintypePlayer
  fun i =>
  if hi : i < st.nextId then
    MAIDCompileState.taggedOfVal (st.descAt ⟨i, hi⟩) (a ⟨i, hi⟩)
  else
    none

-- ============================================================================
-- § 4b. Compiled policy
-- ============================================================================

/-- Kernel normalization: every decision node in `st`, when its kernel is
applied to `σ`, produces a normalized FDist. -/
def MAIDCompileState.KernelNormalized (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L)) : Prop :=
  ∀ (nd : Fin st.nextId) (raw : RawNodeEnv L)
    (τ : L.Ty) (who : Player) (acts : List (L.Val τ))
    (hacts : acts ≠ []) (hnodup : acts.Nodup) (obs : Finset Nat)
    (kernel : Profile (Player := Player) (L := L) → RawNodeEnv L → FDist (L.Val τ)),
    st.descAt nd = .decision τ who acts hacts hnodup obs kernel →
    FDist.totalWeight (kernel σ raw) = 1

/-- Compile a Vegas `Profile` into a MAID `Policy`. Each decision node's
kernel is evaluated and converted via `toPMF`. -/
noncomputable def compiledPolicy (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (hkn : st.KernelNormalized σ) :
    @MAID.Policy Player _ B.fintypePlayer st.nextId st.toStruct := by
  let _ : Fintype Player := B.fintypePlayer
  intro p ⟨d, cfg⟩
  match hdesc : st.descAt d.1 with
  | .decision τ _who acts hacts hnodup obs kernel =>
      change PMF (MAIDCompileState.CompiledNode.valType (st.descAt d.1))
      rw [hdesc]
      exact FDist.toPMF (kernel σ (st.rawEnvOfCfg cfg))
        (hkn d.1 (st.rawEnvOfCfg cfg) τ _ acts hacts hnodup obs kernel hdesc)
  | .chance τ ps cpd hn =>
      exact absurd d.2 (by simp [MAIDCompileState.toStruct, CompiledNode.kind, hdesc])
  | .utility who ps ufn =>
      exact absurd d.2 (by simp [MAIDCompileState.toStruct, CompiledNode.kind, hdesc])

-- ============================================================================
-- § 4c. Kernel normalization from σ.NormalizedOn
-- ============================================================================

/-- The empty compile state trivially satisfies kernel normalization
(it has no nodes). -/
theorem MAIDCompileState.empty_kernelNormalized
    (σ : Profile (Player := Player) (L := L)) :
    (MAIDCompileState.empty (B := B)).KernelNormalized σ :=
  fun nd => nd.elim0

/-- `addVar` does not change nodes, so kernel normalization is preserved. -/
theorem MAIDCompileState.addVar_kernelNormalized
    (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (x : VarId) (τ : VisBindTy Player L) (deps : Finset Nat)
    (hdeps : ∀ d ∈ deps, d < st.nextId)
    (hst : st.KernelNormalized σ) :
    (st.addVar x τ deps hdeps).KernelNormalized σ :=
  hst  -- addVar preserves nodes and nextId

/-- `descAt` for the new node added by `addNode`. -/
theorem MAIDCompileState.addNode_descAt_new
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hdeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId) :
    (st.addNode nd hdeps).2.descAt ⟨st.nextId, Nat.lt_succ_self _⟩ = nd := by
  simp only [descAt, addNode]
  change ((st.nodes ++ [(st.nextId, nd)])[st.nextId]'(by
    simp [st.nodes_length_eq_nextId])).2 = nd
  rw [List.getElem_append_right (by simp [st.nodes_length_eq_nextId])]
  simp [st.nodes_length_eq_nextId]

/-- `descAt` for old nodes is unchanged by `addNode`. -/
theorem MAIDCompileState.addNode_descAt_old
    (st : MAIDCompileState Player L B)
    (nd : CompiledNode Player L B)
    (hdeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId)
    (i : Fin st.nextId) :
    (st.addNode nd hdeps).2.descAt ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = st.descAt i := by
  simp only [descAt, addNode]
  change ((st.nodes ++ [(st.nextId, nd)])[i.val]'(by
    simp [st.nodes_length_eq_nextId])).2 =
    (st.nodes[i.val]'(st.index_lt_nodes i)).2
  congr 1
  rw [List.getElem_append_left]

/-- `addNode` with a chance node preserves kernel normalization. -/
theorem MAIDCompileState.addNode_chance_kernelNormalized
    (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (τ : L.Ty) (deps : Finset Nat)
    (cpd : RawNodeEnv L → FDist (L.Val τ))
    (hn : ∀ raw, FDist.totalWeight (cpd raw) = 1)
    (hdeps : ∀ d ∈ (CompiledNode.chance τ deps cpd hn).parents ∪
      (CompiledNode.chance τ deps cpd hn).obsParents, d < st.nextId)
    (hst : st.KernelNormalized σ) :
    (st.addNode (.chance τ deps cpd hn) hdeps).2.KernelNormalized σ := by
  intro nd raw τ' who acts hacts hnodup obs kernel hdesc
  by_cases h : nd.val < st.nextId
  · -- Old node
    have heq := st.addNode_descAt_old (.chance τ deps cpd hn) hdeps ⟨nd.val, h⟩
    simp only [Fin.eta] at heq
    rw [heq] at hdesc
    exact hst ⟨nd.val, h⟩ raw τ' who acts hacts hnodup obs kernel hdesc
  · -- New node at st.nextId
    have hlen : (st.addNode (.chance τ deps cpd hn) hdeps).2.nextId = st.nextId + 1 := rfl
    have hnd : nd.val = st.nextId := by omega
    have heq := st.addNode_descAt_new (.chance τ deps cpd hn) hdeps
    have hnd' : nd = ⟨st.nextId, Nat.lt_succ_self _⟩ := Fin.ext hnd
    rw [hnd'] at hdesc
    rw [heq] at hdesc
    -- hdesc says .chance = .decision, contradiction
    cases hdesc

/-- `addNode` with a decision node preserves kernel normalization when the
kernel is normalized. -/
theorem MAIDCompileState.addNode_decision_kernelNormalized
    (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (τ : L.Ty) (who : Player) (acts : List (L.Val τ))
    (hacts : acts ≠ []) (hnodup : acts.Nodup) (obs : Finset Nat)
    (kernel : Profile (Player := Player) (L := L) → RawNodeEnv L → FDist (L.Val τ))
    (hdeps : ∀ d ∈ (CompiledNode.decision τ who acts hacts hnodup obs kernel).parents ∪
      (CompiledNode.decision τ who acts hacts hnodup obs kernel).obsParents, d < st.nextId)
    (hst : st.KernelNormalized σ)
    (hkernel : ∀ raw, FDist.totalWeight (kernel σ raw) = 1) :
    (st.addNode (.decision τ who acts hacts hnodup obs kernel) hdeps).2.KernelNormalized σ := by
  intro nd raw τ' who' acts' hacts' hnodup' obs' kernel' hdesc
  by_cases h : nd.val < st.nextId
  · have heq := st.addNode_descAt_old
        (.decision τ who acts hacts hnodup obs kernel) hdeps ⟨nd.val, h⟩
    simp only [Fin.eta] at heq
    rw [heq] at hdesc
    exact hst ⟨nd.val, h⟩ raw τ' who' acts' hacts' hnodup' obs' kernel' hdesc
  · have hlen : (st.addNode (.decision τ who acts hacts hnodup obs kernel) hdeps).2.nextId =
        st.nextId + 1 := rfl
    have hnd : nd.val = st.nextId := by omega
    have heq := st.addNode_descAt_new (.decision τ who acts hacts hnodup obs kernel) hdeps
    have hnd' : nd = ⟨st.nextId, Nat.lt_succ_self _⟩ := Fin.ext hnd
    rw [hnd'] at hdesc; rw [heq] at hdesc
    cases hdesc
    exact hkernel raw

/-- Utility nodes preserve kernel normalization. -/
theorem MAIDCompileState.addUtilityNodes_kernelNormalized
    (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId)
    (ufn : Player → RawNodeEnv L → ℝ) (players : List Player)
    (hst : st.KernelNormalized σ) :
    (st.addUtilityNodes deps hdeps ufn players).KernelNormalized σ := by
  induction players generalizing st with
  | nil => exact hst
  | cons who rest ih =>
    apply ih
    have hutdeps : ∀ d ∈ (CompiledNode.utility (B := B) who deps
        (ufn who)).parents ∪
        (CompiledNode.utility (B := B) who deps (ufn who)).obsParents,
        d < st.nextId := by
      intro d hd'; have := Finset.mem_union.mp hd'
      rcases this with h | h <;>
        simpa [CompiledNode.parents, CompiledNode.obsParents]
          using hdeps d h
    intro nd raw τ who' acts hacts hnodup obs kernel hdesc
    by_cases h : nd.val < st.nextId
    · have heq := st.addNode_descAt_old
        (.utility who deps (ufn who)) hutdeps ⟨nd.val, h⟩
      simp only [Fin.eta] at heq; rw [heq] at hdesc
      exact hst ⟨nd.val, h⟩ raw τ who' acts hacts hnodup
        obs kernel hdesc
    · have hlen : (st.addNode (.utility who deps (ufn who))
          hutdeps).2.nextId = st.nextId + 1 := rfl
      have hnd : nd.val = st.nextId := by omega
      have heq := st.addNode_descAt_new
        (.utility who deps (ufn who)) hutdeps
      have hnd' : nd = ⟨st.nextId, Nat.lt_succ_self _⟩ :=
        Fin.ext hnd
      rw [hnd'] at hdesc; rw [heq] at hdesc
      cases hdesc

/-- `ofProg` preserves kernel normalization: if `st₀` satisfies kernel
normalization and `σ` is normalized on `p`, then so does `ofProg B p ... st₀`. -/
theorem ofProg_kernelNormalized
    (B : MAIDBackend Player L)
    {Γ : VisCtx Player L}
    (p : Prog Player L Γ)
    (σ : Profile (Player := Player) (L := L))
    (hl : Legal p) (ha : DistinctActs p)
    (hd : _root_.NormalizedDists (P := Player) (L := L) p)
    (hσ_norm : σ.NormalizedOn p)
    (ρ : RawNodeEnv L → VisEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B)
    (hst₀ : st₀.KernelNormalized σ) :
    (MAIDCompileState.ofProg B p hl ha hd ρ st₀).KernelNormalized σ := by
  induction p generalizing st₀ with
  | ret u =>
    exact st₀.addUtilityNodes_kernelNormalized σ _ _ _ _ hst₀
  | letExpr x e k ih =>
    exact ih hl ha hd hσ_norm _ _ (st₀.addVar_kernelNormalized σ _ _ _ _ hst₀)
  | sample x τ m D' k ih =>
    exact ih hl ha hd.2 hσ_norm _ _
      ((st₀.addNode _ _).2.addVar_kernelNormalized σ _ _ _ _
        (st₀.addNode_chance_kernelNormalized σ τ.base _ _ _ _ hst₀))
  | @commit Γ x who b acts R k ih =>
    exact ih hl.2 ha.2 hd hσ_norm.2 _ _
      ((st₀.addNode _ _).2.addVar_kernelNormalized σ _ _ _ _
        (st₀.addNode_decision_kernelNormalized σ b who acts _ ha.1 _ _ _ hst₀
          (fun raw => hσ_norm.1 _)))
  | reveal y who x hx k ih =>
    exact ih hl ha hd hσ_norm _ _ (st₀.addVar_kernelNormalized σ _ _ _ _ hst₀)

-- ============================================================================
-- § 4d. Bridge lemma
-- ============================================================================

-- ============================================================================
-- § 4d-i. Infrastructure for the bridge
-- ============================================================================

/-- `addUtilityNodes` increases `nextId` by the number of players. -/
theorem MAIDCompileState.addUtilityNodes_nextId
    (st : MAIDCompileState Player L B) (deps hdeps ufn)
    (players : List Player) :
    (st.addUtilityNodes deps hdeps ufn players).nextId =
      st.nextId + players.length := by
  induction players generalizing st with
  | nil => simp [addUtilityNodes]
  | cons who rest ih =>
    simp only [addUtilityNodes, List.length_cons]
    rw [ih]; simp [addNode]; omega

/-- `ofProg` only increases `nextId`. -/
theorem MAIDCompileState.ofProg_nextId_le
    (B : MAIDBackend Player L) {Γ : VisCtx Player L}
    (p : Prog Player L Γ) (hl ha hd)
    (ρ : RawNodeEnv L → VisEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B) :
    st₀.nextId ≤ (MAIDCompileState.ofProg B p hl ha hd ρ st₀).nextId := by
  induction p generalizing st₀ with
  | ret u =>
    letI := B.fintypePlayer; simp only [MAIDCompileState.ofProg]
    rw [MAIDCompileState.addUtilityNodes_nextId]; omega
  | letExpr x e k ih =>
    (expose_names;
      exact
        le_of_le_of_eq''
          (ih hl ha hd
            (fun raw ↦
              have env := ρ raw;
              VisEnv.cons (VisExprKit.eval e env) env)
            (st₀.addVar x (VisBindTy.pub b) (st₀.ctxDeps Γ_1) (ofProg._proof_1 B Γ_1 st₀)))
          rfl)
  | sample x τ m D' k ih =>
    change st₀.nextId ≤ (MAIDCompileState.ofProg B k hl ha hd.2 _ _).nextId
    refine le_trans (Nat.le_succ _) ?_
    (expose_names;
      exact
        le_of_le_of_eq''
          (ih hl ha hd.right
            (fun raw ↦
              have env := ρ raw;
              have v := readVal raw τ.base st₀.nextId;
              VisEnv.cons v env)
            ((st₀.addNode
                    (CompiledNode.chance τ.base (st₀.ctxDeps Γ_1)
                      (fun raw ↦
                        have env := ρ raw;
                        VisDistKit.eval D' (VisEnv.projectDist τ m env))
                      (ofProg._proof_2 Γ_1 x τ m D' k hd ρ))
                    (ofProg._proof_3 B Γ_1 x τ m D' k hd ρ st₀)).2.addVar
              x τ {st₀.nextId} (ofProg._proof_5 B Γ_1 x τ m D' k hd ρ st₀)))
          rfl)
  | commit x who acts R k ih =>
    change st₀.nextId ≤ (MAIDCompileState.ofProg B k hl.2 ha.2 hd _ _).nextId
    refine le_trans (Nat.le_succ _) ?_
    (expose_names;
      exact
        le_of_le_of_eq''
          (ih hl.right ha.right hd
            (fun raw ↦
              have env := ρ raw;
              have v := readVal raw _ st₀.nextId;
              VisEnv.cons v env)
            ((st₀.addNode
                    (CompiledNode.decision _ who acts _ _ (st₀.ctxDeps Γ_1) fun σ raw ↦
                      σ.commit who x acts R (VisEnv.toView who (ρ raw)))
                    _).2.addVar
              x _ {st₀.nextId} _))
          rfl)
  | reveal y who x hx k ih =>
    (expose_names;
      exact
        le_of_le_of_eq''
          (ih hl ha hd
            (fun raw ↦
              have env := ρ raw;
              have v := env.get hx;
              VisEnv.cons v env)
            (st₀.addVar y (VisBindTy.pub b) (st₀.lookupDeps x) (lookupDeps_lt st₀ x)))
          rfl)

/-- `nativeOutcomeDist` has total weight 1 when distributions and profile
are normalized. -/
theorem nativeOutcomeDist_totalWeight
    (B : MAIDBackend Player L)
    {Γ : VisCtx Player L}
    (p : Prog Player L Γ)
    (σ : Profile (Player := Player) (L := L))
    (hd : _root_.NormalizedDists (P := Player) (L := L) p)
    (hσ_norm : σ.NormalizedOn p)
    (ρ : RawNodeEnv L → VisEnv (Player := Player) L Γ)
    (nextId : Nat)
    (hρ : ∀ nid, nextId ≤ nid → InsensitiveTo ρ nid)
    (raw : RawNodeEnv L) :
    FDist.totalWeight (nativeOutcomeDist B σ p ρ nextId raw) = 1 := by
  rw [nativeOutcomeDist_eq_outcomeDist B p σ ρ nextId hρ raw]
  exact outcomeDist_totalWeight_eq_one hd hσ_norm

-- ============================================================================
-- § 4d-ii. Layer 1 — Compiler shape lemmas
-- ============================================================================

-- Equation lemmas for `ofProg`. Used via explicit `rw` only, NOT @[simp].

theorem ofProg_ret (B : MAIDBackend Player L) {Γ : VisCtx Player L}
    (u : U.PayoffExpr Γ) (hl ha hd ρ st₀) :
    MAIDCompileState.ofProg B (Prog.ret u) hl ha hd ρ st₀ =
    st₀.addUtilityNodes (st₀.ctxDeps Γ) (st₀.depsOfVars_lt _)
      (fun who raw => (U.payoff (U.eval u (ρ raw)) who : ℝ))
      (@Finset.univ Player B.fintypePlayer).toList := by
  letI := B.fintypePlayer; rfl

-- ============================================================================
-- § 4d-iii. Layer 2 — Raw assignment stability
-- ============================================================================

open MAID in
/-- Updating a total assignment at a node with the current value is a no-op. -/
theorem updateAssign_self [Fintype Player] {n : Nat}
    {S : @Struct Player _ ‹_› n}
    (a : TAssign S) (nd : Fin n) :
    updateAssign a nd (a nd) = a := by
  funext nd'
  by_cases h : nd' = nd
  · subst h; exact updateAssign_get_self a nd' (a nd')
  · exact updateAssign_get_ne a nd nd' (a nd) h

open MAID in
/-- Snocing `default` doesn't change `extend`. -/
theorem PrefixAssign_snoc_default_extend [Fintype Player] {n : Nat}
    {S : @Struct Player _ ‹_› n} {k : Nat} {hk : k < n}
    (a : PrefixAssign S k (le_of_lt hk)) :
    (a.snoc (default : S.Val ⟨k, hk⟩)).extend = a.extend := by
  rw [PrefixAssign.snoc_extend]
  have hdef : a.extend ⟨k, hk⟩ = default :=
    PrefixAssign.extend_default a ⟨k, hk⟩ (lt_irrefl k)
  rw [← hdef]; exact updateAssign_self a.extend ⟨k, hk⟩

/-- 2b. Old cells: rawOfTAssign at positions i < k is unchanged by snoc.
Proof: snoc_extend gives updateAssign; updateAssign_get_ne at i ≠ k. -/
theorem rawOfTAssign_snoc_old
    (st : MAIDCompileState Player L B)
    {k : Nat} {hk : k < st.nextId}
    (a : @PrefixAssign Player _ B.fintypePlayer st.nextId st.toStruct k (le_of_lt hk))
    (v : st.toStruct.Val ⟨k, hk⟩)
    (i : Nat) (hi : i < k) :
    rawOfTAssign st (a.snoc v).extend i = rawOfTAssign st a.extend i := by
  letI := B.fintypePlayer
  simp only [rawOfTAssign]
  split
  · next hi' =>
    congr 1
    rw [PrefixAssign.snoc_extend, MAID.updateAssign_get_ne]
    exact Fin.ne_of_val_ne (by omega)
  · rfl

/-- ρ is unchanged when rawOfTAssign is extended at position k ≥ st₀.nextId,
because InsensitiveTo says ρ doesn't depend on those positions.
Proof: snoc_extend gives updateAssign; rawOfTAssign of updateAssign differs
from rawOfTAssign of original only at position k; use InsensitiveTo. -/
theorem rawOfTAssign_snoc_rho_stable
    (st : MAIDCompileState Player L B)
    {k : Nat} {hk : k < st.nextId}
    (a : @PrefixAssign Player _ B.fintypePlayer st.nextId st.toStruct k (le_of_lt hk))
    (v : st.toStruct.Val ⟨k, hk⟩)
    (ρ : RawNodeEnv L → α) (hρ : ∀ nid, k ≤ nid → InsensitiveTo ρ nid) :
    ρ (rawOfTAssign st (a.snoc v).extend) = ρ (rawOfTAssign st a.extend) := by
  letI := B.fintypePlayer; sorry

/-- 3b-utility. nodeDistPrefix at a utility node is PMF.pure default. -/
open MAID in
theorem nodeDistPrefix_utility_eq
    (st : MAIDCompileState Player L B)
    (σ : Distilled.Profile (Player := Player) (L := L))
    (hkn : st.KernelNormalized σ)
    {k : Nat} {hk : k ≤ st.nextId}
    (a : @PrefixAssign Player _ B.fintypePlayer st.nextId st.toStruct k hk)
    (nd : Fin st.nextId)
    (hutil : ∃ who ps ufn, st.descAt nd = .utility (B := B) who ps ufn)
    (hparents : ∀ p ∈ st.toStruct.parents nd, p.val < k)
    (hobs : ∀ p ∈ st.toStruct.obsParents nd, p.val < k) :
    @nodeDistPrefix Player _ B.fintypePlayer st.nextId st.toStruct
      (MAIDCompileState.toSem st) (compiledPolicy st σ hkn)
      k hk nd a hparents hobs =
    PMF.pure default := by
  letI := B.fintypePlayer; sorry

/-- 3b-chance. nodeDistPrefix at a chance node equals toPMF of the compiled CPD
applied to rawOfTAssign. -/
open MAID in
theorem nodeDistPrefix_chance_eq
    (st : MAIDCompileState Player L B)
    (σ : Distilled.Profile (Player := Player) (L := L))
    (hkn : st.KernelNormalized σ)
    {k : Nat} {hk : k ≤ st.nextId}
    (a : @PrefixAssign Player _ B.fintypePlayer st.nextId st.toStruct k hk)
    (nd : Fin st.nextId) (τ : L.Ty)
    (deps : Finset Nat)
    (cpd : RawNodeEnv L → FDist (L.Val τ))
    (hn : ∀ raw, FDist.totalWeight (cpd raw) = 1)
    (hdesc : st.descAt nd = .chance τ deps cpd hn)
    (hparents : ∀ p ∈ st.toStruct.parents nd, p.val < k)
    (hobs : ∀ p ∈ st.toStruct.obsParents nd, p.val < k)
    (hcpd_insens : ∀ nid, k ≤ nid → InsensitiveTo cpd nid) :
    @nodeDistPrefix Player _ B.fintypePlayer st.nextId st.toStruct
      (MAIDCompileState.toSem st) (compiledPolicy st σ hkn)
      k hk nd a hparents hobs =
    FDist.toPMF (cpd (rawOfTAssign st a.extend)) (hn _) := by
  letI := B.fintypePlayer; sorry

/-- 3b-decision. nodeDistPrefix at a decision node equals toPMF of the
compiled kernel applied to rawOfTAssign. -/
open MAID in
theorem nodeDistPrefix_decision_eq
    (st : MAIDCompileState Player L B)
    (σ : Distilled.Profile (Player := Player) (L := L))
    (hkn : st.KernelNormalized σ)
    {k : Nat} {hk : k ≤ st.nextId}
    (a : @PrefixAssign Player _ B.fintypePlayer st.nextId st.toStruct k hk)
    (nd : Fin st.nextId) (τ : L.Ty) (who : Player)
    (acts : List (L.Val τ)) (hacts : acts ≠ []) (hnodup : acts.Nodup)
    (obs : Finset Nat)
    (kernel : Distilled.Profile (Player := Player) (L := L) → RawNodeEnv L → FDist (L.Val τ))
    (hdesc : st.descAt nd = .decision τ who acts hacts hnodup obs kernel)
    (hparents : ∀ p ∈ st.toStruct.parents nd, p.val < k)
    (hobs : ∀ p ∈ st.toStruct.obsParents nd, p.val < k)
    (hkernel_insens : ∀ nid, k ≤ nid → InsensitiveTo (kernel σ) nid) :
    @nodeDistPrefix Player _ B.fintypePlayer st.nextId st.toStruct
      (MAIDCompileState.toSem st) (compiledPolicy st σ hkn)
      k hk nd a hparents hobs =
    FDist.toPMF (kernel σ (rawOfTAssign st a.extend))
      (hkn nd (rawOfTAssign st a.extend) τ who acts hacts hnodup obs kernel hdesc) := by
  letI := B.fintypePlayer; sorry

-- ============================================================================
-- § 4d-iv. Bridge lemma
-- ============================================================================

open MAID in
/-- **General bridge**: the prefix fold from `st₀.nextId`, mapped through
`extractOutcome`, equals `nativeOutcomeDist` bound over the accumulator.

Parametrized over the abstract compile state `st` with proof `hst` that it
equals `ofProg ...`, to keep terms small during elaboration. -/
theorem evalFoldPrefix_go_extract_eq
    (B : MAIDBackend Player L)
    {Γ : VisCtx Player L}
    (p : Prog Player L Γ)
    (σ : Profile (Player := Player) (L := L))
    (hl : Legal p) (ha : DistinctActs p)
    (hd : _root_.NormalizedDists (P := Player) (L := L) p)
    (hσ_norm : σ.NormalizedOn p)
    (ρ : RawNodeEnv L → VisEnv (Player := Player) L Γ)
    (st₀ : MAIDCompileState Player L B)
    (hst₀ : st₀.KernelNormalized σ)
    (hρ : ∀ nid, st₀.nextId ≤ nid → InsensitiveTo ρ nid) :
    let _ := B.fintypePlayer
    let st := MAIDCompileState.ofProg B p hl ha hd ρ st₀
    let S := st.toStruct
    let sem := MAIDCompileState.toSem st
    let hkn := ofProg_kernelNormalized B p σ hl ha hd hσ_norm ρ st₀ hst₀
    let pol := compiledPolicy st σ hkn
    let hnat := compiled_naturalOrder st
    let hle := MAIDCompileState.ofProg_nextId_le B p hl ha hd ρ st₀
    ∀ (acc : PMF (@PrefixAssign Player _ B.fintypePlayer st.nextId S st₀.nextId hle)),
    (evalFoldPrefix.go S sem pol hnat st₀.nextId hle acc).map
      (fun a => extractOutcome B p ρ st₀.nextId
        (rawOfTAssign st a.toTAssign))
    = acc.bind (fun a₀ =>
        FDist.toPMF (nativeOutcomeDist B σ p ρ st₀.nextId
          (rawOfTAssign st a₀.extend))
          (nativeOutcomeDist_totalWeight B p σ hd hσ_norm ρ st₀.nextId hρ _)) := by
  simp only; intro μ
  induction p generalizing st₀ with
  | letExpr x e k ih =>
    simp only [MAIDCompileState.ofProg, extractOutcome, nativeOutcomeDist]
    exact ih hl ha hd hσ_norm _ _ (st₀.addVar_kernelNormalized σ _ _ _ _ hst₀)
      (fun nid hn raw tv =>
        VisEnv.cons_ext (by rw [hρ nid hn raw tv]) (hρ nid hn raw tv)) μ
  | reveal y who x hx k ih =>
    simp only [MAIDCompileState.ofProg, extractOutcome, nativeOutcomeDist]
    exact ih hl ha hd hσ_norm _ _ (st₀.addVar_kernelNormalized σ _ _ _ _ hst₀)
      (fun nid hn raw tv =>
        VisEnv.cons_ext (by rw [hρ nid hn raw tv]) (hρ nid hn raw tv)) μ
  | ret u =>
    simp only [extractOutcome, nativeOutcomeDist, FDist.toPMF_pure]
    -- Goal: map (U.eval u ∘ ρ ∘ rawOfTAssign st ∘ toTAssign) (go ... μ)
    --     = μ.bind (fun a₀ => PMF.pure (U.eval u (ρ (rawOfTAssign st a₀.extend))))
    -- Strategy: show fold through utility nodes is transparent for rawOfTAssign.
    -- Each utility step snocs default; PrefixAssign_snoc_default_extend shows
    -- extend is unchanged; so rawOfTAssign ∘ toTAssign = rawOfTAssign ∘ extend.
    -- This requires induction on the players list in addUtilityNodes.
    sorry
  | sample x τ m D' k ih =>
    -- Step 1: Unfold ofProg, extractOutcome, nativeOutcomeDist one level
    simp only [MAIDCompileState.ofProg, extractOutcome, nativeOutcomeDist]
    -- Step 2: The fold starts at st₀.nextId which is a chance node.
    -- Unfold evalFoldPrefix.go one step to get evalStepPrefix + go from st₀.nextId+1.
    -- Step 3: evalStepPrefix draws from nodeDistPrefix at the chance node.
    -- By nodeDistPrefix_chance_eq, this equals toPMF of the CPD on rawOfTAssign.
    -- Step 4: After snoc v, use rawOfTAssign_snoc_rho_stable to show ρ stable,
    -- and readVal_extend_self to read back v. This gives the new ρ'.
    -- Step 5: Apply IH with the new st₀' = (addNode ...).2.addVar ...,
    -- new ρ' = cons (readVal ...) ρ, and the stepped accumulator.
    -- The IH hypotheses (kernel normalized, InsensitiveTo) follow from
    -- addNode/addVar preservation lemmas + readVal_extend_ne + hρ.
    sorry
  | @commit _ x who b acts R k ih =>
    -- Analogous to sample: unfold, step fold, match decision node distribution,
    -- apply IH. The kernel normalization comes from hσ_norm.
    simp only [MAIDCompileState.ofProg, extractOutcome, nativeOutcomeDist]
    sorry

open MAID in
/-- **Bridge lemma.** Mapping `extractOutcome` over the MAID assignment
distribution yields the Vegas outcome distribution. -/
theorem maid_map_extract_eq_outcomeDist
    (B : MAIDBackend Player L)
    {Γ : VisCtx Player L}
    (p : Prog Player L Γ)
    (env : VisEnv (Player := Player) L Γ)
    (σ : Profile (Player := Player) (L := L))
    (hl : Legal p) (ha : DistinctActs p)
    (hd : _root_.NormalizedDists (P := Player) (L := L) p)
    (hσ_norm : σ.NormalizedOn p) :
    let _ : Fintype Player := B.fintypePlayer
    let st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty
    let S := st.toStruct
    let sem := MAIDCompileState.toSem st
    let hkn := ofProg_kernelNormalized B p σ hl ha hd hσ_norm
        (fun _ => env) .empty (MAIDCompileState.empty_kernelNormalized σ)
    let pol := compiledPolicy st σ hkn
    let extract : @TAssign Player _ B.fintypePlayer st.nextId S → U.Outcome :=
      fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a)
    PMF.map extract (evalAssignDist S sem pol) =
      (outcomeDist σ p env).toPMF (outcomeDist_totalWeight_eq_one hd hσ_norm) := by
  simp only
  letI : Fintype Player := B.fintypePlayer
  have hnat := compiled_naturalOrder
    (MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty)
  -- Rewrite evalAssignDist via prefix fold
  rw [← evalFoldPrefix_eq_evalAssignDist _ _ _ hnat, PMF.map_comp]
  -- Apply general bridge
  have hbridge := evalFoldPrefix_go_extract_eq B p σ hl ha hd hσ_norm
    (fun _ => env) .empty (MAIDCompileState.empty_kernelNormalized σ)
    (fun _ _ _ _ => rfl) (PMF.pure (PrefixAssign.empty _))
  simp only [Function.comp_def]
  exact hbridge.trans (by
    rw [PMF.pure_bind]
    congr 1
    exact nativeOutcomeDist_eq_outcomeDist_init B p σ env _)

-- ============================================================================
-- § 4e. Main theorem
-- ============================================================================

open MAID in
/-- **B2: Vegas to MAID distribution equality.** -/
theorem vegas_maid_dist_eq
    (B : MAIDBackend Player L)
    {Γ : VisCtx Player L}
    (p : Prog Player L Γ)
    (env : VisEnv (Player := Player) L Γ)
    (σ : Profile (Player := Player) (L := L))
    (hl : Legal p) (ha : DistinctActs p)
    (hd : _root_.NormalizedDists (P := Player) (L := L) p)
    (hσ_norm : σ.NormalizedOn p) :
    let _ : Fintype Player := B.fintypePlayer
    let st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty
    let S := st.toStruct
    let sem := MAIDCompileState.toSem st
    ∃ (pol : @Policy Player _ B.fintypePlayer st.nextId S)
      (extract : @TAssign Player _ B.fintypePlayer st.nextId S → U.Outcome),
      PMF.map extract (evalAssignDist S sem pol) =
        (outcomeDist σ p env).toPMF (outcomeDist_totalWeight_eq_one hd hσ_norm) := by
  let _ := B.fintypePlayer
  let st := MAIDCompileState.ofProg B p hl ha hd (fun _ => env) .empty
  let hkn := ofProg_kernelNormalized B p σ hl ha hd hσ_norm
      (fun _ => env) .empty (MAIDCompileState.empty_kernelNormalized σ)
  let pol := compiledPolicy st σ hkn
  let extract : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct → U.Outcome :=
    fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a)
  exact ⟨pol, extract,
    maid_map_extract_eq_outcomeDist B p env σ hl ha hd hσ_norm⟩

end Distilled
