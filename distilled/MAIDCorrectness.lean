import GameTheory.Languages.MAID.Prefix
import distilled.MAIDCompile
import distilled.OutcomeKernelBridge
import distilled.MAIDFDistFold

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

/-- If `f` is insensitive at position `k`, then any two raw environments that
agree on all positions except `k` give the same result under `f`. -/
theorem InsensitiveTo.eq_of_eq_off [Nonempty (TaggedVal L)]
    {f : RawNodeEnv L → α} {k : Nat}
    (hins : InsensitiveTo f k)
    {raw₁ raw₂ : RawNodeEnv L}
    (hoff : ∀ i, i ≠ k → raw₁ i = raw₂ i) :
    f raw₁ = f raw₂ := by
  obtain ⟨tv⟩ := ‹Nonempty (TaggedVal L)›
  calc f raw₁ = f (raw₁.extend k tv) := (hins raw₁ tv).symm
    _ = f (raw₂.extend k tv) := by
        congr 1; funext i; simp only [RawNodeEnv.extend]
        split <;> [rfl; exact hoff i (by assumption)]
    _ = f raw₂ := hins raw₂ tv

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
  change PMF (CompiledNode.valType (st.descAt d.1))
  exact match hdesc : st.descAt d.1 with
  | .decision τ _who acts hacts hnodup obs kernel =>
      @FDist.toPMF (L.Val τ) L.decEqVal (kernel σ (st.rawEnvOfCfg cfg))
        (hkn d.1 (st.rawEnvOfCfg cfg) τ _ acts hacts hnodup obs kernel hdesc)
  | .chance τ ps cpd hn =>
      absurd d.2 (by simp [MAIDCompileState.toStruct, CompiledNode.kind, hdesc])
  | .utility who ps ufn =>
      absurd d.2 (by simp [MAIDCompileState.toStruct, CompiledNode.kind, hdesc])

noncomputable instance (nd : CompiledNode Player L B) :
    DecidableEq (CompiledNode.valType (B := B) nd) := by
  cases nd with
  | chance τ _ _ _ => exact L.decEqVal
  | decision τ _ _ _ _ _ _ => exact L.decEqVal
  | utility _ _ _ => exact instDecidableEqPUnit

/-- Per-node FDist dispatch: given a `CompiledNode`, produce the FDist over
its value type. This is a plain `match` on the node descriptor, making it
easy for `simp` to unfold. -/
noncomputable def compiledNodeFDist
    (_st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (rawP : RawNodeEnv L) (rawO : RawNodeEnv L) :
    (c : CompiledNode Player L B) → FDist (CompiledNode.valType c)
  | .chance _τ _ cpd _ => cpd rawP
  | .decision _τ _ _ _ _ _ kernel => kernel σ rawO
  | .utility _ _ _ => FDist.pure ()

/-- FDist node data produced by the compiler. -/
noncomputable def compiledFDistData
    (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (hkn : st.KernelNormalized σ) :
    @FDistNodeData Player _ B.fintypePlayer _ st.toStruct :=
  letI := B.fintypePlayer
  { dist := fun nd a =>
      compiledNodeFDist st σ
        (st.rawEnvOfCfg (projCfg a (st.toStruct.parents nd)))
        (st.rawEnvOfCfg (projCfg a (st.toStruct.obsParents nd)))
        (st.descAt nd)
    normalized := by
      intro nd a
      change FDist.totalWeight (compiledNodeFDist st σ _ _ (st.descAt nd)) = 1
      match hdesc : st.descAt nd with
      | .chance _ _ _ hn => simp only [compiledNodeFDist]; exact hn _
      | .decision _ _ _ _ _ _ _ => simp only [compiledNodeFDist]; exact hkn nd _ _ _ _ _ _ _ _ hdesc
      | .utility _ _ _ => simp [compiledNodeFDist, FDist.totalWeight_pure] }

/-- The dist field of `compiledFDistData` equals `compiledNodeFDist` applied to `st.descAt nd`.
The `letI` in the type is required to match the instance scope inside the definition. -/
@[congr] theorem FDist.toPMF_congr [DecidableEq α]
    {d₁ d₂ : FDist α} {h₁ h₂} (heq : d₁ = d₂) :
    FDist.toPMF d₁ h₁ = FDist.toPMF d₂ h₂ := by subst heq; rfl

/-- Transporting `PMF.pure default` along any index equality gives `PMF.pure default`. -/
theorem eq_rec_pmf_pure_default
    {ι : Type} {F : ι → Type} [∀ i, Inhabited (F i)]
    {i j : ι} (h : i = j) :
    (h ▸ (PMF.pure (α := F i) default : PMF (F i)) : PMF (F j)) =
    PMF.pure default := by
  subst h; rfl

/-- `toPMF` commutes past a `CompiledNode` match: proof irrelevance lets us
case-split the node descriptor without disturbing the normalization proof. -/
theorem FDist.toPMF_compiledNode_comm
    (f : (c : CompiledNode Player L B) → FDist (CompiledNode.valType c))
    (c : CompiledNode Player L B)
    (h : FDist.totalWeight (f c) = 1) :
    FDist.toPMF (f c) h =
    match c with
    | .chance τ ps cpd hn => FDist.toPMF (f (.chance τ ps cpd hn)) h
    | .decision τ who acts ha hnd obs k =>
        FDist.toPMF (f (.decision τ who acts ha hnd obs k)) h
    | .utility who ps ufn => FDist.toPMF (f (.utility who ps ufn)) h := by
  cases c <;> rfl

@[simp] theorem toStruct_kind (st : MAIDCompileState Player L B) (nd : Fin st.nextId) :
    letI := B.fintypePlayer; st.toStruct.kind nd = (st.descAt nd).kind := rfl

@[simp] theorem toStruct_Val (st : MAIDCompileState Player L B) (nd : Fin st.nextId) :
    letI := B.fintypePlayer; st.toStruct.Val nd = CompiledNode.valType (st.descAt nd) := rfl

theorem compiledFDistData_dist_eq
    (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (hkn : st.KernelNormalized σ)
    (nd : Fin st.nextId)
    (a : @TAssign Player _ B.fintypePlayer st.nextId st.toStruct) :
    letI := B.fintypePlayer
    (compiledFDistData st σ hkn).dist nd a =
    compiledNodeFDist st σ
      (st.rawEnvOfCfg (projCfg a (st.toStruct.parents nd)))
      (st.rawEnvOfCfg (projCfg a (st.toStruct.obsParents nd)))
      (st.descAt nd) := rfl

theorem compiledFDistData_compatible
    (st : MAIDCompileState Player L B)
    (σ : Profile (Player := Player) (L := L))
    (hkn : st.KernelNormalized σ) :
    @FDistNodeDataCompatible _ _ B.fintypePlayer _ _ (compiledFDistData st σ hkn)
      (MAIDCompileState.toSem st) (compiledPolicy st σ hkn) := by
  letI := B.fintypePlayer
  intro nd a
  -- Show the goal with compiledNodeFDist explicitly, so st.descAt nd appears
  -- syntactically in both the FDist type and the toPMF application.
  let rawP := st.rawEnvOfCfg (projCfg a (st.toStruct.parents nd))
  let rawO := st.rawEnvOfCfg (projCfg a (st.toStruct.obsParents nd))
  have hnorm : FDist.totalWeight (compiledNodeFDist st σ rawP rawO (st.descAt nd)) = 1 :=
    (compiledFDistData st σ hkn).normalized nd a
  -- Suffices: prove equality for each CompiledNode case.
  -- Use suffices to introduce the RHS with the right dependent type,
  -- then close the suffices by rfl.
  suffices ∀ (c : CompiledNode Player L B)
      (hn : FDist.totalWeight (compiledNodeFDist st σ rawP rawO c) = 1)
      (hc : st.descAt nd = c),
      FDist.toPMF (compiledNodeFDist st σ rawP rawO c) hn =
        (hc ▸ nodeDist st.toStruct st.toSem (compiledPolicy st σ hkn) nd a) by
    exact this (st.descAt nd) hnorm rfl
  intro c hn hc
  cases c with
  | chance τ ps cpd hcn =>
      simp_all only [compiledNodeFDist, nodeDist, toStruct_kind, CompiledNode.kind,
         MAIDCompileState.toSem, eq_mpr_eq_cast, id_eq]
      grind only
  | decision τ who acts ha hnd obs k =>
      simp_all only [compiledNodeFDist, nodeDist, toStruct_kind, CompiledNode.kind,
        id_eq, compiledPolicy]
      grind only
  | utility who ps ufn =>
      -- Both sides are in PMF Unit (defeq to PMF (CompiledNode.valType (utility ...))).
      -- PMF Unit is a subsingleton, so they are equal.
      have hsub : Subsingleton (PMF Unit) := ⟨fun a b => PMF.ext fun ⟨⟩ => by
        have ha := a.2.tsum_eq
        rw [tsum_eq_single ()
          (fun x hx => absurd (Subsingleton.elim x ()) hx)] at ha
        have hb := b.2.tsum_eq
        rw [tsum_eq_single ()
          (fun x hx => absurd (Subsingleton.elim x ()) hx)] at hb
        exact ha.trans hb.symm⟩
      exact hsub.elim _ _

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
    (hd : NormalizedDists p)
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
  rfl

-- ============================================================================
-- § 4d-iii. Layer 2 & 3 — Raw stability + Distribution matching
-- ============================================================================

section BridgeLemmas

open MAID

/-- Updating a total assignment at a node with the current value is a no-op. -/
theorem updateAssign_self' [Fintype Player] {n : Nat} {S : @Struct Player _ ‹_› n}
    (a : TAssign S) (nd : Fin n) :
    updateAssign a nd (a nd) = a := by
  funext nd'
  by_cases h : nd' = nd
  · subst h
    exact updateAssign_get_self a nd' (a nd')
  · exact updateAssign_get_ne a nd nd' (a nd) h

/-- Snocing `default` doesn't change `extend`. -/
theorem PrefixAssign_snoc_default_extend' [Fintype Player] {n : Nat}
    {S : @Struct Player _ ‹_› n} {k : Nat} {hk : k < n}
    (a : PrefixAssign S k (le_of_lt hk)) :
    (a.snoc (default : S.Val ⟨k, hk⟩)).extend = a.extend := by
  rw [PrefixAssign.snoc_extend]
  have hdef : a.extend ⟨k, hk⟩ = default :=
    PrefixAssign.extend_default a ⟨k, hk⟩ (lt_irrefl k)
  rw [← hdef]; exact updateAssign_self' a.extend ⟨k, hk⟩

end BridgeLemmas

-- ============================================================================
-- § 4d-iii-a. Utility fold transparency
-- ============================================================================

open MAID in
omit E D U B in
/-- `evalStepPrefix` at a utility node just snocs `default` (pure, no randomness). -/
private theorem evalStepPrefix_utility
    [Fintype Player] {n : Nat} {S : Struct Player n}
    {sem : Sem S} {pol : Policy S}
    {k : Nat} {hk : k < n}
    {μ : PMF (PrefixAssign S k (le_of_lt hk))}
    {hparents : ∀ p ∈ S.parents ⟨k, hk⟩, p.val < k}
    {hobs : ∀ p ∈ S.obsParents ⟨k, hk⟩, p.val < k}
    {who : Player}
    (hkind : S.kind ⟨k, hk⟩ = .utility who) :
    evalStepPrefix S sem pol μ hparents hobs =
    μ.map (fun a => a.snoc default) := by
  simp only [evalStepPrefix]
  have hndp : ∀ (a : PrefixAssign S k (le_of_lt hk)),
      nodeDistPrefix S sem pol ⟨k, hk⟩ a hparents hobs = PMF.pure default := by
    intro a
    unfold nodeDistPrefix
    split <;> [skip; skip; rfl]
    all_goals (rename_i hk'; rw [hk'] at hkind; cases hkind)
  have mp : ∀ (a : PrefixAssign S k (le_of_lt hk)),
      PMF.map (a.snoc ·) (PMF.pure (default : S.Val ⟨k, hk⟩)) =
      PMF.pure (a.snoc default) := by
    intro a; ext b; simp only [PMF.map_apply, PMF.pure_apply]
    rw [tsum_eq_single default (fun x hx => by simp [hx])]; simp
  simp_rw [hndp, mp]
  rw [show (fun a : PrefixAssign S k (le_of_lt hk) =>
    (PMF.pure (a.snoc default))) = PMF.pure ∘ (fun a => a.snoc default) from rfl,
    PMF.bind_pure_comp]

open MAID in
omit E D U B in
/-- **Utility fold transparency.** If all nodes from `k` onwards are utility,
the fold is deterministic (only snocs `default`) and `toTAssign` of the
result agrees with `extend` of the input prefix. -/
private theorem go_utility_transparent
    [Fintype Player] {n : Nat} {S : Struct Player n}
    (sem : Sem S) (pol : Policy S) (hnat : S.NaturalOrder)
    {α : Type} (f : TAssign S → α)
    (k : Nat) (hk : k ≤ n)
    (hutility : ∀ (i : Fin n), k ≤ i.val → ∃ who, S.kind i = .utility who)
    (μ : PMF (PrefixAssign S k hk)) :
    (evalFoldPrefix.go S sem pol hnat k hk μ).map (f ∘ PrefixAssign.toTAssign) =
    μ.map (f ∘ PrefixAssign.extend) := by
  induction h : n - k using Nat.strongRecOn generalizing k μ with
  | _ d ih =>
    by_cases hlt : k < n
    · -- Step: unfold go, one utility node
      conv_lhs => rw [evalFoldPrefix.go]; simp only [hlt, ↓reduceDIte]
      obtain ⟨who, hkind⟩ := hutility ⟨k, hlt⟩ (le_refl k)
      rw [ih (n - (k + 1)) (by omega) (k + 1) hlt
        (fun i hi => hutility i (by omega)) _ rfl]
      -- Goal: (evalStepPrefix ...).map (f ∘ extend) = μ.map (f ∘ extend)
      rw [evalStepPrefix_utility hkind, PMF.map_comp]
      congr 1; funext a
      exact congrArg f (PrefixAssign_snoc_default_extend' a)
    · -- Base: k = n
      have hkn : k = n := by omega
      subst hkn
      conv_lhs => rw [evalFoldPrefix.go]; simp only [lt_irrefl, ↓reduceDIte]
      congr 1; funext a
      exact congrArg f a.toTAssign_eq_extend

/-- `addUtilityNodes` preserves `descAt` for old nodes. -/
theorem MAIDCompileState.addUtilityNodes_descAt_old
    (st : MAIDCompileState Player L B)
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId)
    (ufn : Player → RawNodeEnv L → ℝ) (players : List Player)
    (j : Nat) (hj : j < st.nextId) :
    let stf := st.addUtilityNodes deps hdeps ufn players
    (stf.descAt ⟨j, Nat.lt_of_lt_of_le hj (by
      rw [addUtilityNodes_nextId]; omega)⟩) =
    st.descAt ⟨j, hj⟩ := by
  induction players generalizing st with
  | nil => rfl
  | cons who rest ih =>
    simp only [addUtilityNodes]
    rw [ih]; exact addNode_descAt_old st _ _ ⟨j, hj⟩

/-- All nodes added by `addUtilityNodes` are utility nodes in the struct. -/
theorem MAIDCompileState.addUtilityNodes_all_utility
    (st : MAIDCompileState Player L B)
    (deps : Finset Nat) (hdeps : ∀ d ∈ deps, d < st.nextId)
    (ufn : Player → RawNodeEnv L → ℝ) (players : List Player)
    (i : Fin (st.addUtilityNodes deps hdeps ufn players).nextId)
    (hi : st.nextId ≤ i.val) :
    let _ := B.fintypePlayer
    ∃ who, (st.addUtilityNodes deps hdeps ufn players).toStruct.kind i =
      NodeKind.utility who := by
  letI := B.fintypePlayer
  -- By induction on `players`: each step adds a utility node at `st.nextId`,
  -- and `addUtilityNodes_descAt_old` preserves old nodes.
  sorry

-- ============================================================================
-- § 4d-iii-b. Raw-agreement and rho-stability for snoc
-- ============================================================================

open MAID in
/-- `rawOfTAssign` at a snoced prefix agrees with the un-snoced version
at every node except the snoc position `k`. -/
theorem rawOfTAssign_agree_off_snoc
    (B : MAIDBackend Player L)
    (st : MAIDCompileState Player L B)
    (k : Nat) (hk : k < st.nextId) (hle : k ≤ st.nextId)
    (a : @PrefixAssign Player _ B.fintypePlayer st.nextId st.toStruct k hle)
    (v : @Struct.Val Player _ B.fintypePlayer st.nextId st.toStruct ⟨k, hk⟩) :
    let _ := B.fintypePlayer
    ∀ j, j ≠ k →
      rawOfTAssign st (a.snoc v).extend j = rawOfTAssign st a.extend j := by
  letI := B.fintypePlayer
  -- snoc_extend converts snoc to updateAssign; updateAssign at j ≠ k is identity
  sorry

open MAID in
/-- Corollary: if `ρ` is insensitive at the snoc position `k`,
then `ρ` gives the same result on the snoced and un-snoced raw envs. -/
theorem rho_stable_off_snoc
    [Nonempty (TaggedVal L)]
    (B : MAIDBackend Player L)
    (st : MAIDCompileState Player L B)
    (k : Nat) (hk : k < st.nextId) (hle : k ≤ st.nextId)
    {ρ : RawNodeEnv L → α}
    (hins : InsensitiveTo ρ k)
    (a : @MAID.PrefixAssign Player _ B.fintypePlayer st.nextId st.toStruct k hle)
    (v : @MAID.Struct.Val Player _ B.fintypePlayer st.nextId st.toStruct ⟨k, hk⟩) :
    let _ := B.fintypePlayer
    ρ (rawOfTAssign st (a.snoc v).extend) = ρ (rawOfTAssign st a.extend) := by
  letI := B.fintypePlayer
  exact InsensitiveTo.eq_of_eq_off hins (rawOfTAssign_agree_off_snoc B st k hk hle a v)

-- ============================================================================
-- § 4d-iii-c. Head-node shape + distribution matching
-- ============================================================================

-- Head-node shape: after compiling `sample`/`commit`, the node at
-- st₀.nextId is the expected chance/decision node. Proved via
-- `addNode_descAt_new` + `ofProg_nextId_le` to show later compilation
-- preserves the node descriptor.
--
-- Distribution matching: `nodeDistPrefix` at the compiled node matches
-- the stored CPD/kernel applied to `rawOfTAssign st a.extend`.
-- Uses `nodeDistPrefix_eq_nodeDist` + `toSem` unfolding + an
-- `hρ_agree` hypothesis that the CPD/kernel gives the same result
-- on the projected parent config vs the full raw env.
--
-- These lemmas are sorry'd for now; their proofs are mechanical
-- (unfold toStruct/toSem definitions, use descAt preservation)
-- but require careful Fin arithmetic.

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
    -- Layer 3: all nodes ≥ st₀.nextId are utility → fold is transparent
    letI := B.fintypePlayer
    exact go_utility_transparent
      (MAIDCompileState.toSem _) (compiledPolicy _ σ _) (compiled_naturalOrder _)
      (fun a => U.eval u (ρ (rawOfTAssign _ a)))
      st₀.nextId _
      (fun i hi => MAIDCompileState.addUtilityNodes_all_utility st₀ _ _ _ _ i hi)
      μ
  | sample x τ m D' k ih =>
    -- The fold starts at st₀.nextId. The first node is a chance node.
    -- We need to unfold go one step, then apply IH at st₀.nextId + 1.
    -- But the IH is generalized over st₀, so we apply it with
    -- st₀' = (st₀.addNode ...).2.addVar ... (which has nextId = st₀.nextId + 1).
    --
    -- Step 1: Simplify extractOutcome and nativeOutcomeDist for sample
    simp only [extractOutcome, nativeOutcomeDist]
    -- Now both sides have ofProg B k ... inside, matching the IH.
    -- Step 2: Apply IH. The ofProg for sample definitionally equals
    -- ofProg B k ... ρ' st₁, so the IH should unify.
    -- But the fold starts at st₀.nextId, not st₁.nextId = st₀.nextId + 1.
    -- We need to decompose the fold: go st₀.nextId = go (st₀.nextId+1) ∘ step.
    -- This decomposition + matching the step distribution is the core difficulty.
    sorry
  | @commit _ x who b acts R k ih =>
    simp only [extractOutcome, nativeOutcomeDist]
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
    let data := compiledFDistData st σ
               (ofProg_kernelNormalized B p σ hl ha hd hσ_norm _ _ _)
    let sem := MAIDCompileState.toSem st
    let pol := compiledPolicy st σ (ofProg_kernelNormalized B p σ hl ha hd hσ_norm _ _ _)
    let extract : TAssign st.toStruct → U.Outcome :=
      fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a)
    PMF.map extract (evalFoldFDist data (compiled_naturalOrder st)).toPMF _ =
      (outcomeDist σ p env).toPMF (outcomeDist_totalWeight_eq_one hd hσ_norm) := by
  rw [evalFoldFDist_toPMF_eq_evalFold data sem pol
        (compiledFDistData_compatible st σ _)]
  exact maid_map_extract_eq_outcomeDist B p env σ hl ha hd hσ_norm

end Distilled
