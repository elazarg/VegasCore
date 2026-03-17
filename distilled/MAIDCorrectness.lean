import distilled.MAIDFDistFold
import GameTheory.Languages.MAID.Prefix

namespace Distilled

open MAID

variable {Player : Type} [DecidableEq Player] {L : ExprLanguage}
variable [E : VisExprKit Player L] [D : VisDistKit Player L] [U : VisPayoffKit Player L]
variable {B : MAIDBackend Player L}

noncomputable instance : DecidableEq (RawNodeEnv L) := Classical.decEq _

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
-- § 2. Native fold by recursion on Prog (no Fin, no TAssign)
-- ============================================================================

/-- The native fold over `FDist (RawNodeEnv L)`, defined by structural
recursion on `Prog` to match `outcomeDist` 1:1.

- `ret`: identity (utility nodes don't affect raw env)
- `letExpr`/`reveal`: recurse with updated ρ, no new draw
- `sample`: draw from `D.eval D'`, extend raw env, recurse
- `commit`: draw from `σ.commit`, extend raw env, recurse -/
noncomputable def nativeFoldProg
    (B : MAIDBackend Player L)
    (σ : Profile (Player := Player) (L := L)) :
    {Γ : VisCtx Player L} →
    (p : Prog Player L Γ) →
    (ρ : RawNodeEnv L → VisEnv (Player := Player) L Γ) →
    (nextId : Nat) →
    FDist (RawNodeEnv L) → FDist (RawNodeEnv L)
  | _, .ret _, _, _, acc => acc
  | _, .letExpr (b := b) x e k, ρ, nextId, acc =>
      nativeFoldProg B σ k
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := .pub b)
          (E.eval e (ρ raw)) (ρ raw))
        nextId acc
  | _, .sample x τ _m D' k, ρ, nextId, acc =>
      let acc' := FDist.bind acc (fun raw =>
        FDist.map (fun v => raw.extend nextId ⟨τ.base, v⟩)
          (D.eval D' (VisEnv.projectDist (Player := Player) (L := L) τ _ (ρ raw))))
      nativeFoldProg B σ k
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := τ)
          (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw))
        (nextId + 1) acc'
  | _, .commit (b := b) x who acts R k, ρ, nextId, acc =>
      let acc' := FDist.bind acc (fun raw =>
        FDist.map (fun v => raw.extend nextId ⟨b, v⟩)
          (σ.commit who x acts R (VisEnv.toView (Player := Player) (L := L) who (ρ raw))))
      nativeFoldProg B σ k
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := .hidden who b)
          (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw))
        (nextId + 1) acc'
  | _, .reveal (b := b) y _who _x hx k, ρ, nextId, acc =>
      nativeFoldProg B σ k
        (fun raw =>
          let v : L.Val b := VisEnv.get (Player := Player) (L := L) (ρ raw) hx
          VisEnv.cons (Player := Player) (L := L) (x := y) (τ := .pub b) v (ρ raw))
        nextId acc

/-- Outcome extractor: mirrors `ofProg`'s ρ-threading, returns the outcome. -/
noncomputable def outcomeExtractor
    (B : MAIDBackend Player L) :
    {Γ : VisCtx Player L} →
    Prog Player L Γ →
    (RawNodeEnv L → VisEnv (Player := Player) L Γ) →
    Nat → (RawNodeEnv L → U.Outcome)
  | _, .ret u, ρ, _ => fun raw => U.eval u (ρ raw)
  | _, .letExpr (b := b) x e k, ρ, nextId =>
      outcomeExtractor B k
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := .pub b)
          (E.eval e (ρ raw)) (ρ raw))
        nextId
  | _, .sample x τ _m _D' k, ρ, nextId =>
      outcomeExtractor B k
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := τ)
          (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw))
        (nextId + 1)
  | _, .commit (b := b) x who _acts _R k, ρ, nextId =>
      outcomeExtractor B k
        (fun raw => VisEnv.cons (Player := Player) (L := L) (x := x) (τ := .hidden who b)
          (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw))
        (nextId + 1)
  | _, .reveal (b := b) y _who _x hx k, ρ, nextId =>
      outcomeExtractor B k
        (fun raw =>
          let v : L.Val b := VisEnv.get (Player := Player) (L := L) (ρ raw) hx
          VisEnv.cons (Player := Player) (L := L) (x := y) (τ := .pub b) v (ρ raw))
        nextId

-- ============================================================================
-- § 3. Core theorem: nativeFoldProg = outcomeDist
-- ============================================================================

/-- `nativeFoldProg` distributes `FDist.map` through `FDist.bind`. -/
theorem nativeFoldProg_map_bind
    (B : MAIDBackend Player L)
    {Γ : VisCtx Player L} {α β : Type} [DecidableEq α] [DecidableEq β]
    (p : Prog Player L Γ)
    (σ : Profile (Player := Player) (L := L))
    (ρ : RawNodeEnv L → VisEnv (Player := Player) L Γ)
    (nextId : Nat)
    (f : RawNodeEnv L → β)
    (d : FDist α)
    (g : α → FDist (RawNodeEnv L)) :
    FDist.map f (nativeFoldProg B σ p ρ nextId (FDist.bind d g)) =
    FDist.bind d (fun a => FDist.map f (nativeFoldProg B σ p ρ nextId (g a))) := by
  induction p generalizing nextId d g with
  | ret _ =>
    simp only [nativeFoldProg, FDist.bind_map]
  | letExpr x e k ih =>
    simp only [nativeFoldProg]
    exact ih _ _ _ _
  | sample x τ m D' k ih =>
    simp only [nativeFoldProg]
    -- nativeFoldProg_k ... (bind (bind d g) F) = bind d (fun a => nativeFoldProg_k ... (bind (g a) F))
    -- where F raw = map (extend raw nid ...) (D.eval D' ...)
    -- This follows from ih + bind_assoc
    rw [FDist.bind_assoc]
    exact ih _ _ _ _
  | commit x who acts R k ih =>
    simp only [nativeFoldProg]
    rw [FDist.bind_assoc]
    exact ih _ _ _ _
  | reveal y who x hx k ih =>
    simp only [nativeFoldProg]
    exact ih _ _ _ _

/-- **Core theorem.** The native fold, projected to outcomes, equals `outcomeDist`.

The proof is by structural induction on `Prog`. Each case is definitional
or uses `readVal_extend_self` + `InsensitiveTo` for the ρ roundtrip. -/
theorem nativeFoldProg_eq_outcomeDist
    (B : MAIDBackend Player L)
    {Γ : VisCtx Player L}
    (p : Prog Player L Γ)
    (σ : Profile (Player := Player) (L := L))
    (ρ : RawNodeEnv L → VisEnv (Player := Player) L Γ)
    (nextId : Nat)
    (hρ : ∀ nid, nextId ≤ nid → InsensitiveTo ρ nid) :
    ∀ raw₀ : RawNodeEnv L,
    FDist.map (outcomeExtractor B p ρ nextId)
      (nativeFoldProg B σ p ρ nextId (FDist.pure raw₀))
    = outcomeDist σ p (ρ raw₀) := by
  induction p generalizing nextId with
  | ret u =>
    intro raw₀
    -- nativeFoldProg for ret = acc (identity)
    -- outcomeExtractor for ret = fun raw => U.eval u (ρ raw)
    -- FDist.map f (pure raw₀) = pure (f raw₀) = FDist.map_pure
    simp only [nativeFoldProg, outcomeExtractor, outcomeDist, FDist.map_pure]
  | letExpr x e k ih =>
    intro raw₀
    simp only [nativeFoldProg, outcomeExtractor, outcomeDist]
    exact ih _ nextId (fun nid hn raw tv => VisEnv.cons_ext (by rw [hρ nid hn raw tv]) (hρ nid hn raw tv)) raw₀
  | sample x τ m D' k ih =>
    intro raw₀
    -- Unfold definitions
    simp only [nativeFoldProg, outcomeExtractor, outcomeDist, FDist.pure_bind]
    -- Goal: map extract_k (nativeFoldProg_k ρ' (nid+1) (map (extend raw₀ nid ⟨τ,·⟩) μ))
    --     = bind μ (fun v => outcomeDist σ k (cons v (ρ raw₀)))
    -- where μ = D.eval D' (proj (ρ raw₀)), nid = nextId
    -- Insensitivity for ρ'
    have hρ' : ∀ nid', nextId + 1 ≤ nid' → InsensitiveTo
        (fun raw => VisEnv.cons (Player := Player) (L := L)
          (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw)) nid' := by
      intro nid' hn' raw tv
      exact VisEnv.cons_ext
        (readVal_extend_ne raw nid' nextId tv τ.base (by omega))
        (hρ nid' (by omega) raw tv)
    -- Rewrite FDist.map as bind-pure then distribute
    sorry
    congr 1; funext v
    rw [ih _ (nextId + 1) hρ']
    congr 1
    exact VisEnv.cons_ext (readVal_extend_self (B := B) raw₀ nextId τ.base v)
      (hρ nextId (le_refl _) raw₀ ⟨τ.base, v⟩)
  | commit x who acts R k ih =>
    intro raw₀
    simp only [nativeFoldProg, outcomeExtractor, outcomeDist]
    sorry
  | reveal y who x hx k ih =>
    intro raw₀
    simp only [nativeFoldProg, outcomeExtractor, outcomeDist]
    exact ih _ nextId (fun nid hn raw tv => VisEnv.cons_ext (by rw [hρ nid hn raw tv]) (hρ nid hn raw tv)) raw₀

-- ============================================================================
-- § 4. Main theorem
-- ============================================================================

theorem compiled_naturalOrder (st : MAIDCompileState Player L B) :
    @Struct.NaturalOrder Player _ B.fintypePlayer st.nextId st.toStruct := by
  let _ : Fintype Player := B.fintypePlayer
  intro nd p hp
  rcases Finset.mem_image.mp hp with ⟨d, hd, rfl⟩
  exact st.descAt_parent_lt nd d.2

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
        (outcomeDist σ p env).toPMF (outcomeDist_totalWeight_eq_one hd hσ_norm) :=
  sorry

end Distilled
