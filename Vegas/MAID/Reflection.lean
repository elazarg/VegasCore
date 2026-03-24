import Vegas.StrategicPMF
import Vegas.MAID.Correctness
import Vegas.MAID.PureBridge

/-!
# MAID Policy ↔ Vegas Strategy Reflection

This file provides two constructions:

1. **`reflectPolicy`**: Convert a MAID `Policy` back to a Vegas
   `ProgramBehavioralProfilePMF`. At each commit site of the program, the
   construction looks up the corresponding MAID decision node in the compile
   state and reads the policy at that node's information set.

2. **`compilePureProfile`**: Convert a Vegas `ProgramPureProfile` to a MAID
   `PurePolicy`. This is the pure-strategy analogue of the existing
   `compiledPolicy ∘ pureProfileOperational` path, but constructed directly
   on the pure level.

Both constructions come with semantic correctness theorems connecting
them to the existing bridges.
-/

namespace Vegas

open MAID

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## Policy reflection: MAID → Vegas PMF behavioral -/

/-- Reflect a MAID behavioral policy back to a Vegas PMF behavioral profile.

At each commit site `(x, who, Γ, b)` in program `p`:
- Look up the corresponding MAID decision node in the compile state `st`
- Read the MAID policy at that node's information set
- Convert the Vegas `ViewEnv` to the MAID infoset configuration
- Apply the policy to get the PMF over values -/
private noncomputable def reflectPolicyAux
    (B : MAIDBackend P L) :
    {Γ : VCtx P L} →
    (p : VegasCore P L Γ) →
    (hl : Legal p) → (hd : NormalizedDists p) →
    (ρ : RawNodeEnv L → VEnv (Player := P) L Γ) →
    (st₀ : MAIDCompileState P L B) →
    MAID.Policy (fp := B.fintypePlayer)
      (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct →
    ProgramBehavioralProfilePMF p
  | _, .ret _, _, _, _, _, _ => fun _ => PUnit.unit
  | _, .letExpr (b := b) x e k, hl, hd, ρ, st, pol =>
      reflectPolicyAux B k hl hd _ _ pol
  | _, .sample x τ m D' k, hl, hd, ρ, st, pol =>
      reflectPolicyAux B k hl hd.2 _ _ pol
  | Γ, .commit (b := b) x who R k, hl, hd, ρ, st, pol =>
      -- At this commit site, node id = st.nextId is a decision for `who`.
      -- The kernel reads the MAID policy at that node.
      letI := B.fintypePlayer
      let st_final := MAIDCompileState.ofProg B (.commit x who R k) hl hd ρ st
      let id := st.nextId
      let hid_lt : id < st_final.nextId :=
        Nat.lt_of_lt_of_le (by simp [MAIDCompileState.addNode, MAIDCompileState.addVar]; omega)
          (MAIDCompileState.ofProg_nextId_le B k hl.2 hd _ _)
      let kernel : ProgramBehavioralKernelPMF who Γ b :=
        { run := by
            intro view
            -- The decision node for this commit is at index st.nextId in st_final
            -- Node at id is a decision for who (from addNode_descAt_new + ofProg_descAt_old)
            -- Derive descAt for the decision node at st.nextId
            let nd : CompiledNode P L B :=
              .decision b who (allValues B b) (allValues_ne_nil B b)
                (allValues_nodup B b) (st.viewDeps who Γ)
            have hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st.nextId := by
              intro d hd'
              have : d ∈ st.viewDeps who Γ := by
                rcases Finset.mem_union.mp hd' with h | h <;>
                  simpa [CompiledNode.parents, CompiledNode.obsParents, nd] using h
              exact st.depsOfVars_lt _ d (by simpa [MAIDCompileState.viewDeps] using this)
            have hst1_lt : st.nextId < ((st.addNode nd hndeps).2.addVar x (.hidden who b)
                {st.nextId} (fun d hd₁ => by
                  simp only [Finset.mem_singleton] at hd₁; subst hd₁
                  exact Nat.lt_succ_self _)).nextId := by
              simp [MAIDCompileState.addVar, MAIDCompileState.addNode]
            have hdesc : st_final.descAt ⟨id, hid_lt⟩ = nd := by
              let ρ' (raw : RawNodeEnv L) : VEnv (Player := P) L ((x, .hidden who b) :: Γ) :=
                VEnv.cons (MAIDCompileState.readVal (B := B) raw b st.nextId) (ρ raw)
              let st₁ := (st.addNode nd hndeps).2.addVar x (.hidden who b) {st.nextId}
                (fun d hd₁ => by
                  simp only [Finset.mem_singleton] at hd₁
                  subst hd₁
                  exact Nat.lt_succ_self _)
              change (MAIDCompileState.ofProg B k hl.2 hd ρ' st₁).descAt ⟨st.nextId, _⟩ = nd
              rw [MAIDCompileState.ofProg_descAt_old B k hl.2 hd ρ' st₁ st.nextId hst1_lt]
              simp only [st₁, MAIDCompileState.addVar]
              exact st.addNode_descAt_new nd hndeps
            have hkind : st_final.toStruct.kind ⟨id, hid_lt⟩ =
                MAID.NodeKind.decision who := by
              simp only [toStruct_kind, hdesc, nd, CompiledNode.kind]
            have hval : st_final.toStruct.Val ⟨id, hid_lt⟩ = L.Val b := by
              change CompiledNode.valType (st_final.descAt ⟨id, hid_lt⟩) = L.Val b
              rw [hdesc]; rfl
            let obs := st_final.toStruct.obsParents ⟨id, hid_lt⟩
            let forwardMap (cfg : MAID.Cfg (fp := B.fintypePlayer) st_final.toStruct obs) :=
              projectViewEnv who (VEnv.eraseEnv (ρ (st_final.rawEnvOfCfg cfg)))
            by_cases h : ∃ cfg, forwardMap cfg = view
            · exact hval ▸ (pol who ⟨⟨⟨id, hid_lt⟩, hkind⟩, Classical.choose h⟩)
            · exact PMF.pure (MAIDValuation.defaultVal L B.toMAIDValuation b) }
      fun i => by
        by_cases h : who = i
        · subst h
          simpa [ProgramBehavioralStrategyPMF] using
            (kernel, reflectPolicyAux B k hl.2 hd _ _ pol who)
        · simpa [ProgramBehavioralStrategyPMF, h] using
            reflectPolicyAux B k hl.2 hd _ _ pol i
  | _, .reveal (b := b) y who x hx k, hl, hd, ρ, st, pol =>
      reflectPolicyAux B k hl hd _ _ pol

noncomputable def reflectPolicy
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (env : VEnv L Γ) :
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    MAID.Policy (fp := B.fintypePlayer) st.toStruct →
    ProgramBehavioralProfilePMF p :=
  reflectPolicyAux B p hl hd (fun _ => env) .empty

/-! ### PMF-level native outcome distribution -/

/-- PMF-level native outcome distribution: like `nativeOutcomeDist` (FDist) but
uses PMF throughout. At sample sites, the FDist from nature is converted to PMF
via `NormalizedDists`. At commit sites, the PMF behavioral kernel is applied. -/
private noncomputable def nativeOutcomeDistPMF
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (hd : NormalizedDists p)
    (σ : ProgramBehavioralProfilePMF p) :
    (ρ : RawNodeEnv L → VEnv L Γ) →
    (nextId : Nat) →
    RawNodeEnv L → PMF (Outcome P) :=
  match p, hd, σ with
  | .ret u, _, _ => fun ρ _ raw =>
      PMF.pure (evalPayoffs u (ρ raw))
  | .letExpr (b := b) x e k, hd, σ => fun ρ nextId raw =>
      nativeOutcomeDistPMF B k hd σ
        (fun raw => VEnv.cons (L := L) (x := x) (τ := .pub b)
          (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw))
        nextId raw
  | .sample x τ _m D' k, hd, σ => fun ρ nextId raw =>
      ((L.evalDist D' (VEnv.eraseDistEnv τ _ (ρ raw))).toPMF (hd.1 _)).bind
        (fun v =>
          nativeOutcomeDistPMF B k hd.2 σ
            (fun raw => VEnv.cons (L := L) (x := x) (τ := τ)
              (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw))
            (nextId + 1) (raw.extend nextId ⟨τ.base, v⟩))
  | .commit (b := b) x who _ k, hd, σ => fun ρ nextId raw =>
      let κ := ProgramBehavioralStrategyPMF.headKernel (P := P) (L := L) (σ who)
      (κ (projectViewEnv who (VEnv.eraseEnv (ρ raw)))).bind
        (fun v =>
          nativeOutcomeDistPMF B k hd
            (ProgramBehavioralProfilePMF.tail (P := P) (L := L) σ)
            (fun raw => VEnv.cons (L := L) (x := x) (τ := .hidden who b)
              (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw))
            (nextId + 1) (raw.extend nextId ⟨b, v⟩))
  | .reveal (b := b) y _who _x hx k, hd, σ => fun ρ nextId raw =>
      nativeOutcomeDistPMF B k hd σ
        (fun raw =>
          let v : L.Val b := VEnv.get (L := L) (ρ raw) hx
          VEnv.cons (L := L) (x := y) (τ := .pub b) v (ρ raw))
        nextId raw

/-- `nativeOutcomeDistPMF` equals `outcomeDistBehavioralPMF` when ρ is
insensitive to all node ids ≥ nextId. -/
private theorem nativeOutcomeDistPMF_eq
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (hd : NormalizedDists p)
    (σ : ProgramBehavioralProfilePMF p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (nextId : Nat)
    (hρ : ∀ nid, nextId ≤ nid → InsensitiveTo ρ nid) :
    ∀ raw : RawNodeEnv L,
    nativeOutcomeDistPMF B p hd σ ρ nextId raw =
      outcomeDistBehavioralPMF p hd σ (ρ raw) := by
  induction p generalizing nextId with
  | ret u =>
    intro raw; simp only [nativeOutcomeDistPMF, outcomeDistBehavioralPMF]
  | letExpr x e k ih =>
    intro raw; simp only [nativeOutcomeDistPMF, outcomeDistBehavioralPMF]
    exact ih hd σ _ nextId
      (fun nid hn raw tv => VEnv.cons_ext
        (congrArg (L.eval e) (congrArg VEnv.erasePubEnv (hρ nid hn raw tv)))
        (hρ nid hn raw tv))
      raw
  | sample x τ m D' k ih =>
    intro raw; simp only [nativeOutcomeDistPMF, outcomeDistBehavioralPMF]
    congr 1; funext v
    have hρ' : ∀ nid', nextId + 1 ≤ nid' → InsensitiveTo
        (fun raw => VEnv.cons (L := L) (x := x) (τ := τ)
          (MAIDCompileState.readVal (B := B) raw τ.base nextId) (ρ raw)) nid' := by
      intro nid' hn' raw tv
      exact VEnv.cons_ext
        (readVal_extend_ne raw nid' nextId tv τ.base (by omega))
        (hρ nid' (by omega) raw tv)
    rw [ih hd.2 σ _ (nextId + 1) hρ']
    congr 1
    exact VEnv.cons_ext (readVal_extend_self (B := B) raw nextId τ.base v)
      (hρ nextId (le_refl _) raw ⟨τ.base, v⟩)
  | @commit _ x who b R k ih =>
    intro raw; simp only [nativeOutcomeDistPMF, outcomeDistBehavioralPMF]
    congr 1; funext v
    have hρ' : ∀ nid', nextId + 1 ≤ nid' → InsensitiveTo
        (fun raw => VEnv.cons (L := L) (x := x) (τ := .hidden who b)
          (MAIDCompileState.readVal (B := B) raw b nextId) (ρ raw)) nid' := by
      intro nid' hn' raw tv
      exact VEnv.cons_ext
        (readVal_extend_ne raw nid' nextId tv b (by omega))
        (hρ nid' (by omega) raw tv)
    rw [ih hd (ProgramBehavioralProfilePMF.tail (P := P) (L := L) σ) _ (nextId + 1) hρ']
    congr 1
    exact VEnv.cons_ext (readVal_extend_self (B := B) raw nextId b v)
      (hρ nextId (le_refl _) raw ⟨b, v⟩)
  | reveal y who x hx k ih =>
    intro raw; simp only [nativeOutcomeDistPMF, outcomeDistBehavioralPMF]
    exact ih hd σ _ nextId
      (fun nid hn raw tv =>
        VEnv.cons_ext (τ := .pub _)
          (congrArg (VEnv.get (L := L) · hx) (hρ nid hn raw tv))
          (hρ nid hn raw tv))
      raw

/-- **PMF fold bridge**: the MAID evaluation folded through `evalStep` and
mapped through outcome extraction equals `nativeOutcomeDistPMF` applied
to the reflected policy.

This is the hard half of the reflectPolicy correctness proof. It requires:
- At chance nodes: the compiled sem matches the sample distribution
- At decision nodes: obs-config injectivity ensures the reflected kernel
  (using Classical.choose) matches the MAID policy
- At utility nodes: extract is invariant under utility-node updates

The proof is by structural induction on `p`, mirroring
`foldFDist_map_extract_eq_nativeOutcomeDist` at the PMF level. -/
private theorem foldl_evalStep_bind_left [Fintype P] {n : Nat}
    {S : MAID.Struct P n} (sem : MAID.Sem S) (pol : MAID.Policy S)
    (nodes : List (Fin n)) {β : Type} (μ : PMF β) (g : β → PMF (MAID.TAssign S)) :
    List.foldl (MAID.evalStep S sem pol) (μ.bind g) nodes =
      μ.bind (fun v => List.foldl (MAID.evalStep S sem pol) (g v) nodes) := by
  induction nodes generalizing g with
  | nil => simp
  | cons nd rest ih =>
    simp only [List.foldl_cons, MAID.evalStep]
    rw [show (μ.bind g).bind (fun a =>
          (MAID.nodeDist S sem pol nd a).bind (fun v =>
            PMF.pure (MAID.updateAssign a nd v))) =
        μ.bind (fun v => (g v).bind (fun a =>
          (MAID.nodeDist S sem pol nd a).bind (fun v' =>
            PMF.pure (MAID.updateAssign a nd v')))) from PMF.bind_bind _ _ _]
    exact ih _

/-- Cast cancellation for nodeDist at compiled nodes: if `descAt nd = c`, then
casting a `PMF (valType c)` to `PMF (valType (descAt nd))` and binding with
`f ∘ castValType` gives the same result as binding without casts. -/
private theorem pmf_descAt_cast_bind_cancel
    {st : MAIDCompileState P L B} {nd : Fin st.nextId}
    {c : CompiledNode P L B} (hdesc : st.descAt nd = c)
    (d : PMF (CompiledNode.valType c))
    {γ : Type} (f : CompiledNode.valType c → PMF γ)
    (hcast : PMF (CompiledNode.valType c) =
      PMF (CompiledNode.valType (st.descAt nd))) :
    (cast hcast d).bind (fun v => f (castValType hdesc v)) = d.bind f := by
  subst hdesc; rfl

/-- Raw-level view determinacy: if two raw environments agree outside viewDeps
(and outside [0, nextId)), and their views through ρ agree, then they agree
on viewDeps. This is the injectivity condition needed for the commit case,
formulated over raw environments to avoid cfg-casting between compile states. -/
private def ViewDeterminesRaw (st : MAIDCompileState P L B)
    (Γ : VCtx P L) (ρ : RawNodeEnv L → VEnv L Γ) : Prop :=
  ∀ (who : P) (raw₁ raw₂ : RawNodeEnv L),
    (∀ i, st.nextId ≤ i → raw₁ i = raw₂ i) →
    (∀ i, i ∉ st.viewDeps who Γ → i < st.nextId → raw₁ i = raw₂ i) →
    projectViewEnv (P := P) (L := L) who
      (VEnv.eraseEnv (ρ raw₁)) =
    projectViewEnv (P := P) (L := L) who
      (VEnv.eraseEnv (ρ raw₂)) →
    ∀ i, i ∈ st.viewDeps who Γ → raw₁ i = raw₂ i

private theorem pmfFoldBridge
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (hfresh : FreshBindings p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState P L B)
    (hvars : st₀.VarsSubCtx Γ)
    (hρ_deps : ∀ j, j ∉ (st₀.ctxDeps Γ : Finset Nat) → InsensitiveTo ρ j)
    (hρ_var : EnvRespectsLookupDeps st₀ ρ)
    (hρ_readers : ViewDeterminesRaw st₀ Γ ρ)
    (hnodup : (Γ.map Prod.fst).Nodup) :
    letI := B.fintypePlayer
    let st := MAIDCompileState.ofProg B p hl hd ρ st₀
    let S := st.toStruct
    let sem := MAIDCompileState.toSem st
    let extract : MAID.TAssign (fp := B.fintypePlayer) S → Outcome P :=
      fun a => extractOutcome B p ρ st₀.nextId (rawOfTAssign st a)
    ∀ (pol : MAID.Policy (fp := B.fintypePlayer) S)
      (a₀ : MAID.TAssign (fp := B.fintypePlayer) S),
      PMF.map extract
        ((List.finRange st.nextId).drop st₀.nextId |>.foldl
          (MAID.evalStep S sem pol) (PMF.pure a₀)) =
      nativeOutcomeDistPMF B p hd
        (reflectPolicyAux B p hl hd ρ st₀ pol)
        ρ st₀.nextId (rawOfTAssign st a₀) := by
  letI := B.fintypePlayer
  dsimp only
  induction p generalizing st₀ with
  | ret u =>
    rename_i Γ'
    intro pol a₀
    let st := MAIDCompileState.ofProg B (.ret u) hl hd ρ st₀
    let extract := fun a => extractOutcome B (.ret u) ρ st₀.nextId (rawOfTAssign st a)
    -- All new nodes are utility; evalStep at utility preserves PMF.map extract
    have hutility : ∀ nd ∈ (List.finRange st.nextId).drop st₀.nextId,
        ∃ who, (st.descAt nd).kind = .utility who :=
      fun nd hnd => by
        have hge : st₀.nextId ≤ nd.val := by
          rcases List.mem_iff_getElem.mp hnd with ⟨i, hi, hget⟩
          have := congrArg Fin.val hget; rw [List.getElem_drop] at this; simp at this; omega
        exact MAIDCompileState.addUtilityNodes_all_utility
          (st := st₀) (deps := st₀.ctxDeps Γ') (hdeps := st₀.depsOfVars_lt _)
          (ufn := fun who raw => ((evalPayoffs u (ρ raw)) who : ℝ))
          (players := Finset.univ.toList) (i := nd) hge
    have hstep : ∀ (nd : Fin st.nextId)
        (hwho : ∃ who, (st.descAt nd).kind = .utility who) (acc : PMF (MAID.TAssign st.toStruct)),
        PMF.map extract (MAID.evalStep st.toStruct (MAIDCompileState.toSem st) pol acc nd) =
        PMF.map extract acc := by
      intro nd hwho acc
      simp only [MAID.evalStep, PMF.map_bind]
      congr 1; funext a
      obtain ⟨w, hw⟩ := hwho
      have hkind : st.toStruct.kind nd = .utility w := by
        simp only [toStruct_kind]; exact hw
      conv_lhs => rw [show (fun a_1 => PMF.map extract (PMF.pure (MAID.updateAssign a nd a_1))) =
        (fun a_1 => PMF.pure (extract (MAID.updateAssign a nd a_1))) from
        funext fun v => PMF.pure_map extract (MAID.updateAssign a nd v)]
      simp only [MAID.nodeDist]
      split
      · -- chance: contradicts hkind
        rename_i hk; simp only [toStruct_kind] at hk; rw [hk] at hw; exact absurd hw (by simp)
      · -- decision: contradicts hkind
        rename_i p hk; simp only [toStruct_kind] at hk; rw [hk] at hw; exact absurd hw (by simp)
      · -- utility: PMF.pure default
        simp only [PMF.pure_bind, Function.comp]
        exact congrArg PMF.pure (congrArg (extractOutcome B (.ret u) ρ st₀.nextId)
          (rawOfTAssign_updateAssign_utility st a nd _ ⟨w, hw⟩))
    have hfold : ∀ (nodes : List (Fin st.nextId))
        (hnodes : ∀ nd ∈ nodes, ∃ who, (st.descAt nd).kind = .utility who)
        (acc : PMF (MAID.TAssign st.toStruct)),
        PMF.map extract (List.foldl (MAID.evalStep st.toStruct
          (MAIDCompileState.toSem st) pol) acc nodes) =
        PMF.map extract acc := by
      intro nodes hnodes acc
      induction nodes generalizing acc with
      | nil => rfl
      | cons nd rest ih_nodes =>
        simp only [List.foldl_cons]
        rw [ih_nodes (fun nd' hnd' => hnodes nd' (List.mem_cons.mpr (.inr hnd')))
          (MAID.evalStep st.toStruct (MAIDCompileState.toSem st) pol acc nd)]
        exact hstep nd (hnodes nd (List.mem_cons.mpr (.inl rfl))) acc
    rw [hfold _ hutility, PMF.pure_map]
    simp [extract, extractOutcome, nativeOutcomeDistPMF]; rfl
  | letExpr x e k ih =>
    rename_i Γ' b
    intro pol a₀
    have hxΓ : Fresh x Γ' := hfresh.1
    have hxvars : x ∉ st₀.vars.map Prod.fst := fun hxmem => hxΓ (hvars x hxmem)
    let ρ' : RawNodeEnv L → VEnv L ((x, .pub b) :: Γ') :=
      fun raw => VEnv.cons (L := L) (x := x) (τ := .pub b)
        (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw)
    let st₁ := st₀.addVar x (.pub b) (st₀.pubCtxDeps Γ') (st₀.depsOfVars_lt _)
    have hρ'_deps : ∀ j, j ∉ st₁.ctxDeps ((x, .pub b) :: Γ') → InsensitiveTo ρ' j := by
      intro j hj raw tv
      rw [st₀.ctxDeps_letExpr_step x hxΓ hxvars] at hj
      have hρj := hρ_deps j hj raw tv
      simp only [ρ', hρj]
    have hρ'_var : EnvRespectsLookupDeps st₁ ρ' := by
      intro y τ hy j hj raw tv
      cases hy with
      | here =>
          have hj' : j ∉ st₀.pubCtxDeps Γ' := by
            simpa [st₁, st₀.lookupDeps_addVar_eq_self_of_fresh x (.pub b)
              (st₀.pubCtxDeps Γ') (st₀.depsOfVars_lt _) hxvars] using hj
          exact Vegas.eval_pubExpr_insensitive_of_pubCtxDeps st₀ ρ hρ_var e j hj' raw tv
      | there hy' =>
          have hxy : y ≠ x := fun hEq => hxΓ (hEq.symm ▸ hy'.mem_map_fst)
          have hj' : j ∉ st₀.lookupDeps y := by
            simpa [st₁, st₀.lookupDeps_addVar_eq_of_ne x (.pub b)
              (st₀.pubCtxDeps Γ') (st₀.depsOfVars_lt _) hxy] using hj
          simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hy' j hj' raw tv
    have hρ'_readers : ViewDeterminesRaw st₁ ((x, .pub b) :: Γ') ρ' := by
      intro who raw₁ raw₂ hout hnot_vd hview i hi
      have hview_old := Vegas.projectViewEnv_cons_eq
        (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩) hview
      -- viewDeps: st₁.viewDeps who ((x,.pub b)::Γ') = st₀.viewDeps who Γ'
      -- (no new nodes, pubCtxDeps ⊆ viewDeps; proven before)
      -- Apply hρ_readers with same raws + viewDeps equality
      apply hρ_readers who raw₁ raw₂
      · -- hout: st₀.nextId = st₁.nextId (addVar preserves nextId)
        intro j hj; exact hout j (by
          simp [st₁, MAIDCompileState.addVar] at hj ⊢; exact hj)
      · -- hnot_vd: viewDeps same
        intro j hj hjlt
        apply hnot_vd j _ (by simp [st₁, MAIDCompileState.addVar]; exact hjlt)
        -- viewDeps: st₁.viewDeps who Γ₁ = st₀.viewDeps who Γ'
        have hVD : st₁.viewDeps who ((x, .pub b) :: Γ') = st₀.viewDeps who Γ' := by
          unfold MAIDCompileState.viewDeps
          simp only [viewVCtx, canSee, ite_true, List.map_cons, MAIDCompileState.depsOfVars]
          rw [st₀.lookupDeps_addVar_eq_self_of_fresh x (.pub b) (st₀.pubCtxDeps Γ')
              (st₀.depsOfVars_lt _) hxvars,
            st₀.depsOfVars_addVar_eq_of_not_mem x (.pub b) _ _ _
              (fun hmem => hxΓ (viewVCtx_map_fst_sub hmem))]
          exact Finset.union_eq_right.mpr (st₀.depsOfVars_subset_of_subset _ _
            erasePubVCtx_map_fst_sub_viewVCtx)
        rw [hVD] at hi; exact fun hmem => hj (hVD ▸ hmem)
      · exact hview_old
      · -- i ∈ st₀.viewDeps from i ∈ st₁.viewDeps
        have hVD : st₁.viewDeps who ((x, .pub b) :: Γ') = st₀.viewDeps who Γ' := by
          unfold MAIDCompileState.viewDeps
          simp only [viewVCtx, canSee, ite_true, List.map_cons, MAIDCompileState.depsOfVars]
          rw [st₀.lookupDeps_addVar_eq_self_of_fresh x (.pub b) (st₀.pubCtxDeps Γ')
              (st₀.depsOfVars_lt _) hxvars,
            st₀.depsOfVars_addVar_eq_of_not_mem x (.pub b) _ _ _
              (fun hmem => hxΓ (viewVCtx_map_fst_sub hmem))]
          exact Finset.union_eq_right.mpr (st₀.depsOfVars_subset_of_subset _ _
            erasePubVCtx_map_fst_sub_viewVCtx)
        rwa [hVD] at hi
    exact ih hl hd hfresh.2 ρ' st₁
      (st₀.VarsSubCtx_letExpr_step hvars x hxΓ) hρ'_deps hρ'_var hρ'_readers
      (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩) pol a₀
  | sample x τ m D' k ih =>
    rename_i Γ'
    intro pol a₀
    have hxΓ : Fresh x Γ' := hfresh.1
    have hxvars : x ∉ st₀.vars.map Prod.fst := fun hxmem => hxΓ (hvars x hxmem)
    let deps := st₀.ctxDeps Γ'
    let id := st₀.nextId
    let cpdFDist : RawNodeEnv L → FDist (L.Val τ.base) := fun raw =>
      L.evalDist D' (VEnv.eraseDistEnv τ m (ρ raw))
    let cpdNorm : ∀ raw, FDist.totalWeight (cpdFDist raw) = 1 := fun raw => hd.1 _
    let nd : CompiledNode P L B := .chance τ.base deps cpdFDist cpdNorm
    have hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st₀.nextId := by
      intro d hd'
      have hd'' : d ∈ deps := by
        simpa [CompiledNode.parents, CompiledNode.obsParents] using hd'
      exact st₀.depsOfVars_lt _ d hd''
    let stNode := (st₀.addNode nd hndeps).2
    let st₁ := stNode.addVar x τ ({id}) (by
      intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
      exact Nat.lt_succ_self id)
    let ρ' : RawNodeEnv L → VEnv L ((x, τ) :: Γ') :=
      fun raw => VEnv.cons (MAIDCompileState.readVal (B := B) raw τ.base id) (ρ raw)
    have hvars₁ : st₁.VarsSubCtx ((x, τ) :: Γ') := by
      simpa [st₁, stNode, nd, deps, id] using
        st₀.VarsSubCtx_addNode_addVar_singleton_step hvars nd hndeps x τ hxΓ
    have hctx₁ : st₁.ctxDeps ((x, τ) :: Γ') = {id} ∪ st₀.ctxDeps Γ' := by
      simpa [st₁, stNode, nd, deps, id] using
        st₀.ctxDeps_addNode_addVar_singleton_cons_eq_of_fresh nd hndeps x τ hxΓ hxvars
    have hρ'_deps : ∀ j, j ∉ st₁.ctxDeps ((x, τ) :: Γ') → InsensitiveTo ρ' j := by
      intro j hj raw tv
      have hjid : j ≠ id := by intro hEq; apply hj; simp [hctx₁, hEq]
      have hj' : j ∉ st₀.ctxDeps Γ' := by intro hmem; apply hj; simp [hctx₁, hmem]
      have hρj := hρ_deps j hj' raw tv
      exact VEnv.cons_ext (readVal_extend_ne raw j id tv τ.base hjid.symm) hρj
    have hρ'_var : EnvRespectsLookupDeps st₁ ρ' := by
      intro y σ hy j hj raw tv
      cases hy with
      | here =>
          have hlookup : st₁.lookupDeps x = ({id} : Finset Nat) := by
            simpa [st₁] using stNode.lookupDeps_addVar_eq_self_of_fresh x τ {id}
              (by intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
                  exact Nat.lt_succ_self id)
              (by simpa [stNode, MAIDCompileState.addNode] using hxvars)
          have hjid : j ≠ id := by
            simpa [Finset.mem_singleton] using (show j ∉ ({id} : Finset Nat) by
              simpa [hlookup] using hj)
          simpa [ρ', VEnv.get, readVal_extend_ne, hjid] using
            (readVal_extend_ne (B := B) raw j id tv τ.base hjid.symm)
      | there hy' =>
          have hxy : y ≠ x := fun hEq => hxΓ (hEq.symm ▸ hy'.mem_map_fst)
          have hlookupVar : st₁.lookupDeps y = stNode.lookupDeps y := by
            simpa [st₁] using stNode.lookupDeps_addVar_eq_of_ne x τ {id}
              (by intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
                  exact Nat.lt_succ_self id) hxy
          have hlookupNode : stNode.lookupDeps y = st₀.lookupDeps y := by
            simpa [stNode] using st₀.lookupDeps_addNode nd hndeps y
          have hj' : j ∉ st₀.lookupDeps y := by simpa [hlookupVar, hlookupNode] using hj
          simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hy' j hj' raw tv
    let st := MAIDCompileState.ofProg B k hl hd.2 ρ' st₁
    have hid_lt : id < st.nextId :=
      Nat.lt_of_lt_of_le (by
        simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode])
        (MAIDCompileState.ofProg_nextId_le B k hl hd.2 ρ' st₁)
    let nd0 : Fin st.nextId := ⟨id, hid_lt⟩
    have hdrop :
        (List.finRange st.nextId).drop id =
          nd0 :: (List.finRange st.nextId).drop st₁.nextId := by
      have hlen : id < (List.finRange st.nextId).length := by simpa using hid_lt
      rw [show st₁.nextId = id + 1 by
        simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode]]
      rw [← List.cons_getElem_drop_succ (l := List.finRange st.nextId) (n := id) (h := hlen)]
      simp [nd0]
    have hdesc0 : st.descAt nd0 = nd := by
      have hdesc1 := MAIDCompileState.ofProg_descAt_old B k hl hd.2 ρ' st₁ id
        (by simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode])
      rw [hdesc1]
      simpa [st₁, stNode] using st₀.addNode_descAt_new nd hndeps
    have hρeq :
        ρ (st.rawEnvOfCfg (MAID.projCfg a₀ (st.toStruct.parents nd0))) =
          ρ (rawOfTAssign st a₀) := by
      have hrawP : st.rawEnvOfCfg (MAID.projCfg a₀ (st.toStruct.parents nd0)) =
          fun i => if i < st.nextId then
            if i ∈ deps then rawOfTAssign st a₀ i else none else none := by
        apply st.rawEnvOfCfg_proj_eq_select a₀ (st.toStruct.parents nd0) deps
        intro i hi
        simp only [st.mem_toStruct_parents_iff nd0 hi, hdesc0, nd, CompiledNode.parents]
      rw [hrawP]
      simpa [deps] using (eq_on_ctxDeps_rawOfTAssign (st := st) (deps := deps) hρ_deps a₀)
    -- Peel off the chance node from the fold
    -- The goal has ofProg B (sample ...) which = ofProg B k ρ' st₁ = st
    change PMF.map (fun a => extractOutcome B (.sample x τ m D' k) ρ st₀.nextId (rawOfTAssign st a))
      (List.foldl (MAID.evalStep st.toStruct st.toSem pol) (PMF.pure a₀)
        ((List.finRange st.nextId).drop id)) =
      nativeOutcomeDistPMF B (.sample x τ m D' k) hd
        (reflectPolicyAux B (.sample x τ m D' k) hl hd ρ st₀ pol) ρ
        id (rawOfTAssign st a₀)
    rw [hdrop, List.foldl_cons]
    simp only [nativeOutcomeDistPMF, reflectPolicyAux]
    -- evalStep at nd0: acc.bind (nodeDist.bind (pure ∘ updateAssign))
    simp only [MAID.evalStep, PMF.pure_bind]
    -- Distribute bind through fold using monad associativity, then map through bind
    rw [foldl_evalStep_bind_left, PMF.map_bind]
    have hst₁_id : st₁.nextId = id + 1 := by
      simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode]
    -- Apply IH to rewrite inner fold for each v
    have hinner : ∀ v, PMF.map (fun a => extractOutcome B (.sample x τ m D' k) ρ
          st₀.nextId (rawOfTAssign st a))
        (List.foldl (MAID.evalStep st.toStruct st.toSem pol)
          (PMF.pure (MAID.updateAssign a₀ nd0 v))
          ((List.finRange st.nextId).drop st₁.nextId)) =
        nativeOutcomeDistPMF B k hd.2 (reflectPolicyAux B k hl hd.2 ρ' st₁ pol)
          ρ' (id + 1) (rawOfTAssign st (MAID.updateAssign a₀ nd0 v)) := by
      intro v
      rw [← hst₁_id]
      have hρ'_readers : ViewDeterminesRaw st₁ ((x, τ) :: Γ') ρ' := by
        intro who raw₁ raw₂ hout hnot_vd hview i hi
        have hview_old := Vegas.projectViewEnv_cons_eq
          (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩) hview
        sorry
      exact ih hl hd.2 hfresh.2 ρ' st₁ hvars₁ hρ'_deps hρ'_var hρ'_readers
        (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩) pol _
    -- Rewrite inner fold using IH
    simp_rw [hinner]
    -- Cast rawOfTAssign update to extend
    have hraw : ∀ v, rawOfTAssign st (MAID.updateAssign a₀ nd0 v) =
        (rawOfTAssign st a₀).extend id ⟨τ.base, castValType hdesc0 v⟩ :=
      fun v => MAIDCompileState.rawOfTAssign_updateAssign_of_tagged st a₀ nd0
        v ⟨τ.base, castValType hdesc0 v⟩ (taggedOfVal_chance_cast hdesc0 v)
    simp_rw [hraw]
    -- Now LHS: (nodeDist ...).bind (fun v => F (castValType hdesc0 v))
    -- RHS: (cpdFDist (rawOfTAssign st a₀)).toPMF.bind F
    -- Unfold nodeDist and toSem to expose the CPD
    simp only [MAID.nodeDist]
    have hkind_chance : (st.descAt nd0).kind = .chance := by
      simp [hdesc0, nd, CompiledNode.kind]
    split
    · -- chance branch: the correct one
      simp only [MAIDCompileState.toSem]
      split
      · -- inner match: .chance
        rename_i hk τ₁ deps₁ cpd₁ norm₁ hdesc₁
        have hinj := hdesc₁.symm.trans hdesc0
        simp only [nd, CompiledNode.chance.injEq] at hinj
        have hτeq := hinj.1
        subst hτeq
        have hcpd : cpd₁ = cpdFDist := eq_of_heq hinj.2.2
        subst hcpd
        have hdeps := hinj.2.1
        subst hdeps
        have hnorm : norm₁ = cpdNorm := funext fun _ => Subsingleton.elim _ _
        subst hnorm
        -- Now hdesc₁ and hdesc0 are proofs of the same statement; replace
        rw [show hdesc₁ = hdesc0 from Subsingleton.elim _ _]
        -- Factor out castValType hdesc0 so the cancel lemma can match
        simp only [_root_.id, eq_mpr_eq_cast]
        let F : CompiledNode.valType nd → PMF (Outcome P) :=
          fun w => nativeOutcomeDistPMF B k hd.2
            (reflectPolicyAux B k hl hd.2 ρ' st₁ pol) ρ'
            (id + 1) ((rawOfTAssign st a₀).extend id ⟨τ.base, w⟩)
        change PMF.bind (cast _ ((cpdFDist (st.rawEnvOfCfg
          (MAID.projCfg a₀ (st.toStruct.parents nd0)))).toPMF _))
          (fun a => F (castValType hdesc0 a)) = _
        rw [pmf_descAt_cast_bind_cancel hdesc0]
        -- Now: (cpdFDist (rawEnvOfCfg ...)).toPMF.bind F = RHS.bind F'
        -- F and F' are the same (let bindings); distribution differs by hρeq
        change ((cpdFDist (st.rawEnvOfCfg
            (MAID.projCfg a₀ (st.toStruct.parents nd0)))).toPMF (cpdNorm _)).bind F =
          ((L.evalDist D' (VEnv.eraseDistEnv τ m (ρ (rawOfTAssign st a₀)))).toPMF _).bind F
        congr 1
        exact congrArg (fun env => FDist.toPMF (L.evalDist D' (VEnv.eraseDistEnv τ m env))
          (hd.1 env)) hρeq
      · -- inner match .decision: contradicts hdesc0
        rename_i hdesc₁
        rw [hdesc₁] at hkind_chance; simp [CompiledNode.kind] at hkind_chance
      · -- inner match .utility: contradicts hdesc0
        rename_i hdesc₁
        rw [hdesc₁] at hkind_chance; simp [CompiledNode.kind] at hkind_chance
    · -- decision branch: contradicts kind = .chance
      rename_i hk
      rw [toStruct_kind] at hk; rw [hkind_chance] at hk; exact absurd hk (by simp)
    · -- utility branch: contradicts kind = .chance
      rename_i hk
      rw [toStruct_kind] at hk; rw [hkind_chance] at hk; exact absurd hk (by simp)
  | commit x who R k ih =>
    rename_i Γ' b
    intro pol a₀
    have hxΓ : Fresh x Γ' := hfresh.1
    have hxvars : x ∉ st₀.vars.map Prod.fst := fun hxmem => hxΓ (hvars x hxmem)
    let obs := st₀.viewDeps who Γ'
    let acts := allValues B b
    let id := st₀.nextId
    let nd : CompiledNode P L B := .decision b who acts
      (allValues_ne_nil B b) (allValues_nodup B b) obs
    have hndeps : ∀ d ∈ nd.parents ∪ nd.obsParents, d < st₀.nextId := by
      intro d hd'; have hd'' : d ∈ obs := by
        simpa [nd, CompiledNode.parents, CompiledNode.obsParents] using hd'
      exact st₀.depsOfVars_lt _ d hd''
    let stNode := (st₀.addNode nd hndeps).2
    let st₁ := stNode.addVar x (.hidden who b) ({id}) (by
      intro d hd'; have := Finset.mem_singleton.mp hd'; subst d; exact Nat.lt_succ_self id)
    let ρ' : RawNodeEnv L → VEnv (Player := P) L ((x, .hidden who b) :: Γ') :=
      fun raw => VEnv.cons (τ := .hidden who b)
        (MAIDCompileState.readVal (B := B) raw b id) (ρ raw)
    have hvars₁ : st₁.VarsSubCtx ((x, .hidden who b) :: Γ') := by
      simpa [st₁, stNode, nd, obs, id] using
        st₀.VarsSubCtx_addNode_addVar_singleton_step hvars nd hndeps x (.hidden who b) hxΓ
    have hctx₁ : st₁.ctxDeps ((x, .hidden who b) :: Γ') = {id} ∪ st₀.ctxDeps Γ' := by
      simpa [st₁, stNode, nd, obs, id] using
        st₀.ctxDeps_addNode_addVar_singleton_cons_eq_of_fresh nd hndeps x (.hidden who b) hxΓ hxvars
    have hρ'_deps : ∀ j, j ∉ st₁.ctxDeps ((x, .hidden who b) :: Γ') → InsensitiveTo ρ' j := by
      intro j hj raw tv
      have hjid : j ≠ id := by intro hEq; apply hj; simp [hctx₁, hEq]
      have hj' : j ∉ st₀.ctxDeps Γ' := by intro hmem; apply hj; simp [hctx₁, hmem]
      have hρj := hρ_deps j hj' raw tv
      exact VEnv.cons_ext (readVal_extend_ne raw j id tv b hjid.symm) hρj
    have hρ'_var : EnvRespectsLookupDeps st₁ ρ' := by
      intro y σ hy j hj raw tv
      cases hy with
      | here =>
          have hlookup : st₁.lookupDeps x = ({id} : Finset Nat) := by
            simpa [st₁] using stNode.lookupDeps_addVar_eq_self_of_fresh x (.hidden who b) {id}
              (by intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
                  exact Nat.lt_succ_self id)
              (by simpa [stNode, MAIDCompileState.addNode] using hxvars)
          have hjid : j ≠ id := by
            simpa [Finset.mem_singleton] using (show j ∉ ({id} : Finset Nat) by
              simpa [hlookup] using hj)
          simpa [ρ', VEnv.get, readVal_extend_ne, hjid] using
            (readVal_extend_ne (B := B) raw j id tv b hjid.symm)
      | there hy' =>
          have hxy : y ≠ x := fun hEq => hxΓ (hEq.symm ▸ hy'.mem_map_fst)
          have hlookupVar : st₁.lookupDeps y = stNode.lookupDeps y := by
            simpa [st₁] using stNode.lookupDeps_addVar_eq_of_ne x (.hidden who b) {id}
              (by intro d hd'; have := Finset.mem_singleton.mp hd'; subst d
                  exact Nat.lt_succ_self id) hxy
          have hlookupNode : stNode.lookupDeps y = st₀.lookupDeps y := by
            simpa [stNode] using st₀.lookupDeps_addNode nd hndeps y
          have hj' : j ∉ st₀.lookupDeps y := by simpa [hlookupVar, hlookupNode] using hj
          simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hy' j hj' raw tv
    let st := MAIDCompileState.ofProg B k hl.2 hd ρ' st₁
    have hid_lt : id < st.nextId :=
      Nat.lt_of_lt_of_le (by
        simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode])
        (MAIDCompileState.ofProg_nextId_le B k hl.2 hd ρ' st₁)
    let nd0 : Fin st.nextId := ⟨id, hid_lt⟩
    have hdrop :
        (List.finRange st.nextId).drop id =
          nd0 :: (List.finRange st.nextId).drop st₁.nextId := by
      have hlen : id < (List.finRange st.nextId).length := by simpa using hid_lt
      rw [show st₁.nextId = id + 1 by
        simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode]]
      rw [← List.cons_getElem_drop_succ (l := List.finRange st.nextId) (n := id) (h := hlen)]
      simp [nd0]
    have hdesc0 : st.descAt nd0 = nd := by
      have hdesc1 := MAIDCompileState.ofProg_descAt_old B k hl.2 hd ρ' st₁ id
        (by simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode])
      rw [hdesc1]; simpa [st₁, stNode] using st₀.addNode_descAt_new nd hndeps
    -- View equivalence: rawEnvOfCfg at obsParents gives same view as rawOfTAssign
    have hViewEq :
        projectViewEnv (P := P) (L := L) who
          (VEnv.eraseEnv (ρ (st.rawEnvOfCfg
            (MAID.projCfg a₀ (st.toStruct.obsParents nd0))))) =
        projectViewEnv (P := P) (L := L) who
          (VEnv.eraseEnv (ρ (rawOfTAssign st a₀))) := by
      have hrawO : st.rawEnvOfCfg (MAID.projCfg a₀ (st.toStruct.obsParents nd0)) =
          fun i => if i < st.nextId then
            if i ∈ obs then rawOfTAssign st a₀ i else none else none := by
        apply st.rawEnvOfCfg_proj_eq_select a₀ (st.toStruct.obsParents nd0) obs
        intro i hi
        simp only [st.mem_toStruct_obsParents_iff nd0 hi, hdesc0, nd, CompiledNode.obsParents]
      rw [hrawO]
      simpa [obs] using
        (eq_on_ctxDeps_rawOfTAssign (st := st) (deps := obs)
          (f := fun raw => projectViewEnv who (VEnv.eraseEnv (ρ raw)))
          (fun j hj =>
            projectViewEnv_insensitive_of_viewDeps st₀ ρ hρ_var who j
              (by simpa [obs] using hj))
          a₀)
    -- Peel off the decision node from the fold
    change PMF.map (fun a => extractOutcome B (.commit x who R k) ρ st₀.nextId (rawOfTAssign st a))
      (List.foldl (MAID.evalStep st.toStruct st.toSem pol) (PMF.pure a₀)
        ((List.finRange st.nextId).drop id)) =
      nativeOutcomeDistPMF B (.commit x who R k) hd
        (reflectPolicyAux B (.commit x who R k) hl hd ρ st₀ pol) ρ
        id (rawOfTAssign st a₀)
    rw [hdrop, List.foldl_cons]
    simp only [nativeOutcomeDistPMF, reflectPolicyAux]
    simp only [MAID.evalStep, PMF.pure_bind]
    rw [foldl_evalStep_bind_left, PMF.map_bind]
    have hst₁_id : st₁.nextId = id + 1 := by
      simp [st₁, stNode, id, MAIDCompileState.addVar, MAIDCompileState.addNode]
    -- Apply IH to inner fold
    have hinner : ∀ v, PMF.map (fun a => extractOutcome B (.commit x who R k) ρ
          st₀.nextId (rawOfTAssign st a))
        (List.foldl (MAID.evalStep st.toStruct st.toSem pol)
          (PMF.pure (MAID.updateAssign a₀ nd0 v))
          ((List.finRange st.nextId).drop st₁.nextId)) =
        nativeOutcomeDistPMF B k hd (reflectPolicyAux B k hl.2 hd ρ' st₁ pol)
          ρ' (id + 1) (rawOfTAssign st (MAID.updateAssign a₀ nd0 v)) := by
      intro v; rw [← hst₁_id]
      have hρ'_readers : ViewDeterminesRaw st₁ ((x, BindTy.hidden who b) :: Γ') ρ' := by
        intro who' raw₁ raw₂ hout hnot_vd hview i hi
        have hview_old := Vegas.projectViewEnv_cons_eq
          (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩) hview
        sorry
      exact ih hl.2 hd hfresh.2 ρ' st₁ hvars₁ hρ'_deps hρ'_var hρ'_readers
        (List.nodup_cons.mpr ⟨hxΓ, hnodup⟩) pol _
    -- Use IH to rewrite inner fold
    simp_rw [hinner]
    -- Cast raw update to extend (same pattern as sample case)
    have hraw : ∀ v, rawOfTAssign st (MAID.updateAssign a₀ nd0 v) =
        (rawOfTAssign st a₀).extend id ⟨b, castValType hdesc0 v⟩ :=
      fun v => MAIDCompileState.rawOfTAssign_updateAssign_of_tagged st a₀ nd0
        v ⟨b, castValType hdesc0 v⟩ (taggedOfVal_decision_cast hdesc0 v)
    simp_rw [hraw]
    -- Unfold nodeDist at decision node
    simp only [MAID.nodeDist]
    have hkind_decision : (st.descAt nd0).kind = .decision who := by
      simp [hdesc0, nd, CompiledNode.kind]
    split
    · -- chance: contradiction
      rename_i hk; rw [toStruct_kind] at hk; rw [hkind_decision] at hk; exact absurd hk (by simp)
    · -- decision: the correct branch
      rename_i p hk
      -- nodeDist = pol p ⟨⟨nd0, hk⟩, projCfg a₀ (obsParents nd0)⟩
      -- Need: p = who (from hkind_decision and hk)
      have hp : p = who := by
        have := (toStruct_kind st nd0).symm.trans hk
        rw [hkind_decision] at this; exact (MAID.NodeKind.decision.inj this).symm
      subst hp
      -- Simplify: headKernel_mk extracts the kernel from reflectPolicyAux
      simp only [dif_pos trivial, nativeOutcomeDistPMF, reflectPolicyAux,
        ProgramBehavioralStrategyPMF.headKernel_mk]
      -- Resolve the ∃ cfg branch with the witness from hViewEq
      -- Split the kernel's if-then-else
      split_ifs with h_exists
      · -- Show Classical.choose h_exists = projCfg a₀ (obsParents nd0)
        -- via ViewDeterminesRaw → rawEnvOfCfg agreement → rawEnvOfCfg_injective
        have hcfg_eq : Classical.choose h_exists =
            MAID.projCfg a₀ (st.toStruct.obsParents nd0) := by
          -- Both cfgs produce the same ρ view (from h_exists + hViewEq)
          have hchoose_view := Classical.choose_spec h_exists
          -- Apply rawEnvOfCfg_injective: show raws agree at all indices
          apply st.rawEnvOfCfg_injective
          -- Show pointwise raw agreement
          let raw₁ := st.rawEnvOfCfg (Classical.choose h_exists)
          let raw₂ := st.rawEnvOfCfg (MAID.projCfg a₀ (st.toStruct.obsParents nd0))
          -- Both agree outside obsParents (both none) and outside [0, nextId)
          -- View equality: hchoose_view.trans hViewEq.symm
          have hview_eq : projectViewEnv (P := P) (L := L) p
              (VEnv.eraseEnv (ρ raw₁)) =
              projectViewEnv p (VEnv.eraseEnv (ρ raw₂)) := by
            exact hchoose_view.trans hViewEq.symm
          show raw₁ = raw₂
          funext j
          by_cases hj_lt : j < st.nextId
          · by_cases hj_mem : (⟨j, hj_lt⟩ : Fin st.nextId) ∈ st.toStruct.obsParents nd0
            · -- j ∈ obsParents: use hρ_readers
              have hj_obs : j ∈ obs := by
                rw [st.mem_toStruct_obsParents_iff nd0 hj_lt] at hj_mem
                simp [hdesc0, CompiledNode.obsParents] at hj_mem; exact hj_mem
              exact hρ_readers p raw₁ raw₂
                (fun i hi => by
                  show raw₁ i = raw₂ i
                  sorry)
                (fun i hi_not hi_lt => by sorry)
                hview_eq j hj_obs
            · -- j ∉ obsParents: both rawEnvOfCfg give none at j
              show raw₁ j = raw₂ j
              sorry
          · show raw₁ j = raw₂ j
            simp only [raw₁, raw₂, MAIDCompileState.rawEnvOfCfg, hj_lt, dite_false]
        -- With cfg equality, the pol values match. Cast cancel for the rest.
        sorry
      · exfalso; apply h_exists; exact ⟨_, hViewEq⟩
    · -- utility: contradiction
      rename_i hk; rw [toStruct_kind] at hk; rw [hkind_decision] at hk; exact absurd hk (by simp)
  | reveal y who' x hx k ih =>
    rename_i Γ' b
    intro pol a₀
    have hyΓ : Fresh y Γ' := hfresh.1
    have hyvars : y ∉ st₀.vars.map Prod.fst := fun hymem => hyΓ (hvars y hymem)
    let ρ' : RawNodeEnv L → VEnv L ((y, .pub b) :: Γ') :=
      fun raw =>
        let v : L.Val b := VEnv.get (L := L) (ρ raw) hx
        VEnv.cons (L := L) (x := y) (τ := .pub b) v (ρ raw)
    let st₁ := st₀.addVar y (.pub b) (st₀.lookupDeps x) (st₀.lookupDeps_lt x)
    have hvars₁ : st₁.VarsSubCtx ((y, .pub b) :: Γ') := by
      simpa [st₁] using st₀.VarsSubCtx_addVar hvars y _ _ _ hyΓ
    have hctx₁ : st₁.ctxDeps ((y, .pub b) :: Γ') = st₀.ctxDeps Γ' := by
      simpa [st₁] using st₀.ctxDeps_reveal_step y who' x hx hyΓ hyvars
    have hρ'_deps : ∀ j, j ∉ st₁.ctxDeps ((y, .pub b) :: Γ') → InsensitiveTo ρ' j := by
      intro j hj raw tv
      have hj' : j ∉ st₀.ctxDeps Γ' := by simpa [hctx₁] using hj
      have hρj := hρ_deps j hj' raw tv
      simp only [ρ', hρj]
    have hρ'_var : EnvRespectsLookupDeps st₁ ρ' := by
      intro z σ hz j hj raw tv
      cases hz with
      | here =>
          have hj' : j ∉ st₀.lookupDeps x := by
            simpa [st₁, st₀.lookupDeps_addVar_eq_self_of_fresh y (.pub b) (st₀.lookupDeps x)
              (st₀.lookupDeps_lt x) hyvars] using hj
          simpa [ρ', VEnv.get] using hρ_var hx j hj' raw tv
      | there hz' =>
          have hzy : z ≠ y := fun hEq => hyΓ (hEq.symm ▸ hz'.mem_map_fst)
          have hj' : j ∉ st₀.lookupDeps z := by
            simpa [st₁, st₀.lookupDeps_addVar_eq_of_ne y (.pub b) (st₀.lookupDeps x)
              (st₀.lookupDeps_lt x) hzy] using hj
          simpa [ρ', VEnv.get, VEnv.cons_get_there] using hρ_var hz' j hj' raw tv
    have hρ'_readers : ViewDeterminesRaw st₁ ((y, .pub b) :: Γ') ρ' := by
      intro who raw₁ raw₂ hout hnot_vd hview i hi
      have hview_old := Vegas.projectViewEnv_cons_eq
        (List.nodup_cons.mpr ⟨hyΓ, hnodup⟩) hview
      sorry
    exact ih hl hd hfresh.2 ρ' st₁ hvars₁ hρ'_deps hρ'_var hρ'_readers
      (List.nodup_cons.mpr ⟨hyΓ, hnodup⟩) pol a₀

/-- Semantic correctness of `reflectPolicy`: the PMF behavioral profile
obtained by reflecting a MAID policy produces the same outcome distribution
as the MAID's `evalAssignDist` mapped through outcome extraction. -/
theorem reflectPolicy_outcomeDistBehavioralPMF_eq
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (env : VEnv L Γ)
    (hl : Legal p)
    (hd : NormalizedDists p)
    (hwf : WF p)
    (hnodup_ctx : (Γ.map Prod.fst).Nodup) :
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    ∀ (pol : MAID.Policy (fp := B.fintypePlayer) st.toStruct),
      PMF.map (fun a => extractOutcome B p (fun _ => env) 0 (rawOfTAssign st a))
        (evalAssignDist (fp := B.fintypePlayer) st.toStruct
        (MAIDCompileState.toSem st) pol) =
        outcomeDistBehavioralPMF p hd (reflectPolicy B p hl hd env pol) env := by
  intro st pol
  letI := B.fintypePlayer
  -- Step 1: Rewrite evalAssignDist as evalFold along natural order
  let hnat := compiled_naturalOrder st
  let σ_topo := hnat.toTopologicalOrder
  rw [MAID.evalAssignDist_eq_evalFold _ _ _ σ_topo]
  -- Step 2: Apply the fold bridge
  have hbridge := pmfFoldBridge B p hl hd hwf.1
    (fun _ => env) .empty
    (fun _ h => by simp [MAIDCompileState.empty] at h)
    (fun j hj => by intro raw tv; rfl)
    (envRespectsLookupDeps_const (B := B) (st := .empty) env)
    (fun who raw₁ raw₂ _ _ _ i hi => by
      simp [MAIDCompileState.viewDeps, MAIDCompileState.empty, MAIDCompileState.depsOfVars] at hi
      exact absurd hi (by
        have := MAIDCompileState.depsOfVars_lt MAIDCompileState.empty
          ((viewVCtx who Γ).map Prod.fst) i hi
        simp [MAIDCompileState.empty] at this))
    hnodup_ctx pol (MAID.defaultAssign st.toStruct)
  -- Step 3: Connect to outcomeDistBehavioralPMF via nativeOutcomeDistPMF_eq
  have hnative := nativeOutcomeDistPMF_eq B p hd
    (reflectPolicyAux B p hl hd (fun _ => env) .empty pol)
    (fun _ => env) 0
    (fun nid _ raw tv => rfl)
  rw [show (MAIDCompileState.empty (B := B) (Player := P) (L := L)).nextId = 0 from rfl,
    List.drop_zero] at hbridge
  -- evalFold = foldl along the natural order
  have hfold : MAID.evalFold st.toStruct (MAIDCompileState.toSem st) pol σ_topo =
      (List.finRange st.nextId).foldl (MAID.evalStep st.toStruct (MAIDCompileState.toSem st) pol)
        (PMF.pure (MAID.defaultAssign st.toStruct)) := by
    rfl
  rw [hfold]
  -- Chain: foldl → nativeOutcomeDistPMF → outcomeDistBehavioralPMF
  exact hbridge.trans (hnative _)

/-! ## Pure strategy compilation: Vegas → MAID -/

/-- Auxiliary for `compilePureProfile`, threading compile state.
Mirrors `translateStrategy` but extracts pure values instead of PMFs. -/
private noncomputable def compilePureProfileAux
    (B : MAIDBackend P L) :
    {Γ : VCtx P L} →
    (p : VegasCore P L Γ) →
    (hl : Legal p) → (hd : NormalizedDists p) →
    (ρ : RawNodeEnv L → VEnv (Player := P) L Γ) →
    (st₀ : MAIDCompileState P L B) →
    ProgramPureProfile p →
    MAID.PurePolicy (fp := B.fintypePlayer)
      (MAIDCompileState.ofProg B p hl hd ρ st₀).toStruct
  | _, .ret _, _, _, _, _, _ => by
      letI := B.fintypePlayer; intro _p ⟨d, _⟩
      exact default
  | _, .letExpr (b := b) x e k, hl, hd, ρ, st, π =>
      compilePureProfileAux B k hl hd
        (fun raw => VEnv.cons (τ := .pub b) (L.eval e (VEnv.erasePubEnv (ρ raw))) (ρ raw))
        (st.addVar x (.pub b) (st.pubCtxDeps _) (st.depsOfVars_lt _)) π
  | _, .sample x τ m D' k, hl, hd, ρ, st, π =>
      compilePureProfileAux B k hl hd.2 _ _ π
  | Γ, .commit (b := b) x who R k, hl, hd, ρ, st, π => by
      letI := B.fintypePlayer
      let id := st.nextId
      let obs := st.viewDeps who Γ
      let acts := allValues B b
      let res := st.addNode
        (.decision b who acts (allValues_ne_nil B b) (allValues_nodup B b) obs) (by
        intro d hd'
        have := Finset.mem_union.mp hd'
        rcases this with h | h <;> simpa [CompiledNode.parents, CompiledNode.obsParents] using
          st.depsOfVars_lt _ d h)
      let st' := res.2
      let ρ' : RawNodeEnv L → VEnv (Player := P) L ((x, .hidden who b) :: Γ) :=
        fun raw => VEnv.cons (τ := .hidden who b)
          (MAIDCompileState.readVal (B := B) raw b id) (ρ raw)
      let st₁ := st'.addVar x (.hidden who b) ({id}) (by
        intro d hd₁; simp only [Finset.mem_singleton] at hd₁; subst hd₁; exact Nat.lt_succ_self _)
      let pol_rest := compilePureProfileAux B k hl.2 hd ρ' st₁
        (ProgramPureProfile.tail π)
      let κ := ProgramPureStrategy.headKernel (π who)
      intro p ⟨d, cfg⟩
      let st_final := MAIDCompileState.ofProg B k hl.2 hd ρ' st₁
      by_cases hd_eq : d.1.val = id
      · have hid_lt_st₁ : id < st₁.nextId := by
          simp [st₁, st', res, id, MAIDCompileState.addVar, MAIDCompileState.addNode]
        have hid_lt : id < st_final.nextId :=
          Nat.lt_of_lt_of_le hid_lt_st₁
            (MAIDCompileState.ofProg_nextId_le B k hl.2 hd ρ' st₁)
        have hdesc : st_final.descAt d.1 =
              .decision b who acts (allValues_ne_nil B b) (allValues_nodup B b) obs := by
          have hdesc0 : st₁.descAt ⟨id, hid_lt_st₁⟩ =
              .decision b who acts (allValues_ne_nil B b) (allValues_nodup B b) obs := by
            simp only [st₁, MAIDCompileState.addVar, st', res]
            exact st.addNode_descAt_new _ _
          have h := MAIDCompileState.ofProg_descAt_old B k hl.2 hd ρ' st₁ id hid_lt_st₁
          conv_lhs => rw [show d.1 = ⟨id, hid_lt⟩ from Fin.ext hd_eq]
          exact h.trans hdesc0
        change CompiledNode.valType (st_final.descAt d.1)
        rw [hdesc]; change L.Val b
        exact κ (projectViewEnv who
          (VEnv.eraseEnv (ρ (st_final.rawEnvOfCfg cfg))))
      · exact pol_rest p ⟨d, cfg⟩
  | _, .reveal (b := b) y who x hx k, hl, hd, ρ, st, π =>
      compilePureProfileAux B k hl hd _ _ π

/-- Compile a Vegas pure profile to a MAID pure policy. -/
noncomputable def compilePureProfile
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (hl : Legal p) (hd : NormalizedDists p)
    (env : VEnv L Γ)
    (π : ProgramPureProfile p) :
    let st := MAIDCompileState.ofProg B p hl hd (fun _ => env) .empty
    MAID.PurePolicy (fp := B.fintypePlayer) st.toStruct :=
  compilePureProfileAux B p hl hd (fun _ => env) .empty π

/-- Generalized: translateStrategy of toBehavioral = pureToPolicy of compilePureProfileAux -/
private theorem compilePureProfile_eq_pureToPolicy_aux
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (hl : Legal p) (hd : NormalizedDists p) (hfresh : FreshBindings p)
    (ρ : RawNodeEnv L → VEnv L Γ)
    (st₀ : MAIDCompileState P L B)
    (π : ProgramPureProfile p) :
    translateStrategy B p hl hd ρ st₀ (ProgramPureProfile.toBehavioral p π) =
      MAID.pureToPolicy (fp := B.fintypePlayer) (compilePureProfileAux B p hl hd ρ st₀ π) := by
  induction p generalizing st₀ with
  | ret => funext player ⟨d, cfg⟩
           simp [translateStrategy, compilePureProfileAux,
                 MAID.pureToPolicy, MAID.pureToPlayerStrategy]
  | letExpr _ _ k ih =>
    simp only [translateStrategy, compilePureProfileAux]
    exact ih hl hd hfresh.2 _ _ _
  | sample _ _ _ _ k ih => exact ih hl hd.2 hfresh.2 _ _ _
  | commit x who_c R k ih =>
    funext player ⟨d, cfg⟩
    simp only [translateStrategy, compilePureProfileAux,
      MAID.pureToPolicy, MAID.pureToPlayerStrategy]
    split
    · -- isTrue: toPMF_pure + cast commutation with PMF.pure
      simp only [toStruct_kind, toStruct_Val, id, ProgramBehavioralStrategy.headKernel,
        ProgramPureProfile.toBehavioral, ↓reduceDIte, ProgramBehavioralKernel.ofPure,
        ProgramPureStrategy.headKernel, eq_mp_eq_cast, eq_mpr_eq_cast, cast_cast, cast_eq,
        FDist.totalWeight_pure, FDist.toPMF_pure]
      have : ∀ (α β : Type) [DecidableEq α] [DecidableEq β] (h : α = β)
          (v : α), cast (congrArg PMF h) (PMF.pure v) = PMF.pure (cast h v) := by
        intro α β _ _ h v; subst h; rfl
      exact this _ _ _ _
    · -- isFalse: IH on continuation
      simpa [ProgramPureProfile.tail_toBehavioral, MAID.pureToPolicy,
        MAID.pureToPlayerStrategy] using
        congrFun (congrFun (ih hl.2 hd hfresh.2 _ _ _) player) ⟨d, cfg⟩
  | reveal _ _ _ _ k ih => exact ih hl hd hfresh.2 _ _ _

/-- The compiled pure policy, lifted to a behavioral MAID policy via
`pureToPolicy`, agrees with the `compiledPolicy` of the operationally
lifted pure profile. -/
theorem compilePureProfile_eq_pureToPolicy
    (B : MAIDBackend P L)
    {Γ : VCtx P L}
    (p : VegasCore P L Γ)
    (env : VEnv L Γ)
    (π : ProgramPureProfile p)
    (hl : Legal p)
    (hd : NormalizedDists p)
    (hfresh : FreshBindings p) :
    let β := ProgramPureProfile.toBehavioral p π
    compiledPolicy B p hl hd (fun _ => env) .empty β =
      MAID.pureToPolicy (fp := B.fintypePlayer) (compilePureProfile B p hl hd env π) := by
  intro β
  exact compilePureProfile_eq_pureToPolicy_aux B p hl hd hfresh (fun _ => env) .empty π

end Vegas
