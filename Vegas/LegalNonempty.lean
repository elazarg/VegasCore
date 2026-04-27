import Vegas.PureStrategic

/-!
# Nonempty instance for guard-legal pure profiles

Two constructors witnessing `Nonempty (LegalProgramPureProfile g)`:

* `instNonempty_of_trivialGuards` — for programs whose commit guards
  are constantly-true (matching-pennies, sequential-reveal, any
  program using `constBool true` guards).
* `instNonempty_of_wfctx` — for any `WFProgram` bundle whose initial
  context has distinct variable names (`WFCtx g.Γ`), discharging the
  `Nonempty` from `g.wf` and `g.legal` in the general
  `ViewScoped` case.

Both constructors additionally require the base-type nonemptiness
assumption `[∀ τ, Nonempty (L.Val τ)]`. The trivial-guard case does
not need `WFCtx`; the general case uses it for the `HasVar`-proof
uniqueness at the heart of the view-extension argument.

## The general chain

At each commit site with guard `R`, fix the committer's view. By
`ViewScoped` and `FreshBindings`, evaluation of `R` is invariant
under environments agreeing on the committer's visible variables
(Scope's `evalGuard_eq_of_obsEq`). Under `WFCtx Γ`, two environments
with the same `projectViewEnv` image coincide on every visible
variable (proved here as `obsEq_of_projectViewEnv_eq`, the converse
of `projectViewEnv_eq_of_obsEq`, using `HasVar.eq_of_nodup`).
`Legal` supplies a guard-satisfying action at every environment;
`Classical.choose` picks one per view. The resulting per-site
kernel is legal at every reachable environment by the uniformity
argument (`evalGuard_eq_of_projectViewEnv_eq`).

The recursive assembly `exists_legal_pureStrategy` threads `WFCtx`
through each binding: every non-return constructor extends the
context by a binding whose name is fresh by `FreshBindings`, which
via `WFCtx.cons` preserves `WFCtx`.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A default pure strategy for player `who` on program `p`: at every
commit site, select an arbitrary action via `Nonempty`. Legality is
not automatic — see `defaultPureStrategy_IsLegal` for the condition
under which the default is guaranteed legal. -/
noncomputable def defaultPureStrategy
    [∀ τ : L.Ty, Nonempty (L.Val τ)] (who : P) :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
    ProgramPureStrategy (P := P) (L := L) who p
  | _, .ret _ => PUnit.unit
  | _, .letExpr _ _ k => defaultPureStrategy who k
  | _, .sample _ _ k => defaultPureStrategy who k
  | Γ, .commit _ owner (b := b) _ k => by
      by_cases h : owner = who
      · subst h
        exact by
          simpa [ProgramPureStrategy] using
            ((fun _ : ViewEnv (P := P) (L := L) owner Γ =>
                Classical.arbitrary (L.Val b)),
             defaultPureStrategy owner k)
      · simpa [ProgramPureStrategy, h] using defaultPureStrategy who k
  | _, .reveal _ _ _ _ k => defaultPureStrategy who k

/-- The default joint pure profile. -/
noncomputable def defaultPureProfile
    [∀ τ : L.Ty, Nonempty (L.Val τ)]
    {Γ : VCtx P L} (p : VegasCore P L Γ) :
    ProgramPureProfile (P := P) (L := L) p :=
  fun who => defaultPureStrategy who p

/-- A guard is *trivially true* if it evaluates to `true` for every
action and environment. -/
def GuardTrivial {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) : Prop :=
  ∀ (a : L.Val b) (ρ : Env L.Val (eraseVCtx Γ)),
    evalGuard (Player := P) (L := L) R a ρ = true

/-- Every commit site in the program has a trivially-true guard. -/
def TrivialGuards :
    {Γ : VCtx P L} → VegasCore P L Γ → Prop
  | _, .ret _ => True
  | _, .letExpr _ _ k => TrivialGuards k
  | _, .sample _ _ k => TrivialGuards k
  | _, .commit _ _ R k => GuardTrivial R ∧ TrivialGuards k
  | _, .reveal _ _ _ _ k => TrivialGuards k

/-- Under `TrivialGuards`, the default pure strategy is guard-legal:
every proposed action trivially satisfies the guard. -/
theorem defaultPureStrategy_IsLegal
    [∀ τ : L.Ty, Nonempty (L.Val τ)]
    {who : P} : {Γ : VCtx P L} → (p : VegasCore P L Γ) →
    TrivialGuards p →
    (defaultPureStrategy (L := L) who p).IsLegal p
  | _, .ret _, _ => trivial
  | _, .letExpr _ _ k, htriv => by
      dsimp [defaultPureStrategy, ProgramPureStrategy.IsLegal]
      exact defaultPureStrategy_IsLegal k htriv
  | _, .sample _ _ k, htriv => by
      dsimp [defaultPureStrategy, ProgramPureStrategy.IsLegal]
      exact defaultPureStrategy_IsLegal k htriv
  | _, .commit x owner R k, htriv => by
      dsimp [defaultPureStrategy, ProgramPureStrategy.IsLegal]
      obtain ⟨hguard, htail⟩ := htriv
      by_cases h : owner = who
      · subst h
        split
        · refine ⟨?_, ?_⟩
          · intro ρ
            simp only
            exact hguard _ _
          · simpa using defaultPureStrategy_IsLegal k htail
        · exact absurd rfl ‹_›
      · split
        · rename_i h_eq
          exact absurd h_eq h
        · simpa using defaultPureStrategy_IsLegal k htail
  | _, .reveal _ _ _ _ k, htriv => by
      dsimp [defaultPureStrategy, ProgramPureStrategy.IsLegal]
      exact defaultPureStrategy_IsLegal k htriv

/-- The default pure profile is guard-legal under `TrivialGuards`. -/
theorem defaultPureProfile_IsLegal
    [∀ τ : L.Ty, Nonempty (L.Val τ)]
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (htriv : TrivialGuards p) :
    (defaultPureProfile p).IsLegal := fun _ =>
  defaultPureStrategy_IsLegal p htriv

/-- `Nonempty` constructor for the trivial-guard case. -/
@[reducible] noncomputable def LegalProgramPureProfile.instNonempty_of_trivialGuards
    (g : WFProgram P L) [∀ τ : L.Ty, Nonempty (L.Val τ)]
    (htriv : TrivialGuards g.prog) :
    Nonempty (LegalProgramPureProfile g) :=
  ⟨fun _ => ⟨defaultPureStrategy _ g.prog,
    defaultPureStrategy_IsLegal g.prog htriv⟩⟩

/-! ## General case — under `WFCtx` -/

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
    (hfresh : Fresh (P := P) (L := L) x Γ)
    (hR : GuardUsesOnly (L := L) (Γ := Γ) (x := x) (who := who) R)
    {a : L.Val b}
    {ρ₁ ρ₂ : Env L.Val (eraseVCtx Γ)}
    (hview : projectViewEnv who ρ₁ = projectViewEnv who ρ₂) :
    evalGuard (Player := P) (L := L) R a ρ₁ =
      evalGuard (Player := P) (L := L) R a ρ₂ :=
  evalGuard_eq_of_obsEq hfresh hR (obsEq_of_projectViewEnv_eq hctx hview)

/-- From program-level legality (`Legal`), there exists a pure kernel
that is guard-legal at the given commit site. The kernel is defined
per-view using `Classical.choose` on the existence witnessed by
`Legal`; view-uniformity (from `WFCtx` + `Fresh` + `GuardUsesOnly`)
ensures the per-view choice is legal at every environment that
projects to that view.

"Unreachable" views (those that no environment projects to) are
filled with `Classical.arbitrary`; legality imposes no constraint
there, since `IsLegalAt` only quantifies over environments and their
projected views. -/
theorem exists_legalKernel
    [∀ τ : L.Ty, Nonempty (L.Val τ)]
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    (hctx : WFCtx (L := L) Γ)
    (hfresh : Fresh (P := P) (L := L) x Γ)
    (hR : GuardUsesOnly (L := L) (Γ := Γ) (x := x) (who := who) R)
    (hL : ∀ ρ : Env L.Val (eraseVCtx Γ), ∃ a : L.Val b,
        evalGuard (Player := P) (L := L) R a ρ = true) :
    ∃ κ : PureKernel (P := P) (L := L) who Γ b,
      κ.IsLegalAt (P := P) (L := L) (x := x) (who := who) (b := b) R := by
  classical
  refine ⟨fun view =>
    if hreach : ∃ ρ, projectViewEnv who ρ = view then
      Classical.choose (hL hreach.choose)
    else
      Classical.arbitrary (L.Val b), ?_⟩
  intro ρ
  dsimp only [PureKernel.IsLegalAt]
  have hreach : ∃ ρ', projectViewEnv who ρ' = projectViewEnv who ρ := ⟨ρ, rfl⟩
  rw [dif_pos hreach]
  have hview_eq : projectViewEnv who hreach.choose = projectViewEnv who ρ :=
    hreach.choose_spec
  have hspec := Classical.choose_spec (hL hreach.choose)
  rw [← evalGuard_eq_of_projectViewEnv_eq hctx hfresh hR hview_eq]
  exact hspec

/-- For every well-formed program over a `WFCtx` initial context and
every player, there exists a guard-legal pure strategy. The
construction recurses on the program structure: `ret` gives
`PUnit.unit`; `letExpr`, `sample`, and `reveal` recurse after
extending the context by a fresh binding (using `FreshBindings`);
`commit` uses `exists_legalKernel` for the owner's kernel at that
site and recurses on the tail. -/
theorem exists_legal_pureStrategy [∀ τ : L.Ty, Nonempty (L.Val τ)] :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
    WFCtx (L := L) Γ → FreshBindings p → ViewScoped p → Legal p →
    ∀ who, ∃ s : ProgramPureStrategy (P := P) (L := L) who p, s.IsLegal p
  | _, .ret _, _, _, _, _, _ => ⟨PUnit.unit, trivial⟩
  | _, .letExpr _ _ k, hctx, hfresh, hsc, hl, who => by
      obtain ⟨s, hs⟩ :=
        exists_legal_pureStrategy k
          (WFCtx.cons hfresh.1 hctx) hfresh.2 hsc hl who
      exact ⟨s, hs⟩
  | _, .sample _ _ k, hctx, hfresh, hsc, hl, who => by
      obtain ⟨s, hs⟩ :=
        exists_legal_pureStrategy k
          (WFCtx.cons hfresh.1 hctx) hfresh.2 hsc hl who
      exact ⟨s, hs⟩
  | _, .reveal _ _ _ _ k, hctx, hfresh, hsc, hl, who => by
      obtain ⟨s, hs⟩ :=
        exists_legal_pureStrategy k
          (WFCtx.cons hfresh.1 hctx) hfresh.2 hsc hl who
      exact ⟨s, hs⟩
  | _, .commit x owner (b := b) R k, hctx, hfresh, hsc, hl, who => by
      have hctx' : WFCtx (L := L) ((x, BindTy.hidden owner b) :: _) :=
        WFCtx.cons hfresh.1 hctx
      obtain ⟨s_tail, hs_tail⟩ :=
        exists_legal_pureStrategy k hctx' hfresh.2 hsc.2 hl.2 who
      by_cases hown : owner = who
      · subst hown
        obtain ⟨κ, hκ⟩ :=
          exists_legalKernel (who := owner) hctx hfresh.1 hsc.1 hl.1
        refine ⟨?_, ?_⟩
        · exact by
            simpa [ProgramPureStrategy] using (κ, s_tail)
        · dsimp [ProgramPureStrategy.IsLegal]
          split
          · rename_i h_eq
            refine ⟨?_, ?_⟩
            · -- κ.IsLegalAt R for the ⟨κ, s_tail⟩.1 projection
              simpa using hκ
            · simpa using hs_tail
          · exact absurd rfl ‹_›
      · refine ⟨?_, ?_⟩
        · exact by
            simpa [ProgramPureStrategy, hown] using s_tail
        · dsimp [ProgramPureStrategy.IsLegal]
          split
          · rename_i h_eq
            exact absurd h_eq hown
          · simpa using hs_tail

/-- Profile-level existence: for every well-formed program with a
`WFCtx` initial context and base-type nonemptiness, there exists a
guard-legal pure profile. -/
theorem exists_legal_pureProfile
    [∀ τ : L.Ty, Nonempty (L.Val τ)]
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (hctx : WFCtx (L := L) Γ) (hwf : WF p) (hl : Legal p) :
    ∃ σ : ProgramPureProfile (P := P) (L := L) p, σ.IsLegal := by
  classical
  refine ⟨fun who =>
    Classical.choose (exists_legal_pureStrategy p hctx hwf.1 hwf.2.2 hl who), ?_⟩
  intro who
  exact Classical.choose_spec
    (exists_legal_pureStrategy p hctx hwf.1 hwf.2.2 hl who)

/-- `Nonempty` constructor for the legal pure profile, under
`WFCtx g.Γ` (distinct initial variable names) and base-type
nonemptiness. Combines `exists_legal_pureProfile` with the three
fields of the `WFProgram` bundle. -/
@[reducible] noncomputable def LegalProgramPureProfile.instNonempty_of_wfctx
    (g : WFProgram P L) [∀ τ : L.Ty, Nonempty (L.Val τ)]
    (hctx : WFCtx (L := L) g.Γ) :
    Nonempty (LegalProgramPureProfile g) := by
  obtain ⟨σ, hσ⟩ := exists_legal_pureProfile hctx g.wf g.legal
  exact ⟨fun who => ⟨σ who, hσ who⟩⟩

end Vegas
