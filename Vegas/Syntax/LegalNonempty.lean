import Vegas.Syntax.Strategy.Pure
import Vegas.ViewProjection

/-!
# Nonempty instance for guard-legal pure profiles

Two constructors witnessing `Nonempty (FeasibleProgramPureProfile g)`:

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
    ProgramPureStrategy who p
  | _, .ret _ => PUnit.unit
  | _, .letExpr _ _ k => defaultPureStrategy who k
  | _, .sample _ _ k => defaultPureStrategy who k
  | Γ, .commit _ owner (b := b) _ k => by
      by_cases h : owner = who
      · subst h
        exact by
          simpa [ProgramPureStrategy] using
            ((fun _ : ViewEnv owner Γ =>
                Classical.arbitrary (L.Val b)),
             defaultPureStrategy owner k)
      · simpa [ProgramPureStrategy, h] using defaultPureStrategy who k
  | _, .reveal _ _ _ _ k => defaultPureStrategy who k

/-- The default joint pure profile. -/
noncomputable def defaultPureProfile
    [∀ τ : L.Ty, Nonempty (L.Val τ)]
    {Γ : VCtx P L} (p : VegasCore P L Γ) :
    ProgramPureProfile p :=
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
    (defaultPureStrategy (L := L) who p).RespectsGuards p
  | _, .ret _, _ => trivial
  | _, .letExpr _ _ k, htriv => by
      dsimp [defaultPureStrategy, ProgramPureStrategy.RespectsGuards]
      exact defaultPureStrategy_IsLegal k htriv
  | _, .sample _ _ k, htriv => by
      dsimp [defaultPureStrategy, ProgramPureStrategy.RespectsGuards]
      exact defaultPureStrategy_IsLegal k htriv
  | _, .commit x owner R k, htriv => by
      dsimp [defaultPureStrategy, ProgramPureStrategy.RespectsGuards]
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
      dsimp [defaultPureStrategy, ProgramPureStrategy.RespectsGuards]
      exact defaultPureStrategy_IsLegal k htriv

/-- The default pure profile is guard-legal under `TrivialGuards`. -/
theorem defaultPureProfile_IsLegal
    [∀ τ : L.Ty, Nonempty (L.Val τ)]
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (htriv : TrivialGuards p) :
    (defaultPureProfile p).RespectsGuards := fun _ =>
  defaultPureStrategy_IsLegal p htriv

/-- `Nonempty` constructor for the trivial-guard case. -/
@[reducible] noncomputable def FeasibleProgramPureProfile.instNonempty_of_trivialGuards
    (g : WFProgram P L) [∀ τ : L.Ty, Nonempty (L.Val τ)]
    (htriv : TrivialGuards g.prog) :
    Nonempty (FeasibleProgramPureProfile g) :=
  ⟨fun _ => ⟨defaultPureStrategy _ g.prog,
    defaultPureStrategy_IsLegal g.prog htriv⟩⟩

/-! ## General case — under `WFCtx` -/


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
    (hfresh : Fresh x Γ)
    (hR : GuardUsesOnly (L := L) (Γ := Γ) (x := x) (who := who) R)
    (hL : ∀ ρ : Env L.Val (eraseVCtx Γ), ∃ a : L.Val b,
        evalGuard (Player := P) (L := L) R a ρ = true) :
    ∃ κ : PureKernel who Γ b,
      κ.RespectsGuard (x := x) (who := who) (b := b) R := by
  classical
  refine ⟨fun view =>
    if hreach : ∃ ρ, projectViewEnv who ρ = view then
      Classical.choose (hL hreach.choose)
    else
      Classical.arbitrary (L.Val b), ?_⟩
  intro ρ
  dsimp only [PureKernel.RespectsGuard]
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
    ∀ who, ∃ s : ProgramPureStrategy who p, s.RespectsGuards p
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
        · dsimp [ProgramPureStrategy.RespectsGuards]
          split
          · rename_i h_eq
            refine ⟨?_, ?_⟩
            · -- κ.RespectsGuard R for the ⟨κ, s_tail⟩.1 projection
              simpa using hκ
            · simpa using hs_tail
          · exact absurd rfl ‹_›
      · refine ⟨?_, ?_⟩
        · exact by
            simpa [ProgramPureStrategy, hown] using s_tail
        · dsimp [ProgramPureStrategy.RespectsGuards]
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
    ∃ σ : ProgramPureProfile p, σ.RespectsGuards := by
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
@[reducible] noncomputable def FeasibleProgramPureProfile.instNonempty_of_wfctx
    (g : WFProgram P L) [∀ τ : L.Ty, Nonempty (L.Val τ)]
    (hctx : WFCtx (L := L) g.Γ) :
    Nonempty (FeasibleProgramPureProfile g) := by
  obtain ⟨σ, hσ⟩ := exists_legal_pureProfile hctx g.wf g.legal
  exact ⟨fun who => ⟨σ who, hσ who⟩⟩

end Vegas
