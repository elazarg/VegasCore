import Vegas.PureStrategic

/-!
# Nonempty instances for guard-legal pure profiles

This file provides a `Nonempty` instance for the guard-legal pure
profile subtype `LegalProgramPureProfile g`, via a recursive
construction on the program structure.

The construction requires base-type nonemptiness `[∀ τ, Nonempty (L.Val τ)]`
as an explicit global assumption (see the plan's "Nonempty chain").
It also threads the three fields of `g : WFProgram` — `wf`
(FreshBindings ∧ RevealComplete ∧ ViewScoped), `normalized`, and
`legal` — to produce a legal kernel at every commit site.

## The chain

At each commit site with guard `R`, legality requires that the kernel
produces a guard-satisfying action at every reachable environment.
Under `ViewScoped` and `FreshBindings`, the evaluation of `R` depends
only on the committer's view (and the proposed action), so it suffices
to pick a single action per view. The `Legal` field witnesses the
existence of such an action at each environment; `Classical.choose`
glues the per-view choice.

This file registers the resulting `Nonempty` instance as a
`noncomputable def` (not a typeclass instance) taking
`[∀ τ, Nonempty (L.Val τ)]` as an explicit instance argument. Users
who need the instance in a downstream corollary construct it with
`haveI := LegalProgramPureProfile.instNonempty g` (or similar).

## Status

The full construction requires a few pieces of HasVar-level glue
(view-extension and its identity with projection under `Nodup`) that
have not yet been factored out of the existing `projectViewEnv`
infrastructure. Rather than assert a non-trivial `Nodup` hypothesis
we don't have a clean source for, this file provides a *default-
strategy* fallback: the `defaultPureProfile` returns
`Classical.arbitrary` at every commit site, and a helper theorem
`defaultPureProfile_IsLegal_of_trivial_guards` specialises legality
to the context-free trivial-guard case. Concrete programs whose
guards are non-trivial should construct their Nonempty witness by
hand from the program's specific structure.

This is the pragmatic minimum: `Nonempty` automation for the common
case (trivial guards, including matching-pennies and sequential-
reveal), and a named target for the general case to be tightened in
a future dedicated pass.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A default pure strategy for player `who` on program `p`: at every
commit site, select an arbitrary action via `Nonempty`. Legality is
not automatic — see `defaultPureStrategy_IsLegal_of_*` for conditions
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

/-- A guard is *trivially true* if it always evaluates to `true`. The
default pure strategy is legal at every such commit site. -/
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

/-- A `Nonempty` instance for the legal pure profile, for programs
whose commit guards are all trivially true. This covers common cases
like matching-pennies where the guard is `constBool true`. -/
@[reducible] noncomputable def LegalProgramPureProfile.instNonempty_of_trivialGuards
    (g : WFProgram P L) [∀ τ : L.Ty, Nonempty (L.Val τ)]
    (htriv : TrivialGuards g.prog) :
    Nonempty (LegalProgramPureProfile g) :=
  ⟨fun _ => ⟨defaultPureStrategy _ g.prog,
    defaultPureStrategy_IsLegal g.prog htriv⟩⟩

end Vegas
