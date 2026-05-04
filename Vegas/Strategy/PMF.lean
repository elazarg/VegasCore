import Vegas.Strategy.Behavioral

/-!
# Fixed-program PMF behavioral strategy carriers

This module contains the syntax-recursive PMF-valued behavioral strategy space
and guard-legality predicates. PMF outcome evaluation and strategic-form
packaging remain in `Vegas.StrategicPMF` while the collapse proceeds.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A PMF behavioral choice rule for one fixed commit site. Unlike
`ProgramBehavioralKernel` (FDist-valued), no explicit normalization witness
is needed because PMF is inherently normalized. -/
@[ext]
structure ProgramBehavioralKernelPMF
    (who : P) (Γ : VCtx P L) (b : L.Ty) where
  run : ViewEnv who Γ → PMF (L.Val b)

namespace ProgramBehavioralKernelPMF

/-- Turn a deterministic local rule into a PMF behavioral local rule. -/
noncomputable def ofPure
    {who : P} {Γ : VCtx P L} {b : L.Ty}
    (κ : PureKernel who Γ b) :
    ProgramBehavioralKernelPMF who Γ b :=
  { run := fun view => PMF.pure (κ view) }

@[simp] theorem run_ofPure
    {who : P} {Γ : VCtx P L} {b : L.Ty}
    (κ : PureKernel who Γ b)
    (view : ViewEnv who Γ) :
    (ofPure κ).run view = PMF.pure (κ view) := rfl

/-- Convert an FDist behavioral kernel to a PMF behavioral kernel. -/
noncomputable def ofFDist
    {who : P} {Γ : VCtx P L} {b : L.Ty}
    (κ : ProgramBehavioralKernel who Γ b) :
    ProgramBehavioralKernelPMF who Γ b :=
  { run := fun view => (κ.run view).toPMF (κ.normalized view) }

@[simp] theorem run_ofFDist
    {who : P} {Γ : VCtx P L} {b : L.Ty}
    (κ : ProgramBehavioralKernel who Γ b)
    (view : ViewEnv who Γ) :
    (ofFDist κ).run view =
      (κ.run view).toPMF (κ.normalized view) := rfl

end ProgramBehavioralKernelPMF

/-- Player-`who` PMF behavioral strategies for the fixed program `p`: one
PMF choice rule for each commit site of `p` owned by `who`. -/
inductive ProgramBehavioralStrategyPMF (who : P) :
    {Γ : VCtx P L} → VegasCore P L Γ → Type where
  | ret {Γ : VCtx P L} {u} :
      ProgramBehavioralStrategyPMF who (.ret (Γ := Γ) u)
  | letExpr {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b} {k : VegasCore P L ((x, .pub b) :: Γ)} :
      ProgramBehavioralStrategyPMF who k →
      ProgramBehavioralStrategyPMF who (.letExpr x e k)
  | sample {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {D' : L.DistExpr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)} :
      ProgramBehavioralStrategyPMF who k →
      ProgramBehavioralStrategyPMF who (.sample x D' k)
  | commitOwn {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)} :
      ProgramBehavioralKernelPMF who Γ b →
      ProgramBehavioralStrategyPMF who k →
      ProgramBehavioralStrategyPMF who (.commit x who R k)
  | commitOther {Γ : VCtx P L} {x : VarId} {owner : P} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden owner b) :: Γ)}
      (h : owner ≠ who) :
      ProgramBehavioralStrategyPMF who k →
      ProgramBehavioralStrategyPMF who (.commit x owner R k)
  | reveal {Γ : VCtx P L} {y : VarId} {owner : P} {x : VarId} {b : L.Ty}
      {hx : VHasVar (L := L) Γ x (.hidden owner b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)} :
      ProgramBehavioralStrategyPMF who k →
      ProgramBehavioralStrategyPMF who (.reveal y owner x hx k)

/-- Joint PMF behavioral strategy profile for the fixed program `p`. -/
abbrev ProgramBehavioralProfilePMF {Γ : VCtx P L} (p : VegasCore P L Γ) : Type :=
  ∀ who, ProgramBehavioralStrategyPMF who p

namespace ProgramBehavioralStrategyPMF

/-- Extract the current player's PMF behavioral rule at the head commit site. -/
def headKernel
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralStrategyPMF who (.commit x who R k)) :
    ViewEnv who Γ → PMF (L.Val b) :=
  match σ with
  | .commitOwn kern _ => kern.run

/-- Drop the head commit-site choice rule from the acting player's strategy. -/
def tailOwn
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralStrategyPMF who (.commit x who R k)) :
    ProgramBehavioralStrategyPMF who k :=
  match σ with
  | .commitOwn _ tail => tail

/-- Drop the head commit-site wrapper from any player's strategy. -/
def tail
    {Γ : VCtx P L} {x : VarId} {owner who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden owner b) :: Γ)}
    (σ : ProgramBehavioralStrategyPMF who (.commit x owner R k)) :
    ProgramBehavioralStrategyPMF who k :=
  match σ with
  | .commitOwn _ tail => tail
  | .commitOther _ tail => tail

@[simp] theorem headKernel_mk
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (kern : ProgramBehavioralKernelPMF who Γ b)
    (tail : ProgramBehavioralStrategyPMF who k) :
    headKernel (R := R) (.commitOwn kern tail) = kern.run := rfl

end ProgramBehavioralStrategyPMF

namespace ProgramBehavioralProfilePMF

/-- Drop the head commit site from a PMF behavioral profile. -/
def tail
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralProfilePMF (.commit x who R k)) :
    ProgramBehavioralProfilePMF k :=
  fun i => by
    by_cases h : who = i
    · subst h
      exact ProgramBehavioralStrategyPMF.tailOwn (σ who)
    · exact match σ i with
      | .commitOther _ tail => tail
      | .commitOwn _ tail => tail

end ProgramBehavioralProfilePMF

/-! ## Guard-legality predicate -/

/-- PMF-valued analogue of `ProgramBehavioralKernel.IsLegalAt`: at every
erased environment, the kernel's support is contained in the guard-satisfying
actions for the current commit site. -/
def ProgramBehavioralKernelPMF.IsLegalAt
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    (κ : ProgramBehavioralKernelPMF who Γ b)
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) : Prop :=
  ∀ (ρ : Env L.Val (eraseVCtx Γ)) {v : L.Val b},
    v ∈ (κ.run (projectViewEnv who ρ)).support →
      evalGuard (Player := P) (L := L) R v ρ = true

/-- A PMF behavioral strategy is guard-legal when every owned commit-site
kernel is supported on guard-satisfying actions. -/
def ProgramBehavioralStrategyPMF.IsLegal : {who : P} →
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
    ProgramBehavioralStrategyPMF who p → Prop
  | _, _, .ret _, _ => True
  | who, _, .letExpr _ _ k, .letExpr σ =>
      ProgramBehavioralStrategyPMF.IsLegal (who := who) k σ
  | who, _, .sample _ _ k, .sample σ =>
      ProgramBehavioralStrategyPMF.IsLegal (who := who) k σ
  | who, _, .commit _x owner R k, σ => by
      by_cases h : owner = who
      · subst h
        exact
          (∀ (ρ : Env L.Val (eraseVCtx _)) {v},
            v ∈ (ProgramBehavioralStrategyPMF.headKernel σ
              (projectViewEnv owner ρ)).support →
              evalGuard (Player := P) (L := L) R v ρ = true) ∧
          ProgramBehavioralStrategyPMF.IsLegal (who := owner) k
            (ProgramBehavioralStrategyPMF.tailOwn σ)
      · exact ProgramBehavioralStrategyPMF.IsLegal (who := who) k
          (ProgramBehavioralStrategyPMF.tail σ)
  | who, _, .reveal _ _ _ _ k, .reveal σ =>
      ProgramBehavioralStrategyPMF.IsLegal (who := who) k σ

/-- A PMF behavioral profile is legal when each player's PMF strategy is
guard-legal. -/
def ProgramBehavioralProfilePMF.IsLegal {Γ : VCtx P L} {p : VegasCore P L Γ}
    (σ : ProgramBehavioralProfilePMF p) : Prop :=
  ∀ who, (σ who).IsLegal p

namespace ProgramBehavioralProfilePMF

theorem tail_isLegal
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {σ : ProgramBehavioralProfilePMF (.commit x who R k)}
    (hσ : σ.IsLegal) :
    (tail σ).IsLegal := by
  intro i
  by_cases h : who = i
  · subst i
    have hsite := hσ who
    simp [ProgramBehavioralStrategyPMF.IsLegal] at hsite
    simpa [tail, ProgramBehavioralStrategyPMF.tailOwn] using hsite.2
  · have hsite := hσ i
    cases σi : σ i with
    | commitOwn kern tail' =>
        exact False.elim (h rfl)
    | commitOther hne tail' =>
        simpa [ProgramBehavioralStrategyPMF.IsLegal, tail, h, σi] using hsite

end ProgramBehavioralProfilePMF

/-- Guard-legal syntax-recursive PMF behavioral strategies over a checked
program bundle. -/
abbrev SyntaxLegalProgramBehavioralStrategyPMF (g : WFProgram P L) (who : P) : Type :=
  { s : ProgramBehavioralStrategyPMF who g.prog //
    s.IsLegal g.prog }

/-- Guard-legal joint syntax-recursive PMF behavioral profiles over a checked
program bundle. -/
abbrev SyntaxLegalProgramBehavioralProfilePMF (g : WFProgram P L) : Type :=
  ∀ who, SyntaxLegalProgramBehavioralStrategyPMF g who

end Vegas
