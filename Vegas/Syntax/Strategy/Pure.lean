import Vegas.Finite
import Vegas.WFProgram

/-!
# Fixed-program pure strategy carriers

This module contains the syntax-recursive pure strategy spaces, guard-legality
predicates, and finite instances. It is deliberately below the legacy pure
outcome evaluator and strategic-form game packaging.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Player-`who` pure strategies for the fixed program `p`: one deterministic
choice rule for each commit site of `p` owned by `who`. -/
def ProgramPureStrategy (who : P) :
    {Γ : VCtx P L} → VegasCore P L Γ → Type
  | _, .ret _ => PUnit
  | _, .letExpr _ _ k => ProgramPureStrategy who k
  | _, .sample _ _ k => ProgramPureStrategy who k
  | Γ, .commit _ owner (b := b) _ k =>
      if owner = who then
        PureKernel who Γ b × ProgramPureStrategy who k
      else
        ProgramPureStrategy who k
  | _, .reveal _ _ _ _ k => ProgramPureStrategy who k

/-- Joint pure strategy profile for the fixed program `p`. -/
abbrev ProgramPureProfile {Γ : VCtx P L} (p : VegasCore P L Γ) : Type :=
  ∀ who, ProgramPureStrategy who p

namespace ProgramPureStrategy

/-- Extract the current player's decision rule at the head commit site. -/
def headKernel
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramPureStrategy who (.commit x who R k)) :
    PureKernel who Γ b := by
  let σ' : PureKernel who Γ b ×
      ProgramPureStrategy who k := by
    simpa [ProgramPureStrategy] using σ
  exact σ'.1

/-- Drop the head commit-site choice rule from the acting player's strategy. -/
def tailOwn
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramPureStrategy who (.commit x who R k)) :
    ProgramPureStrategy who k := by
  let σ' : PureKernel who Γ b ×
      ProgramPureStrategy who k := by
    simpa [ProgramPureStrategy] using σ
  exact σ'.2

@[reducible] noncomputable def fintypeOfProof
    (who : P) :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      FiniteVCtxProof Γ → FiniteProgramProof p →
        Fintype (ProgramPureStrategy who p)
  | _, .ret _, _hΓ, .ret => inferInstanceAs (Fintype PUnit)
  | _, .letExpr _ _ k, hΓ, .letExpr head tail =>
      fintypeOfProof who k (.cons head hΓ) tail
  | _, .sample _ _ k, hΓ, .sample head tail =>
      fintypeOfProof who k (.cons head hΓ) tail
  | Γ, .commit _ owner (b := b) _ k, hΓ, hp =>
      match decEq owner who with
      | isTrue h =>
          let head : FiniteType L b := by
            cases hp with
            | commit head _ => exact head
          let tail : FiniteProgramProof k := by
            cases hp with
            | commit _ tail => exact tail
          let _ : FiniteVCtx (viewVCtx who Γ) :=
            { proof := hΓ.view who }
          let _ : FiniteCtx (eraseVCtx (viewVCtx who Γ)) :=
            FiniteVCtx.erase
          let _ : Fintype (ViewEnv who Γ) := by
            dsimp [ViewEnv]
            infer_instance
          let _ : Fintype (L.Val b) := head.fintype
          let _ : Fintype (PureKernel who Γ b) := by
            classical
            dsimp [PureKernel]
            exact @Pi.instFintype
              (ViewEnv who Γ)
              (fun _ => L.Val b)
              (Classical.decEq _)
              inferInstance
              (fun _ => head.fintype)
          let _ : Fintype (ProgramPureStrategy who k) :=
            fintypeOfProof who k (.cons head hΓ) tail
          by
            simpa [ProgramPureStrategy, h] using
              inferInstanceAs
                (Fintype (PureKernel who Γ b ×
                  ProgramPureStrategy who k))
      | isFalse h =>
          by
            let head : FiniteType L b := by
              cases hp with
              | commit head _ => exact head
            let tail : FiniteProgramProof k := by
              cases hp with
              | commit _ tail => exact tail
            simpa [ProgramPureStrategy, h] using
              fintypeOfProof who k (.cons head hΓ) tail
  | _, .reveal _ _ _ _ k, hΓ, .reveal head tail =>
      fintypeOfProof who k (.cons head hΓ) tail

noncomputable instance instFintype
    (who : P) {Γ : VCtx P L} (p : VegasCore P L Γ)
    [hΓ : FiniteVCtx Γ] [hp : FiniteProgram p] :
    Fintype (ProgramPureStrategy who p) :=
  fintypeOfProof who p hΓ.proof hp.proof

end ProgramPureStrategy

namespace ProgramPureProfile

/-- Drop the head commit site from a pure profile. -/
def tail
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramPureProfile (.commit x who R k)) :
    ProgramPureProfile k :=
  fun i =>
    by
      by_cases h : who = i
      · subst h
        exact ProgramPureStrategy.tailOwn (σ who)
      · simpa [ProgramPureStrategy, h] using σ i

noncomputable instance instFintype
    [Fintype P] {Γ : VCtx P L} (p : VegasCore P L Γ)
    [hΓ : FiniteVCtx Γ] [hp : FiniteProgram p] :
    Fintype (ProgramPureProfile p) := by
  classical
  dsimp [ProgramPureProfile]
  exact @Pi.instFintype
    P
    (fun who => ProgramPureStrategy who p)
    inferInstance
    inferInstance
    (fun who => ProgramPureStrategy.instFintype who p)

end ProgramPureProfile

/-! ## Guard-legality for pure strategies -/

/-- A per-commit pure-kernel legality predicate: at every erased
environment, the action chosen by the kernel (on `who`'s view of that
environment) satisfies the commit's guard. -/
def PureKernel.RespectsGuard
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    (κ : PureKernel who Γ b)
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) : Prop :=
  ∀ ρ : Env L.Val (eraseVCtx Γ),
    evalGuard (Player := P) (L := L) R
      (κ (projectViewEnv who ρ)) ρ = true

/-- A pure strategy is guard-legal when every kernel at every owned
commit site satisfies `IsLegalAt` for that commit's guard. -/
def ProgramPureStrategy.RespectsGuards : {who : P} →
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
    ProgramPureStrategy who p → Prop
  | _, _, .ret _, _ => True
  | who, _, .letExpr _ _ k, σ =>
      ProgramPureStrategy.RespectsGuards (who := who) k σ
  | who, _, .sample _ _ k, σ =>
      ProgramPureStrategy.RespectsGuards (who := who) k σ
  | who, _, .commit _x owner (b := b) R k, σ => by
      by_cases h : owner = who
      · let σ' : PureKernel owner _ b ×
                 ProgramPureStrategy owner k := by
          subst h
          simpa [ProgramPureStrategy] using σ
        exact σ'.1.RespectsGuard R
              ∧ ProgramPureStrategy.RespectsGuards (who := owner) k σ'.2
      · let σ' : ProgramPureStrategy who k := by
          simpa [ProgramPureStrategy, h] using σ
        exact ProgramPureStrategy.RespectsGuards (who := who) k σ'
  | who, _, .reveal _ _ _ _ k, σ =>
      ProgramPureStrategy.RespectsGuards (who := who) k σ

/-- A pure profile is legal when every player's strategy is legal. -/
def ProgramPureProfile.RespectsGuards {Γ : VCtx P L} {p : VegasCore P L Γ}
    (σ : ProgramPureProfile p) : Prop :=
  ∀ who, (σ who).RespectsGuards p

namespace ProgramPureProfile

/-- Dropping the head commit site preserves pure guard-legality. -/
theorem tail_isLegal
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {σ : ProgramPureProfile (.commit x who R k)}
    (hσ : σ.RespectsGuards) :
    (ProgramPureProfile.tail σ).RespectsGuards := by
  intro j
  by_cases hj : who = j
  · subst hj
    have hσ_who : (σ who).RespectsGuards (.commit x who R k) := hσ who
    dsimp [ProgramPureStrategy.RespectsGuards] at hσ_who
    dsimp [ProgramPureProfile.tail]
    split at hσ_who
    · split
      · exact hσ_who.2
      · exact absurd rfl ‹_›
    · exact absurd rfl ‹_›
  · have hσ_j : (σ j).RespectsGuards (.commit x who R k) := hσ j
    dsimp [ProgramPureStrategy.RespectsGuards] at hσ_j
    dsimp [ProgramPureProfile.tail]
    split at hσ_j
    · rename_i h
      exact absurd h hj
    · split
      · rename_i h
        exact absurd h hj
      · exact hσ_j

end ProgramPureProfile

/-- Guard-legal pure strategies over a `WFProgram` bundle. -/
abbrev FeasibleProgramPureStrategy (g : WFProgram P L) (who : P) : Type :=
  { s : ProgramPureStrategy who g.prog //
    s.RespectsGuards g.prog }

/-- Guard-legal joint pure profile over a `WFProgram` bundle. -/
abbrev FeasibleProgramPureProfile (g : WFProgram P L) : Type :=
  ∀ who, FeasibleProgramPureStrategy g who

/-- Classical `Fintype` on the per-player guard-legal pure strategy
subtype. Uses the program's finite-domain evidence and `Classical.dec` for
decidability of the legality predicate. -/
@[reducible] noncomputable instance FeasibleProgramPureStrategy.instFintype
    (g : WFProgram P L) [FiniteDomains g] (who : P) :
    Fintype (FeasibleProgramPureStrategy g who) := by
  classical
  letI : FiniteVCtx g.Γ := (inferInstance : FiniteDomains g).context
  letI : FiniteProgram g.prog := (inferInstance : FiniteDomains g).program
  let _ : Fintype (ProgramPureStrategy who g.prog) :=
    ProgramPureStrategy.instFintype who g.prog
  exact Subtype.fintype _

/-- Classical `Fintype` on the joint guard-legal pure profile. -/
@[reducible] noncomputable instance FeasibleProgramPureProfile.instFintype
    (g : WFProgram P L) [FiniteDomains g] [Fintype P] :
    Fintype (FeasibleProgramPureProfile g) := by
  classical
  have h : ∀ who, Fintype (FeasibleProgramPureStrategy g who) := fun who =>
    FeasibleProgramPureStrategy.instFintype g who
  exact Pi.instFintype

end Vegas
