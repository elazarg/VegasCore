import Vegas.ViewKernel
import Vegas.WFProgram

/-!
# Fixed-program behavioral strategy carriers

This module contains only the syntax-recursive behavioral strategy spaces and
guard-legality predicates. It intentionally avoids the legacy outcome
evaluators and kernel-game packaging so protocol/FOSG code can depend on
strategy carriers without importing denotational strategic semantics.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A normalized behavioral choice rule for one fixed commit site. -/
structure ProgramBehavioralKernel
    (who : P) (Γ : VCtx P L) (b : L.Ty) where
  run : BehavioralKernel who Γ b
  normalized : ∀ view, FDist.totalWeight (run view) = 1

/-- Turn a deterministic local rule into a normalized behavioral local rule. -/
noncomputable def ProgramBehavioralKernel.ofPure
    {who : P} {Γ : VCtx P L} {b : L.Ty}
    (κ : PureKernel who Γ b) :
    ProgramBehavioralKernel who Γ b :=
  { run := fun view => FDist.pure (κ view)
    normalized := by
      intro view
      simp [FDist.totalWeight_pure] }

@[simp] theorem ProgramBehavioralKernel.run_ofPure
    {who : P} {Γ : VCtx P L} {b : L.Ty}
    (κ : PureKernel who Γ b)
    (view : ViewEnv who Γ) :
    (ProgramBehavioralKernel.ofPure κ).run view = FDist.pure (κ view) := rfl

/-- Player-`who` behavioral strategies for the fixed program `p`: one
normalized behavioral choice rule for each commit site of `p` owned by `who`. -/
def ProgramBehavioralStrategy (who : P) :
    {Γ : VCtx P L} → VegasCore P L Γ → Type
  | _, .ret _ => PUnit
  | _, .letExpr _ _ k => ProgramBehavioralStrategy who k
  | _, .sample _ _ k => ProgramBehavioralStrategy who k
  | Γ, .commit _ owner (b := b) _ k =>
      if owner = who then
        ProgramBehavioralKernel who Γ b × ProgramBehavioralStrategy who k
      else
        ProgramBehavioralStrategy who k
  | _, .reveal _ _ _ _ k => ProgramBehavioralStrategy who k

/-- Joint behavioral strategy profile for the fixed program `p`. -/
abbrev ProgramBehavioralProfile {Γ : VCtx P L} (p : VegasCore P L Γ) : Type :=
  ∀ who, ProgramBehavioralStrategy who p

namespace ProgramBehavioralStrategy

/-- Extract the current player's behavioral decision rule at the head commit site. -/
def headKernel
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralStrategy who (.commit x who R k)) :
    BehavioralKernel who Γ b := by
  let σ' : ProgramBehavioralKernel who Γ b ×
      ProgramBehavioralStrategy who k := by
    simpa [ProgramBehavioralStrategy] using σ
  exact σ'.1.run

/-- Normalization of the current player's behavioral rule at the head commit site. -/
theorem headKernel_normalized
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralStrategy who (.commit x who R k))
    (view : ViewEnv who Γ) :
    FDist.totalWeight (headKernel σ view) = 1 := by
  let σ' : ProgramBehavioralKernel who Γ b ×
      ProgramBehavioralStrategy who k := by
    simpa [ProgramBehavioralStrategy] using σ
  exact σ'.1.normalized view

/-- Drop the head commit-site choice rule from the acting player's strategy. -/
def tailOwn
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralStrategy who (.commit x who R k)) :
    ProgramBehavioralStrategy who k := by
  let σ' : ProgramBehavioralKernel who Γ b ×
      ProgramBehavioralStrategy who k := by
    simpa [ProgramBehavioralStrategy] using σ
  exact σ'.2

end ProgramBehavioralStrategy

namespace ProgramBehavioralProfile

/-- Drop the head commit site from a behavioral profile. -/
def tail
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralProfile (.commit x who R k)) :
    ProgramBehavioralProfile k :=
  fun i =>
    by
      by_cases h : who = i
      · subst h
        exact ProgramBehavioralStrategy.tailOwn (σ who)
      · simpa [ProgramBehavioralStrategy, h] using σ i

end ProgramBehavioralProfile

/-! ## Guard-legality predicate -/

/-- A per-commit behavioral-kernel legality predicate: at every erased
environment `ρ`, the kernel's output distribution (viewed through `who`'s
view projection of `ρ`) is supported on actions that satisfy the commit
guard `R` under `ρ`. -/
def ProgramBehavioralKernel.RespectsGuard
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    (κ : ProgramBehavioralKernel who Γ b)
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) : Prop :=
  ∀ ρ : Env L.Val (eraseVCtx Γ),
    FDist.Supported (κ.run (projectViewEnv who ρ))
      (fun a => evalGuard (Player := P) (L := L) R a ρ = true)

/-- A behavioral strategy is guard-legal when every kernel at every
owned commit site satisfies `IsLegalAt` for that commit's guard. -/
def ProgramBehavioralStrategy.RespectsGuards : {who : P} →
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
    ProgramBehavioralStrategy who p → Prop
  | _, _, .ret _, _ => True
  | who, _, .letExpr _ _ k, σ =>
      ProgramBehavioralStrategy.RespectsGuards (who := who) k σ
  | who, _, .sample _ _ k, σ =>
      ProgramBehavioralStrategy.RespectsGuards (who := who) k σ
  | who, _, .commit _x owner (b := b) R k, σ => by
      by_cases h : owner = who
      · let σ' : ProgramBehavioralKernel owner _ b ×
                 ProgramBehavioralStrategy owner k := by
          subst h
          simpa [ProgramBehavioralStrategy] using σ
        exact σ'.1.RespectsGuard R
              ∧ ProgramBehavioralStrategy.RespectsGuards (who := owner) k σ'.2
      · let σ' : ProgramBehavioralStrategy who k := by
          simpa [ProgramBehavioralStrategy, h] using σ
        exact ProgramBehavioralStrategy.RespectsGuards (who := who) k σ'
  | who, _, .reveal _ _ _ _ k, σ =>
      ProgramBehavioralStrategy.RespectsGuards (who := who) k σ

/-- A behavioral profile is legal when every player's strategy is legal. -/
def ProgramBehavioralProfile.RespectsGuards {Γ : VCtx P L} {p : VegasCore P L Γ}
    (σ : ProgramBehavioralProfile p) : Prop :=
  ∀ who, (σ who).RespectsGuards p

namespace ProgramBehavioralProfile

/-- Dropping the head commit site preserves behavioral guard-legality. -/
theorem tail_isLegal
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {σ : ProgramBehavioralProfile (.commit x who R k)}
    (hσ : σ.RespectsGuards) :
    (ProgramBehavioralProfile.tail σ).RespectsGuards := by
  intro j
  by_cases hj : who = j
  · subst hj
    have hσ_who : (σ who).RespectsGuards (.commit x who R k) := hσ who
    dsimp [ProgramBehavioralStrategy.RespectsGuards] at hσ_who
    dsimp [ProgramBehavioralProfile.tail]
    split at hσ_who
    · split
      · exact hσ_who.2
      · exact absurd rfl ‹_›
    · exact absurd rfl ‹_›
  · have hσ_j : (σ j).RespectsGuards (.commit x who R k) := hσ j
    dsimp [ProgramBehavioralStrategy.RespectsGuards] at hσ_j
    dsimp [ProgramBehavioralProfile.tail]
    split at hσ_j
    · rename_i h
      exact absurd h hj
    · split
      · rename_i h
        exact absurd h hj
      · exact hσ_j

end ProgramBehavioralProfile

/-- Guard-legal behavioral strategies over a `WFProgram` bundle. -/
abbrev FeasibleProgramBehavioralStrategy (g : WFProgram P L) (who : P) : Type :=
  { s : ProgramBehavioralStrategy who g.prog //
    s.RespectsGuards g.prog }

/-- Guard-legal joint behavioral profile over a `WFProgram` bundle. -/
abbrev FeasibleProgramBehavioralProfile (g : WFProgram P L) : Type :=
  ∀ who, FeasibleProgramBehavioralStrategy g who

end Vegas
