import Vegas.Equilibrium
import Vegas.PureStrategic

/-!
# Vegas strategy vocabulary

Generic predicates and dominance wrappers for strategy claims about checked
Vegas programs. These definitions are program-level: they do not mention any
particular compiler, backend, or theorem family.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## PMF behavioral strategy predicates -/

/-- A predicate on one player's PMF behavioral strategies in a checked Vegas
program. -/
def StrategyPredicate [Fintype P]
    (g : WFProgram P L) [FiniteDomains g] (who : P) : Type :=
  Strategy g who → Prop

/-- A profile satisfies a per-player PMF behavioral strategy predicate when
each component satisfies its player's predicate. -/
def ProfileSatisfies [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (Pred : ∀ who, Strategy g who → Prop)
    (σ : StrategyProfile g) : Prop :=
  ∀ who, Pred who (σ who)

@[simp] theorem profileSatisfies_iff [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (Pred : ∀ who, Strategy g who → Prop)
    (σ : StrategyProfile g) :
    ProfileSatisfies g Pred σ ↔ ∀ who, Pred who (σ who) :=
  Iff.rfl

theorem ProfileSatisfies.mono [Fintype P]
    {g : WFProgram P L} [FiniteDomains g]
    {Pred Q : ∀ who, Strategy g who → Prop}
    (h : ∀ who s, Pred who s → Q who s)
    {σ : StrategyProfile g}
    (hσ : ProfileSatisfies g Pred σ) :
    ProfileSatisfies g Q σ :=
  fun who => h who (σ who) (hσ who)

/-! ## Pure strategy predicates -/

/-- A predicate on one player's reachable-legal pure strategies in a checked
Vegas program. -/
def PureStrategyPredicate
    (g : WFProgram P L) (who : P) : Type :=
  pureStrategyAt g who → Prop

/-- A pure profile satisfies a per-player pure strategy predicate when each
component satisfies its player's predicate. -/
def PureProfileSatisfies
    (g : WFProgram P L)
    (Pred : ∀ who, pureStrategyAt g who → Prop)
    (σ : pureProfileAt g) : Prop :=
  ∀ who, Pred who (σ who)

@[simp] theorem pureProfileSatisfies_iff
    (g : WFProgram P L)
    (Pred : ∀ who, pureStrategyAt g who → Prop)
    (σ : pureProfileAt g) :
    PureProfileSatisfies g Pred σ ↔ ∀ who, Pred who (σ who) :=
  Iff.rfl

theorem PureProfileSatisfies.mono
    {g : WFProgram P L}
    {Pred Q : ∀ who, pureStrategyAt g who → Prop}
    (h : ∀ who s, Pred who s → Q who s)
    {σ : pureProfileAt g}
    (hσ : PureProfileSatisfies g Pred σ) :
    PureProfileSatisfies g Q σ :=
  fun who => h who (σ who) (hσ who)

/-! ## Dominance wrappers -/

/-- PMF behavioral weak dominance in the fixed checked Vegas program. -/
def WeaklyDominates [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (who : P) (s t : Strategy g who) : Prop :=
  (pmfBehavioralKernelGame g).WeaklyDominates who s t

/-- PMF behavioral strict dominance in the fixed checked Vegas program. -/
def StrictlyDominates [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (who : P) (s t : Strategy g who) : Prop :=
  (pmfBehavioralKernelGame g).StrictlyDominates who s t

/-- Pure weak dominance in the fixed checked Vegas program. -/
def PureWeaklyDominates [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (who : P) (s t : pureStrategyAt g who) : Prop :=
  (pureKernelGame g).WeaklyDominates who s t

/-- Pure strict dominance in the fixed checked Vegas program. -/
def PureStrictlyDominates [Fintype P]
    (g : WFProgram P L) [FiniteDomains g]
    (who : P) (s t : pureStrategyAt g who) : Prop :=
  (pureKernelGame g).StrictlyDominates who s t

end Vegas
