import GameTheory.Core.GameMorphism
import Vegas.Strategic.Vocabulary

/-!
# Program-level strategy transport

Generic EU-preserving strategy maps between checked Vegas programs. This is a
program-to-program layer, not a compiler-specific one: examples, refinements,
compilers, and hand-written reductions can all instantiate the same structures.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P]

/-! ## PMF behavioral transport -/

/-- An EU-preserving PMF behavioral strategy morphism between two checked Vegas
programs. -/
abbrev BehavioralStrategyMorphism
    [Fintype P] {L₁ L₂ : IExpr}
    (source : WFProgram P L₁) [FiniteDomains source]
    (target : WFProgram P L₂) [FiniteDomains target] : Type :=
  KernelGame.EUMorphism
    (pmfBehavioralKernelGame source) (pmfBehavioralKernelGame target)

namespace BehavioralStrategyMorphism

variable [Fintype P] {L₁ L₂ : IExpr}
variable {source : WFProgram P L₁} [FiniteDomains source]
variable {target : WFProgram P L₂} [FiniteDomains target]

/-- Map a PMF behavioral strategy profile along a program-level strategy
morphism. -/
def mapProfile
    (F : BehavioralStrategyMorphism source target)
    (σ : StrategyProfile source) : StrategyProfile target :=
  fun who => F.stratMap who (σ who)

@[simp] theorem mapProfile_apply
    (F : BehavioralStrategyMorphism source target)
    (σ : StrategyProfile source) (who : P) :
    F.mapProfile σ who = F.stratMap who (σ who) := rfl

/-- Program-level morphisms preserve expected utility under mapped profiles. -/
theorem mapProfile_eu_eq
    (F : BehavioralStrategyMorphism source target)
    (σ : StrategyProfile source) (who : P) :
    eu target (F.mapProfile σ) who = eu source σ who :=
  F.eu_preserved σ who

/-- If the mapped target profile is Nash, then the source profile is Nash. -/
theorem source_nash_of_target_mapped_nash
    (F : BehavioralStrategyMorphism source target)
    {σ : StrategyProfile source}
    (hN : IsNash target (F.mapProfile σ)) :
    IsNash source σ := by
  simpa [IsNash, mapProfile] using
    (KernelGame.EUMorphism.nash_of_nash F hN)

end BehavioralStrategyMorphism

/-- An EU-preserving PMF behavioral strategy isomorphism between two checked
Vegas programs. -/
abbrev BehavioralStrategyIsomorphism
    [Fintype P] {L₁ L₂ : IExpr}
    (left : WFProgram P L₁) [FiniteDomains left]
    (right : WFProgram P L₂) [FiniteDomains right] : Type :=
  KernelGame.EUGameIsomorphism
    (pmfBehavioralKernelGame left) (pmfBehavioralKernelGame right)

namespace BehavioralStrategyIsomorphism

variable [Fintype P] {L₁ L₂ : IExpr}
variable {left : WFProgram P L₁} [FiniteDomains left]
variable {right : WFProgram P L₂} [FiniteDomains right]

/-- Map a PMF behavioral strategy profile along a program-level strategy
isomorphism. -/
def mapProfile
    (F : BehavioralStrategyIsomorphism left right)
    (σ : StrategyProfile left) : StrategyProfile right :=
  fun who => F.stratEquiv who (σ who)

@[simp] theorem mapProfile_apply
    (F : BehavioralStrategyIsomorphism left right)
    (σ : StrategyProfile left) (who : P) :
    F.mapProfile σ who = F.stratEquiv who (σ who) := rfl

/-- Program-level strategy isomorphisms preserve Nash exactly. -/
theorem nash_iff
    (F : BehavioralStrategyIsomorphism left right)
    (σ : StrategyProfile left) :
    IsNash left σ ↔ IsNash right (F.mapProfile σ) := by
  simpa [IsNash, mapProfile] using
    (KernelGame.EUGameIsomorphism.nash_iff F σ)

end BehavioralStrategyIsomorphism

/-! ## Pure transport -/

/-- An EU-preserving pure strategy morphism between two checked Vegas
programs. -/
abbrev PureStrategyMorphism
    [Fintype P] {L₁ L₂ : IExpr}
    (source : WFProgram P L₁) [FiniteDomains source]
    (target : WFProgram P L₂) [FiniteDomains target] : Type :=
  KernelGame.EUMorphism (pureKernelGame source) (pureKernelGame target)

namespace PureStrategyMorphism

variable [Fintype P] {L₁ L₂ : IExpr}
variable {source : WFProgram P L₁} [FiniteDomains source]
variable {target : WFProgram P L₂} [FiniteDomains target]

/-- Map a pure strategy profile along a program-level pure strategy morphism. -/
def mapProfile
    (F : PureStrategyMorphism source target)
    (σ : pureProfileAt source) : pureProfileAt target :=
  fun who => F.stratMap who (σ who)

@[simp] theorem mapProfile_apply
    (F : PureStrategyMorphism source target)
    (σ : pureProfileAt source) (who : P) :
    F.mapProfile σ who = F.stratMap who (σ who) := rfl

/-- Program-level pure morphisms preserve expected utility under mapped
profiles. -/
theorem mapProfile_eu_eq
    (F : PureStrategyMorphism source target)
    (σ : pureProfileAt source) (who : P) :
    (pureKernelGame target).eu (F.mapProfile σ) who =
      (pureKernelGame source).eu σ who :=
  F.eu_preserved σ who

/-- If the mapped target pure profile is Nash, then the source pure profile is
Nash. -/
theorem source_nash_of_target_mapped_nash
    (F : PureStrategyMorphism source target)
    {σ : pureProfileAt source}
    (hN : IsPureNash target (F.mapProfile σ)) :
    IsPureNash source σ := by
  simpa [IsPureNash, mapProfile] using
    (KernelGame.EUMorphism.nash_of_nash F hN)

end PureStrategyMorphism

/-- An EU-preserving pure strategy isomorphism between two checked Vegas
programs. -/
abbrev PureStrategyIsomorphism
    [Fintype P] {L₁ L₂ : IExpr}
    (left : WFProgram P L₁) [FiniteDomains left]
    (right : WFProgram P L₂) [FiniteDomains right] : Type :=
  KernelGame.EUGameIsomorphism (pureKernelGame left) (pureKernelGame right)

namespace PureStrategyIsomorphism

variable [Fintype P] {L₁ L₂ : IExpr}
variable {left : WFProgram P L₁} [FiniteDomains left]
variable {right : WFProgram P L₂} [FiniteDomains right]

/-- Map a pure strategy profile along a program-level pure strategy
isomorphism. -/
def mapProfile
    (F : PureStrategyIsomorphism left right)
    (σ : pureProfileAt left) : pureProfileAt right :=
  fun who => F.stratEquiv who (σ who)

@[simp] theorem mapProfile_apply
    (F : PureStrategyIsomorphism left right)
    (σ : pureProfileAt left) (who : P) :
    F.mapProfile σ who = F.stratEquiv who (σ who) := rfl

/-- Program-level pure strategy isomorphisms preserve Nash exactly. -/
theorem nash_iff
    (F : PureStrategyIsomorphism left right)
    (σ : pureProfileAt left) :
    IsPureNash left σ ↔ IsPureNash right (F.mapProfile σ) := by
  simpa [IsPureNash, mapProfile] using
    (KernelGame.EUGameIsomorphism.nash_iff F σ)

end PureStrategyIsomorphism

end Vegas
