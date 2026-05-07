import Vegas.Strategic.Vocabulary

/-!
# Strategy dominance infrastructure

Generic dominance and repair lemmas for checked Vegas programs. The repair
bundles are intentionally abstract: a nullable compiler, a protocol-specific
sanitizer, or an example-specific strategy transformation can instantiate the
same interface.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## PMF behavioral dominance -/

/-- A Nash profile cannot assign a strategy that is strictly dominated by some
alternative strategy for the same player. -/
theorem IsNash.not_strictly_dominated_strategy
    [Fintype P] {g : WFProgram P L} [FiniteDomains g]
    {σ : StrategyProfile g} (hN : IsNash g σ)
    {who : P} {s : Strategy g who}
    (hdom : StrictlyDominates g who s (σ who)) :
    False := by
  have hnash :
      (pmfBehavioralKernelGame g).eu
          (Function.update σ who s) who ≤
        (pmfBehavioralKernelGame g).eu σ who :=
    hN who s
  have hstrict :
      (pmfBehavioralKernelGame g).eu
          (Function.update σ who s) who >
        (pmfBehavioralKernelGame g).eu σ who := by
    simpa [StrictlyDominates, Function.update_eq_self] using hdom σ
  exact (not_lt_of_ge hnash) hstrict

/-- A Nash profile cannot assign a strategy for which some strictly dominating
alternative exists. -/
theorem IsNash.not_strictly_dominated
    [Fintype P] {g : WFProgram P L} [FiniteDomains g]
    {σ : StrategyProfile g} (hN : IsNash g σ)
    {who : P}
    (hdom : ∃ s : Strategy g who,
      StrictlyDominates g who s (σ who)) :
    False := by
  rcases hdom with ⟨s, hs⟩
  exact IsNash.not_strictly_dominated_strategy hN hs

/-- A generic repair operation that strictly improves every strategy marked
bad. -/
structure StrictDominationRepair
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] (who : P) where
  /-- The strategies ruled out by this repair argument. -/
  Bad : Strategy g who → Prop
  /-- The strategy transformation used to repair a bad strategy. -/
  repair : Strategy g who → Strategy g who
  /-- Repaired strategies are no longer bad. -/
  repaired_not_bad : ∀ s, ¬ Bad (repair s)
  /-- When `s` is bad, the repaired strategy strictly dominates it. -/
  dominates_bad : ∀ s, Bad s → StrictlyDominates g who (repair s) s

namespace StrictDominationRepair

/-- No Nash profile can use a repairably bad strategy. -/
theorem nash_avoids_bad
    [Fintype P] {g : WFProgram P L} [FiniteDomains g]
    {who : P} (R : StrictDominationRepair g who)
    {σ : StrategyProfile g} (hN : IsNash g σ) :
    ¬ R.Bad (σ who) := by
  intro hbad
  exact IsNash.not_strictly_dominated_strategy hN
    (R.dominates_bad (σ who) hbad)

end StrictDominationRepair

/-! ## Pure dominance -/

/-- A pure Nash profile cannot assign a pure strategy that is strictly
dominated by some alternative pure strategy for the same player. -/
theorem IsPureNash.not_strictly_dominated_strategy
    [Fintype P] {g : WFProgram P L} [FiniteDomains g]
    {σ : pureProfileAt g} (hN : IsPureNash g σ)
    {who : P} {s : pureStrategyAt g who}
    (hdom : PureStrictlyDominates g who s (σ who)) :
    False := by
  have hnash :
      (pureKernelGame g).eu
          (Function.update σ who s) who ≤
        (pureKernelGame g).eu σ who :=
    hN who s
  have hstrict :
      (pureKernelGame g).eu
          (Function.update σ who s) who >
        (pureKernelGame g).eu σ who := by
    simpa [PureStrictlyDominates, Function.update_eq_self] using hdom σ
  exact (not_lt_of_ge hnash) hstrict

/-- A pure Nash profile cannot assign a pure strategy for which some strictly
dominating pure alternative exists. -/
theorem IsPureNash.not_strictly_dominated
    [Fintype P] {g : WFProgram P L} [FiniteDomains g]
    {σ : pureProfileAt g} (hN : IsPureNash g σ)
    {who : P}
    (hdom : ∃ s : pureStrategyAt g who,
      PureStrictlyDominates g who s (σ who)) :
    False := by
  rcases hdom with ⟨s, hs⟩
  exact IsPureNash.not_strictly_dominated_strategy hN hs

/-- A generic pure-strategy repair operation that strictly improves every pure
strategy marked bad. -/
structure PureStrictDominationRepair
    [Fintype P] (g : WFProgram P L) [FiniteDomains g] (who : P) where
  /-- The pure strategies ruled out by this repair argument. -/
  Bad : pureStrategyAt g who → Prop
  /-- The pure strategy transformation used to repair a bad strategy. -/
  repair : pureStrategyAt g who → pureStrategyAt g who
  /-- Repaired pure strategies are no longer bad. -/
  repaired_not_bad : ∀ s, ¬ Bad (repair s)
  /-- When `s` is bad, the repaired pure strategy strictly dominates it. -/
  dominates_bad : ∀ s, Bad s → PureStrictlyDominates g who (repair s) s

namespace PureStrictDominationRepair

/-- No pure Nash profile can use a repairably bad pure strategy. -/
theorem nash_avoids_bad
    [Fintype P] {g : WFProgram P L} [FiniteDomains g]
    {who : P} (R : PureStrictDominationRepair g who)
    {σ : pureProfileAt g} (hN : IsPureNash g σ) :
    ¬ R.Bad (σ who) := by
  intro hbad
  exact IsPureNash.not_strictly_dominated_strategy hN
    (R.dominates_bad (σ who) hbad)

end PureStrictDominationRepair

end Vegas
