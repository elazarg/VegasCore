import Vegas.Strategic
import Vegas.Protocol.Strategic
import GameTheory.Concepts.SolutionConcepts
import GameTheory.Core.GameProperties

/-!
# Vegas equilibrium wrappers

Game-theoretic vocabulary for Vegas programs, defined by transport through the
`toKernelGame` strategic bridge. The entire user-facing game-theory API
consumes a `WFProgram` bundle rather than a raw `(program, env,
NormalizedDists)` triplet: the bundle carries the full well-formedness
obligations (`WF`, `NormalizedDists`, `Legal`) needed to ensure a coherent
game interpretation.

The `MachineGame` mirror keeps the same legal strategy spaces but evaluates
outcomes through the checked graph machine. It takes an explicit
`hctx : WFCtx g.Γ` because the machine elaboration carries context
well-formedness separately from `WFProgram`.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

noncomputable def Game (g : WFProgram P L) : GameTheory.KernelGame P :=
  toKernelGame g

/-- Machine-native behavioral kernel game for a checked Vegas program. -/
noncomputable def MachineGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : GameTheory.KernelGame P :=
  toMachineKernelGame g hctx

/-- Strategy profiles for a Vegas program are exactly the profiles of its
kernel-game image. -/
def StrategyProfile (g : WFProgram P L) : Type :=
  KernelGame.Profile (Game g)

/-- Machine-game strategy profiles use the same legal behavioral profiles. -/
def MachineStrategyProfile (g : WFProgram P L) (hctx : WFCtx g.Γ) : Type :=
  KernelGame.Profile (MachineGame g hctx)

/-- A single player's Vegas strategy is the corresponding strategy in the
kernel-game image. -/
def Strategy (g : WFProgram P L) (who : P) : Type :=
  (Game g).Strategy who

/-- A single player's machine-game strategy is the same legal behavioral
strategy, evaluated by the checked graph machine. -/
def MachineStrategy (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) : Type :=
  (MachineGame g hctx).Strategy who

/-- Correlated profiles for a Vegas program are profile distributions on its
strategy-profile space. -/
def CorrelatedProfile (g : WFProgram P L) : Type :=
  PMF (StrategyProfile g)

@[simp] theorem MachineStrategyProfile_eq_StrategyProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    MachineStrategyProfile g hctx = StrategyProfile g := rfl

@[simp] theorem MachineStrategy_eq_Strategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    MachineStrategy g hctx who = Strategy g who := rfl

theorem MachineGame_outcomeKernel_eq_Game
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : StrategyProfile g) :
    (MachineGame g hctx).outcomeKernel σ =
      (Game g).outcomeKernel σ :=
  toMachineKernelGame_outcomeKernel_eq_toKernelGame g hctx σ

theorem MachineGame_eu_eq_Game
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : StrategyProfile g) (who : P) :
    (MachineGame g hctx).eu σ who = (Game g).eu σ who :=
  toMachineKernelGame_eu_eq_toKernelGame g hctx σ who

instance instFintypeGameStrategy (g : WFProgram P L)
    [∀ who, Fintype (Strategy g who)] :
    ∀ who, Fintype ((Game g).Strategy who) := by
  intro who
  let I : Fintype (Strategy g who) := inferInstance
  simpa [Strategy] using I

instance instNonemptyGameStrategy (g : WFProgram P L)
    [∀ who, Nonempty (Strategy g who)] :
    ∀ who, Nonempty ((Game g).Strategy who) := by
  intro who
  let I : Nonempty (Strategy g who) := inferInstance
  simpa [Strategy] using I

instance instFintypeGameProfile (g : WFProgram P L)
    [Fintype (StrategyProfile g)] :
    Fintype (KernelGame.Profile (Game g)) := by
  let I : Fintype (StrategyProfile g) := inferInstance
  simpa [StrategyProfile] using I

instance instNonemptyGameProfile (g : WFProgram P L)
    [Nonempty (StrategyProfile g)] :
    Nonempty (KernelGame.Profile (Game g)) := by
  let I : Nonempty (StrategyProfile g) := inferInstance
  simpa [StrategyProfile] using I

/-- Expected utility for a Vegas strategy profile, via `toKernelGame`. -/
noncomputable def eu (g : WFProgram P L)
    (σ : StrategyProfile g) (who : P) : ℝ :=
  (Game g).eu σ who

/-- Expected utility for a Vegas strategy profile through the checked graph
machine. -/
noncomputable def machineEu (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : MachineStrategyProfile g hctx) (who : P) : ℝ :=
  (MachineGame g hctx).eu σ who

@[simp] theorem machineEu_eq_eu (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : StrategyProfile g) (who : P) :
    machineEu g hctx σ who = eu g σ who := by
  simp [machineEu, MachineGame, eu, Game,
    toMachineKernelGame_eu_eq_toKernelGame]

/-- Correlated expected utility for a Vegas correlated profile, via
`toKernelGame`. -/
noncomputable def correlatedEu (g : WFProgram P L)
    (μ : CorrelatedProfile g) (who : P) : ℝ :=
  (Game g).correlatedEu μ who

/-- EU weak preference on Vegas outcome distributions. -/
def euPref (g : WFProgram P L) :
    P → PMF (Outcome P) → PMF (Outcome P) → Prop :=
  (Game g).euPref

/-- EU strict preference on Vegas outcome distributions. -/
def euStrictPref (g : WFProgram P L) :
    P → PMF (Outcome P) → PMF (Outcome P) → Prop :=
  (Game g).euStrictPref

/-- Nash equilibrium for a Vegas program, via `toKernelGame`. -/
def IsNash (g : WFProgram P L) (σ : StrategyProfile g) : Prop :=
  (Game g).IsNash σ

/-- Nash equilibrium for a Vegas program through the checked graph machine. -/
def MachineIsNash (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : MachineStrategyProfile g hctx) : Prop :=
  (MachineGame g hctx).IsNash σ

theorem machineIsNash_iff_isNash
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : StrategyProfile g) :
    MachineIsNash g hctx σ ↔ IsNash g σ := by
  constructor
  · intro h who s'
    have h' := h who s'
    simpa [MachineIsNash, IsNash, MachineGame, Game,
      GameTheory.KernelGame.IsNash,
      toMachineKernelGame_eu_eq_toKernelGame] using h'
  · intro h who s'
    have h' := h who s'
    simpa [MachineIsNash, IsNash, MachineGame, Game,
      GameTheory.KernelGame.IsNash,
      toMachineKernelGame_eu_eq_toKernelGame] using h'

/-- Preference-parameterized Nash equilibrium for a Vegas program. -/
def IsNashFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile g) : Prop :=
  (Game g).IsNashFor pref σ

/-- Best response for a player in a Vegas program. -/
def IsBestResponse (g : WFProgram P L)
    (who : P) (σ : StrategyProfile g) (s : Strategy g who) : Prop :=
  (Game g).IsBestResponse who σ s

/-- Best response through the checked graph machine. -/
def MachineIsBestResponse (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : MachineStrategyProfile g hctx)
    (s : MachineStrategy g hctx who) : Prop :=
  (MachineGame g hctx).IsBestResponse who σ s

theorem machineIsBestResponse_iff_isBestResponse
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : StrategyProfile g) (s : Strategy g who) :
    MachineIsBestResponse g hctx who σ s ↔
      IsBestResponse g who σ s := by
  constructor
  · intro h s'
    have h' := h s'
    simpa [MachineIsBestResponse, IsBestResponse, MachineGame, Game,
      GameTheory.KernelGame.IsBestResponse,
      toMachineKernelGame_eu_eq_toKernelGame] using h'
  · intro h s'
    have h' := h s'
    simpa [MachineIsBestResponse, IsBestResponse, MachineGame, Game,
      GameTheory.KernelGame.IsBestResponse,
      toMachineKernelGame_eu_eq_toKernelGame] using h'

/-- Preference-parameterized best response for a player in a Vegas program. -/
def IsBestResponseFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (σ : StrategyProfile g) (s : Strategy g who) : Prop :=
  (Game g).IsBestResponseFor pref who σ s

/-- Dominant strategy for a player in a Vegas program. -/
def IsDominant (g : WFProgram P L) (who : P) (s : Strategy g who) : Prop :=
  (Game g).IsDominant who s

/-- Dominant strategy through the checked graph machine. -/
def MachineIsDominant (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (s : MachineStrategy g hctx who) : Prop :=
  (MachineGame g hctx).IsDominant who s

theorem machineIsDominant_iff_isDominant
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (s : Strategy g who) :
    MachineIsDominant g hctx who s ↔ IsDominant g who s := by
  constructor
  · intro h σ s'
    have h' := h σ s'
    simpa [MachineIsDominant, IsDominant, MachineGame, Game,
      GameTheory.KernelGame.IsDominant,
      toMachineKernelGame_eu_eq_toKernelGame] using h'
  · intro h σ s'
    have h' := h σ s'
    simpa [MachineIsDominant, IsDominant, MachineGame, Game,
      GameTheory.KernelGame.IsDominant,
      toMachineKernelGame_eu_eq_toKernelGame] using h'

/-- Preference-parameterized dominant strategy for a player in a Vegas program. -/
def IsDominantFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s : Strategy g who) : Prop :=
  (Game g).IsDominantFor pref who s

/-- Strict Nash equilibrium for a Vegas program. -/
def IsStrictNash (g : WFProgram P L) (σ : StrategyProfile g) : Prop :=
  (Game g).IsStrictNash σ

/-- Strict Nash equilibrium through the checked graph machine. -/
def MachineIsStrictNash (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : MachineStrategyProfile g hctx) : Prop :=
  (MachineGame g hctx).IsStrictNash σ

theorem machineIsStrictNash_iff_isStrictNash
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : StrategyProfile g) :
    MachineIsStrictNash g hctx σ ↔ IsStrictNash g σ := by
  constructor
  · intro h who s' hs'
    have h' := h who s' hs'
    simpa [MachineIsStrictNash, IsStrictNash, MachineGame, Game,
      GameTheory.KernelGame.IsStrictNash,
      toMachineKernelGame_eu_eq_toKernelGame] using h'
  · intro h who s' hs'
    have h' := h who s' hs'
    simpa [MachineIsStrictNash, IsStrictNash, MachineGame, Game,
      GameTheory.KernelGame.IsStrictNash,
      toMachineKernelGame_eu_eq_toKernelGame] using h'

/-- Preference-parameterized strict Nash equilibrium for a Vegas program. -/
def IsStrictNashFor (g : WFProgram P L)
    (spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile g) : Prop :=
  (Game g).IsStrictNashFor spref σ

/-- Strictly dominant strategy for a player in a Vegas program. -/
def IsStrictDominant (g : WFProgram P L)
    (who : P) (s : Strategy g who) : Prop :=
  (Game g).IsStrictDominant who s

/-- Strictly dominant strategy through the checked graph machine. -/
def MachineIsStrictDominant (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (s : MachineStrategy g hctx who) : Prop :=
  (MachineGame g hctx).IsStrictDominant who s

theorem machineIsStrictDominant_iff_isStrictDominant
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (s : Strategy g who) :
    MachineIsStrictDominant g hctx who s ↔
      IsStrictDominant g who s := by
  constructor
  · intro h σ s' hs'
    have h' := h σ s' hs'
    simpa [MachineIsStrictDominant, IsStrictDominant, MachineGame, Game,
      GameTheory.KernelGame.IsStrictDominant,
      toMachineKernelGame_eu_eq_toKernelGame] using h'
  · intro h σ s' hs'
    have h' := h σ s' hs'
    simpa [MachineIsStrictDominant, IsStrictDominant, MachineGame, Game,
      GameTheory.KernelGame.IsStrictDominant,
      toMachineKernelGame_eu_eq_toKernelGame] using h'

/-- Preference-parameterized strictly dominant strategy for a Vegas player. -/
def IsStrictDominantFor (g : WFProgram P L)
    (spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s : Strategy g who) : Prop :=
  (Game g).IsStrictDominantFor spref who s

/-- Weak dominance between two Vegas strategies for one player. -/
def WeaklyDominates (g : WFProgram P L)
    (who : P) (s t : Strategy g who) : Prop :=
  (Game g).WeaklyDominates who s t

/-- Weak dominance through the checked graph machine. -/
def MachineWeaklyDominates (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (s t : MachineStrategy g hctx who) : Prop :=
  (MachineGame g hctx).WeaklyDominates who s t

theorem machineWeaklyDominates_iff_weaklyDominates
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (s t : Strategy g who) :
    MachineWeaklyDominates g hctx who s t ↔
      WeaklyDominates g who s t := by
  constructor
  · intro h σ
    have h' := h σ
    simpa [MachineWeaklyDominates, WeaklyDominates, MachineGame, Game,
      GameTheory.KernelGame.WeaklyDominates,
      toMachineKernelGame_eu_eq_toKernelGame] using h'
  · intro h σ
    have h' := h σ
    simpa [MachineWeaklyDominates, WeaklyDominates, MachineGame, Game,
      GameTheory.KernelGame.WeaklyDominates,
      toMachineKernelGame_eu_eq_toKernelGame] using h'

/-- Preference-parameterized weak dominance between two Vegas strategies. -/
def WeaklyDominatesFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s t : Strategy g who) : Prop :=
  (Game g).WeaklyDominatesFor pref who s t

/-- Strict dominance between two Vegas strategies for one player. -/
def StrictlyDominates (g : WFProgram P L)
    (who : P) (s t : Strategy g who) : Prop :=
  (Game g).StrictlyDominates who s t

/-- Strict dominance through the checked graph machine. -/
def MachineStrictlyDominates (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (s t : MachineStrategy g hctx who) : Prop :=
  (MachineGame g hctx).StrictlyDominates who s t

theorem machineStrictlyDominates_iff_strictlyDominates
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (s t : Strategy g who) :
    MachineStrictlyDominates g hctx who s t ↔
      StrictlyDominates g who s t := by
  constructor
  · intro h σ
    have h' := h σ
    simpa [MachineStrictlyDominates, StrictlyDominates, MachineGame, Game,
      GameTheory.KernelGame.StrictlyDominates,
      toMachineKernelGame_eu_eq_toKernelGame] using h'
  · intro h σ
    have h' := h σ
    simpa [MachineStrictlyDominates, StrictlyDominates, MachineGame, Game,
      GameTheory.KernelGame.StrictlyDominates,
      toMachineKernelGame_eu_eq_toKernelGame] using h'

/-- Preference-parameterized strict dominance between two Vegas strategies. -/
def StrictlyDominatesFor (g : WFProgram P L)
    (spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (who : P) (s t : Strategy g who) : Prop :=
  (Game g).StrictlyDominatesFor spref who s t

/-- Pareto dominance for Vegas strategy profiles. -/
def ParetoDominates (g : WFProgram P L) (σ τ : StrategyProfile g) : Prop :=
  (Game g).ParetoDominates σ τ

/-- Pareto dominance through the checked graph machine. -/
def MachineParetoDominates (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ τ : MachineStrategyProfile g hctx) : Prop :=
  (MachineGame g hctx).ParetoDominates σ τ

theorem machineParetoDominates_iff_paretoDominates
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ τ : StrategyProfile g) :
    MachineParetoDominates g hctx σ τ ↔ ParetoDominates g σ τ := by
  unfold MachineParetoDominates ParetoDominates MachineGame Game
  simp [GameTheory.KernelGame.ParetoDominates,
    toMachineKernelGame_eu_eq_toKernelGame]

/-- Preference-parameterized Pareto dominance for Vegas strategy profiles. -/
def ParetoDominatesFor (g : WFProgram P L)
    (pref spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ τ : StrategyProfile g) : Prop :=
  (Game g).ParetoDominatesFor pref spref σ τ

/-- Pareto efficiency for Vegas strategy profiles. -/
def IsParetoEfficient (g : WFProgram P L) (σ : StrategyProfile g) : Prop :=
  (Game g).IsParetoEfficient σ

/-- Pareto efficiency through the checked graph machine. -/
def MachineIsParetoEfficient (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : MachineStrategyProfile g hctx) : Prop :=
  (MachineGame g hctx).IsParetoEfficient σ

theorem machineIsParetoEfficient_iff_isParetoEfficient
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : StrategyProfile g) :
    MachineIsParetoEfficient g hctx σ ↔ IsParetoEfficient g σ := by
  constructor
  · intro h hlegacy
    rcases hlegacy with ⟨τ, hτ⟩
    exact h ⟨τ,
      (machineParetoDominates_iff_paretoDominates g hctx τ σ).2 hτ⟩
  · intro h hmachine
    rcases hmachine with ⟨τ, hτ⟩
    exact h ⟨τ,
      (machineParetoDominates_iff_paretoDominates g hctx τ σ).1 hτ⟩

/-- Preference-parameterized Pareto efficiency for Vegas strategy profiles. -/
def IsParetoEfficientFor (g : WFProgram P L)
    (pref spref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (σ : StrategyProfile g) : Prop :=
  (Game g).IsParetoEfficientFor pref spref σ

/-- Social welfare of a Vegas strategy profile, via `toKernelGame`. -/
noncomputable def socialWelfare [Fintype P] (g : WFProgram P L)
    (σ : StrategyProfile g) : ℝ :=
  (Game g).socialWelfare σ

/-- Social welfare through the checked graph machine. -/
noncomputable def machineSocialWelfare [Fintype P]
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : MachineStrategyProfile g hctx) : ℝ :=
  (MachineGame g hctx).socialWelfare σ

@[simp] theorem machineSocialWelfare_eq_socialWelfare
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : StrategyProfile g) :
    machineSocialWelfare g hctx σ = socialWelfare g σ := by
  unfold machineSocialWelfare socialWelfare MachineGame Game
  simp [GameTheory.KernelGame.socialWelfare,
    toMachineKernelGame_eu_eq_toKernelGame]

/-- Correlated equilibrium for a Vegas correlated profile. -/
def IsCorrelatedEq (g : WFProgram P L) (μ : CorrelatedProfile g) : Prop :=
  (Game g).IsCorrelatedEq μ

/-- Coarse correlated equilibrium for a Vegas correlated profile. -/
def IsCoarseCorrelatedEq (g : WFProgram P L) (μ : CorrelatedProfile g) : Prop :=
  (Game g).IsCoarseCorrelatedEq μ

/-- Preference-parameterized correlated equilibrium for a Vegas correlated
profile. -/
def IsCorrelatedEqFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (μ : CorrelatedProfile g) : Prop :=
  (Game g).IsCorrelatedEqFor pref μ

/-- Preference-parameterized coarse correlated equilibrium for a Vegas
correlated profile. -/
def IsCoarseCorrelatedEqFor (g : WFProgram P L)
    (pref : P → PMF (Outcome P) → PMF (Outcome P) → Prop)
    (μ : CorrelatedProfile g) : Prop :=
  (Game g).IsCoarseCorrelatedEqFor pref μ

end Vegas
