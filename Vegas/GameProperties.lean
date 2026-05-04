import Vegas.Equilibrium
import GameTheory.Concepts.ApproximateNash
import GameTheory.Concepts.DominanceSolvability
import GameTheory.Concepts.Rationalizability
import GameTheory.Concepts.SecurityStrategy
import GameTheory.Concepts.Minimax
import GameTheory.Concepts.PriceOfAnarchy

/-!
# Vegas game-theoretic properties

Core game-theoretic property definitions for Vegas programs, transported through
the local `toKernelGame` bridge. All declarations consume a `WFProgram` bundle.

Corollaries and derived theorems live under `Vegas/Corollaries/`.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

def IsεNash (g : WFProgram P L) (ε : ℝ) (σ : StrategyProfile g) : Prop :=
  (Game g).IsεNash ε σ

def MachineIsεNash (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (ε : ℝ) (σ : MachineStrategyProfile g hctx) : Prop :=
  (MachineGame g hctx).IsεNash ε σ

theorem machineIsεNash_iff_isεNash
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (ε : ℝ) (σ : StrategyProfile g) :
    MachineIsεNash g hctx ε σ ↔ IsεNash g ε σ := by
  constructor
  · intro h who s'
    have h' := h who s'
    simpa [MachineIsεNash, IsεNash, MachineGame, Game,
      GameTheory.KernelGame.IsεNash,
      toMachineKernelGame_eu_eq_toKernelGame] using h'
  · intro h who s'
    have h' := h who s'
    simpa [MachineIsεNash, IsεNash, MachineGame, Game,
      GameTheory.KernelGame.IsεNash,
      toMachineKernelGame_eu_eq_toKernelGame] using h'

def IsεBestResponse (g : WFProgram P L)
    (ε : ℝ) (who : P) (σ : StrategyProfile g) (s : Strategy g who) : Prop :=
  (Game g).IsεBestResponse ε who σ s

def MachineIsεBestResponse (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (ε : ℝ) (who : P) (σ : MachineStrategyProfile g hctx)
    (s : MachineStrategy g hctx who) : Prop :=
  (MachineGame g hctx).IsεBestResponse ε who σ s

theorem machineIsεBestResponse_iff_isεBestResponse
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (ε : ℝ) (who : P) (σ : StrategyProfile g) (s : Strategy g who) :
    MachineIsεBestResponse g hctx ε who σ s ↔
      IsεBestResponse g ε who σ s := by
  constructor
  · intro h s'
    have h' := h s'
    simpa [MachineIsεBestResponse, IsεBestResponse, MachineGame, Game,
      GameTheory.KernelGame.IsεBestResponse,
      toMachineKernelGame_eu_eq_toKernelGame] using h'
  · intro h s'
    have h' := h s'
    simpa [MachineIsεBestResponse, IsεBestResponse, MachineGame, Game,
      GameTheory.KernelGame.IsεBestResponse,
      toMachineKernelGame_eu_eq_toKernelGame] using h'

def Survives (g : WFProgram P L) (n : ℕ) (who : P)
    (s : Strategy g who) : Prop :=
  (Game g).Survives n who s

def IsRationalizable (g : WFProgram P L) (who : P)
    (s : Strategy g who) : Prop :=
  (Game g).IsRationalizable who s

def IsIndividuallyRational (g : WFProgram P L)
    (r : P → ℝ) (σ : StrategyProfile g) : Prop :=
  (Game g).IsIndividuallyRational r σ

def MachineIsIndividuallyRational
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (r : P → ℝ) (σ : MachineStrategyProfile g hctx) : Prop :=
  (MachineGame g hctx).IsIndividuallyRational r σ

theorem machineIsIndividuallyRational_iff_isIndividuallyRational
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (r : P → ℝ) (σ : StrategyProfile g) :
    MachineIsIndividuallyRational g hctx r σ ↔
      IsIndividuallyRational g r σ := by
  unfold MachineIsIndividuallyRational IsIndividuallyRational MachineGame Game
  simp [GameTheory.KernelGame.IsIndividuallyRational,
    toMachineKernelGame_eu_eq_toKernelGame]

def IsDominanceSolvable (g : WFProgram P L) : Prop :=
  (Game g).IsDominanceSolvable

noncomputable def IsDominanceSolvable.dominantProfile
    (g : WFProgram P L)
    (h : IsDominanceSolvable g) : StrategyProfile g :=
  KernelGame.IsDominanceSolvable.dominantProfile (G := Game g) h

def IsExactPotential (g : WFProgram P L)
    (Φ : StrategyProfile g → ℝ) : Prop :=
  (Game g).IsExactPotential Φ

def MachineIsExactPotential (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (Φ : MachineStrategyProfile g hctx → ℝ) : Prop :=
  (MachineGame g hctx).IsExactPotential Φ

theorem machineIsExactPotential_iff_isExactPotential
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (Φ : StrategyProfile g → ℝ) :
    MachineIsExactPotential g hctx Φ ↔ IsExactPotential g Φ := by
  constructor
  · intro h who σ s'
    have h' := h who σ s'
    simpa [MachineIsExactPotential, IsExactPotential, MachineGame, Game,
      GameTheory.KernelGame.IsExactPotential,
      toMachineKernelGame_eu_eq_toKernelGame] using h'
  · intro h who σ s'
    have h' := h who σ s'
    simpa [MachineIsExactPotential, IsExactPotential, MachineGame, Game,
      GameTheory.KernelGame.IsExactPotential,
      toMachineKernelGame_eu_eq_toKernelGame] using h'

def IsOrdinalPotential (g : WFProgram P L)
    (Φ : StrategyProfile g → ℝ) : Prop :=
  (Game g).IsOrdinalPotential Φ

def MachineIsOrdinalPotential (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (Φ : MachineStrategyProfile g hctx → ℝ) : Prop :=
  (MachineGame g hctx).IsOrdinalPotential Φ

theorem machineIsOrdinalPotential_iff_isOrdinalPotential
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (Φ : StrategyProfile g → ℝ) :
    MachineIsOrdinalPotential g hctx Φ ↔ IsOrdinalPotential g Φ := by
  constructor
  · intro h who σ s'
    have h' := h who σ s'
    simpa [MachineIsOrdinalPotential, IsOrdinalPotential, MachineGame, Game,
      GameTheory.KernelGame.IsOrdinalPotential,
      toMachineKernelGame_eu_eq_toKernelGame] using h'
  · intro h who σ s'
    have h' := h who σ s'
    simpa [MachineIsOrdinalPotential, IsOrdinalPotential, MachineGame, Game,
      GameTheory.KernelGame.IsOrdinalPotential,
      toMachineKernelGame_eu_eq_toKernelGame] using h'

def Guarantees (g : WFProgram P L)
    (who : P) (s : Strategy g who) (v : ℝ) : Prop :=
  (Game g).Guarantees who s v

def MachineGuarantees (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (s : MachineStrategy g hctx who) (v : ℝ) : Prop :=
  (MachineGame g hctx).Guarantees who s v

theorem machineGuarantees_iff_guarantees
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (s : Strategy g who) (v : ℝ) :
    MachineGuarantees g hctx who s v ↔ Guarantees g who s v := by
  constructor
  · intro h σ
    have h' := h σ
    simpa [MachineGuarantees, Guarantees, MachineGame, Game,
      GameTheory.KernelGame.Guarantees,
      toMachineKernelGame_eu_eq_toKernelGame] using h'
  · intro h σ
    have h' := h σ
    simpa [MachineGuarantees, Guarantees, MachineGame, Game,
      GameTheory.KernelGame.Guarantees,
      toMachineKernelGame_eu_eq_toKernelGame] using h'

def IsSaddlePoint
    (g : WFProgram (Fin 2) L)
    (σ : StrategyProfile g) : Prop :=
  (Game g).IsSaddlePoint σ

def MachineIsSaddlePoint
    (g : WFProgram (Fin 2) L) (hctx : WFCtx g.Γ)
    (σ : MachineStrategyProfile g hctx) : Prop :=
  (MachineGame g hctx).IsSaddlePoint σ

theorem machineIsSaddlePoint_iff_isSaddlePoint
    (g : WFProgram (Fin 2) L) (hctx : WFCtx g.Γ)
    (σ : StrategyProfile g) :
    MachineIsSaddlePoint g hctx σ ↔ IsSaddlePoint g σ := by
  constructor
  · intro h
    constructor
    · intro s0
      have h' := h.1 s0
      simpa [MachineIsSaddlePoint, IsSaddlePoint, MachineGame, Game,
        GameTheory.KernelGame.IsSaddlePoint,
        toMachineKernelGame_eu_eq_toKernelGame] using h'
    · intro s1
      have h' := h.2 s1
      simpa [MachineIsSaddlePoint, IsSaddlePoint, MachineGame, Game,
        GameTheory.KernelGame.IsSaddlePoint,
        toMachineKernelGame_eu_eq_toKernelGame] using h'
  · intro h
    constructor
    · intro s0
      have h' := h.1 s0
      simpa [MachineIsSaddlePoint, IsSaddlePoint, MachineGame, Game,
        GameTheory.KernelGame.IsSaddlePoint,
        toMachineKernelGame_eu_eq_toKernelGame] using h'
    · intro s1
      have h' := h.2 s1
      simpa [MachineIsSaddlePoint, IsSaddlePoint, MachineGame, Game,
        GameTheory.KernelGame.IsSaddlePoint,
        toMachineKernelGame_eu_eq_toKernelGame] using h'

def MixedStrategy (g : WFProgram P L) (who : P) : Type :=
  PMF (Strategy g who)

def MixedStrategyProfile [Fintype P] (g : WFProgram P L)
    [∀ who, Fintype (Strategy g who)] : Type :=
  KernelGame.Profile (Game g).mixedExtension

def IsMixedNash [Fintype P] (g : WFProgram P L)
    [∀ who, Fintype (Strategy g who)]
    (σ : MixedStrategyProfile g) : Prop :=
  (Game g).mixedExtension.IsNash σ

noncomputable def mixedEu [Fintype P] (g : WFProgram P L)
    [∀ who, Fintype (Strategy g who)]
    (σ : MixedStrategyProfile g) (who : P) : ℝ :=
  (Game g).mixedExtension.eu σ who

noncomputable def worstCaseEU (g : WFProgram P L)
    [Fintype (StrategyProfile g)]
    [∀ who, Fintype (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    [Nonempty (StrategyProfile g)]
    (who : P) (s : Strategy g who) : ℝ :=
  (Game g).worstCaseEU who s

noncomputable def securityLevel (g : WFProgram P L)
    [Fintype (StrategyProfile g)]
    [∀ who, Fintype (Strategy g who)]
    [∀ who, Nonempty (Strategy g who)]
    [Nonempty (StrategyProfile g)]
    (who : P) : ℝ :=
  (Game g).securityLevel who

def IsConstantSum [Fintype P] (g : WFProgram P L) (c : ℝ) : Prop :=
  (Game g).IsConstantSum c

def MachineIsConstantSum [Fintype P]
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (c : ℝ) : Prop :=
  (MachineGame g hctx).IsConstantSum c

theorem machineIsConstantSum_iff_isConstantSum
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ) (c : ℝ) :
    MachineIsConstantSum g hctx c ↔ IsConstantSum g c := by
  unfold MachineIsConstantSum IsConstantSum MachineGame Game
  simp [GameTheory.KernelGame.IsConstantSum, toMachineKernelGame,
    toKernelGame]

def IsZeroSum [Fintype P] (g : WFProgram P L) : Prop :=
  (Game g).IsZeroSum

def MachineIsZeroSum [Fintype P]
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : Prop :=
  (MachineGame g hctx).IsZeroSum

theorem machineIsZeroSum_iff_isZeroSum
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    MachineIsZeroSum g hctx ↔ IsZeroSum g := by
  unfold MachineIsZeroSum IsZeroSum GameTheory.KernelGame.IsZeroSum
  exact machineIsConstantSum_iff_isConstantSum g hctx 0

def IsTeamGame [Fintype P] (g : WFProgram P L) : Prop :=
  (Game g).IsTeamGame

def MachineIsTeamGame [Fintype P]
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : Prop :=
  (MachineGame g hctx).IsTeamGame

theorem machineIsTeamGame_iff_isTeamGame
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    MachineIsTeamGame g hctx ↔ IsTeamGame g := by
  unfold MachineIsTeamGame IsTeamGame MachineGame Game
  simp [GameTheory.KernelGame.IsTeamGame, toMachineKernelGame,
    toKernelGame]

noncomputable def optimalWelfare [Fintype P] (g : WFProgram P L) : ℝ :=
  (Game g).optimalWelfare

noncomputable def bestNashWelfare [Fintype P] (g : WFProgram P L)
    [Fintype (StrategyProfile g)] [Nonempty (StrategyProfile g)]
    (hN : ∃ σ : StrategyProfile g, IsNash g σ) : ℝ :=
  (Game g).bestNashWelfare <| by
    simpa [IsNash] using hN

noncomputable def worstNashWelfare [Fintype P] (g : WFProgram P L)
    [Fintype (StrategyProfile g)] [Nonempty (StrategyProfile g)]
    (hN : ∃ σ : StrategyProfile g, IsNash g σ) : ℝ :=
  (Game g).worstNashWelfare <| by
    simpa [IsNash] using hN

end Vegas
