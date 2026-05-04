import Vegas.Equilibrium
import Vegas.FOSG
import Vegas.PureStrategic
import Vegas.StrategicPMF
import Vegas.Protocol.StrategicCompatibility

/-!
# Protocol-native semantics for Vegas

This file records protocol-facing solution-concept names and realization
targets against the machine-backed public strategic kernels.
The purpose is to make the protocol picture explicit in-tree: what a
Vegas Nash equilibrium *means* at the protocol level is exactly the
statement of `ProtocolNash`, and the existing `Vegas.IsNash` (defined
via `KernelGame`) is shown to be literally the same proposition.

The file has two regions.

* **Region A (protocol-native definitions, proved).**
  `protocolEU`, `ProtocolNash`, `ProtocolBestResponse`,
  `ProtocolDominant`, `ProtocolStrictNash`. These are defined directly
  on `FeasibleProgramBehavioralProfile` / `...Strategy`, with the guard-
  legality constraint carried by the subtype. Correspondence theorems
  (`isNash_iff_protocolNash`, etc.) prove each equals its
  `KernelGame`-transported counterpart by definitional unfolding.

* **Region B (realization theorems and named targets).**
  `SequentialKuhnPMF g hctx LF : Prop` is the proved finite
  machine-derived sequential realization claim: every independent mixed
  profile over legal pure strategies is outcome-equivalent to a reachable PMF
  behavioural profile for `FOSGBridge.toFiniteFOSG`. The PMF target is
  essential: arbitrary mixed pure profiles can induce real-valued behavioural
  probabilities, while the original `FDist` behavioural game is rational-valued.
  `ReachableKuhnPMF g hctx LF : Prop` is the
  observed-adapter reachable strategy-space version used by the syntax-facing
  projection route.
  `ProtocolRationalMixedPureRealizationProperty g : Prop` is the corresponding
  FDist-valued target for rational behavioural witnesses.
  `ProtocolCorrelatedPureRealizationPropertyPMF g : Prop` is the stronger
  correlated variant over arbitrary PMFs on joint pure profiles.
-/

namespace Vegas

open GameTheory
open FOSGBridge

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## Region A — protocol-native solution concepts -/

/-- Protocol-level expected utility: the public machine-backed kernel game's
expected utility for player `i`. -/
noncomputable def protocolEU (g : WFProgram P L)
    (σ : FeasibleProgramBehavioralProfile g) (i : P) : ℝ :=
  (behavioralKernelGame g).eu σ i

@[simp] theorem behavioralKernelGame_eu_eq_protocolEU (g : WFProgram P L)
    (σ : FeasibleProgramBehavioralProfile g) (i : P) :
    (behavioralKernelGame g).eu σ i = protocolEU g σ i := by
  rfl

@[simp] theorem Game_eu_eq_protocolEU (g : WFProgram P L)
    (σ : StrategyProfile g) (i : P) :
    (Game g).eu σ i = protocolEU g σ i := by
  unfold Game
  exact behavioralKernelGame_eu_eq_protocolEU g σ i

@[simp] theorem eu_eq_protocolEU (g : WFProgram P L)
    (σ : StrategyProfile g) (i : P) :
    Vegas.eu g σ i = protocolEU g σ i := by
  simp [eu]

/-- Protocol-level Nash equilibrium: no player can improve their
protocol-level expected utility by a unilateral deviation within
the guard-legal strategy space. -/
def ProtocolNash (g : WFProgram P L)
    (σ : FeasibleProgramBehavioralProfile g) : Prop :=
  ∀ (who : P) (s' : FeasibleProgramBehavioralStrategy g who),
    protocolEU g σ who ≥ protocolEU g (Function.update σ who s') who

theorem isNash_iff_protocolNash (g : WFProgram P L)
    (σ : StrategyProfile g) :
    Vegas.IsNash g σ ↔ ProtocolNash g σ := by
  unfold Vegas.IsNash ProtocolNash
  simp only [KernelGame.IsNash, ge_iff_le]
  constructor
  · intro h who s'
    have := h who s'
    simpa using this
  · intro h who s'
    have := h who s'
    simpa using this

/-- Protocol-level best response: `s` maximises player `who`'s
protocol-level expected utility among all legal deviations, holding
opponents' strategies in `σ` fixed. -/
def ProtocolBestResponse (g : WFProgram P L)
    (who : P) (σ : FeasibleProgramBehavioralProfile g)
    (s : FeasibleProgramBehavioralStrategy g who) : Prop :=
  ∀ (s' : FeasibleProgramBehavioralStrategy g who),
    protocolEU g (Function.update σ who s) who ≥
      protocolEU g (Function.update σ who s') who

theorem isBestResponse_iff_protocolBestResponse (g : WFProgram P L)
    (who : P) (σ : StrategyProfile g) (s : Strategy g who) :
    Vegas.IsBestResponse g who σ s ↔ ProtocolBestResponse g who σ s := by
  unfold Vegas.IsBestResponse ProtocolBestResponse
  simp only [KernelGame.IsBestResponse, ge_iff_le]
  constructor
  · intro h s'
    have := h s'
    simpa [Strategy, StrategyProfile] using this
  · intro h s'
    have := h s'
    simpa [Strategy, StrategyProfile] using this

/-- Protocol-level dominant strategy: `s` is at least as good as any
legal alternative, for player `who`, at every legal profile of
opponents. -/
def ProtocolDominant (g : WFProgram P L)
    (who : P) (s : FeasibleProgramBehavioralStrategy g who) : Prop :=
  ∀ (σ : FeasibleProgramBehavioralProfile g)
    (s' : FeasibleProgramBehavioralStrategy g who),
    protocolEU g (Function.update σ who s) who ≥
      protocolEU g (Function.update σ who s') who

theorem isDominant_iff_protocolDominant (g : WFProgram P L)
    (who : P) (s : Strategy g who) :
    Vegas.IsDominant g who s ↔ ProtocolDominant g who s := by
  unfold Vegas.IsDominant ProtocolDominant
  simp only [KernelGame.IsDominant, ge_iff_le]
  constructor
  · intro h σ s'
    have := h σ s'
    simpa [Strategy, StrategyProfile] using this
  · intro h σ s'
    have := h σ s'
    simpa [Strategy, StrategyProfile] using this

/-- Protocol-level strict Nash equilibrium: every legal unilateral
deviation strictly decreases the deviator's protocol-level expected
utility. -/
def ProtocolStrictNash (g : WFProgram P L)
    (σ : FeasibleProgramBehavioralProfile g) : Prop :=
  ∀ (who : P) (s' : FeasibleProgramBehavioralStrategy g who), s' ≠ σ who →
    protocolEU g σ who > protocolEU g (Function.update σ who s') who

theorem isStrictNash_iff_protocolStrictNash (g : WFProgram P L)
    (σ : StrategyProfile g) :
    Vegas.IsStrictNash g σ ↔ ProtocolStrictNash g σ := by
  unfold Vegas.IsStrictNash ProtocolStrictNash
  simp only [KernelGame.IsStrictNash]
  constructor
  · intro h who s' hne
    have := h who s' hne
    simpa [Strategy, StrategyProfile] using this
  · intro h who s' hne
    have := h who s' hne
    simpa [Strategy, StrategyProfile] using this

/-! ## Region B — named realization targets -/

/-- The protocol-level Kuhn property for a concrete finite Vegas program:
every independent mixed profile over guard-legal pure strategies admits a
reachable PMF behavioural profile in the syntax-horizon machine-derived FOSG
with the same outcome distribution. -/
def SequentialKuhnPMF [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L) : Prop :=
  ∀ (μ : ∀ who, PMF (FeasibleProgramPureStrategy g who)),
    letI : ∀ who, Fintype (FeasibleProgramPureStrategy g who) :=
      fun who => FeasibleProgramPureStrategy.instFintype g LF who
    ∃ β : SequentialBehavioralProfilePMF g hctx,
      sequentialOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (pureKernelGameAt g hctx).outcomeKernel σ)

/-- Mixed-to-behavioral realization for concrete finite Vegas programs in the
machine-derived sequential strategy space. -/
theorem mixedPureRealization_sequential_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (FeasibleProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (FeasibleProgramPureStrategy g who) :=
      fun who => FeasibleProgramPureStrategy.instFintype g LF who
    ∃ β : SequentialBehavioralProfilePMF g hctx,
      sequentialOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (pureKernelGameAt g hctx).outcomeKernel σ) := by
  exact sequential_mixedPure_realizedByBehavioralPMF_finite
    g hctx LF μ

/-- Concrete finite sequential-strategy realization theorem. -/
theorem sequentialKuhnPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L) :
    SequentialKuhnPMF g hctx LF := by
  intro μ
  exact mixedPureRealization_sequential_finite
    g hctx LF μ

/-- The protocol-level Kuhn property for a concrete finite Vegas program:
every independent mixed profile over guard-legal pure strategies admits a
reachable PMF behavioural profile of the observed adapter with the same
outcome distribution.

The PMF target is part of the mathematical statement. Vegas' `FDist`
behavioural strategies have rational weights, so they cannot represent all
behavioural probabilities induced by arbitrary `PMF` mixtures over pure
strategies. The behavioral witness is indexed only by reachable observed
program histories and is retained only as a syntax-facing projection target. -/
def ReachableKuhnPMF [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L) : Prop :=
  ∀ (μ : ∀ who, PMF (FeasibleProgramPureStrategy g who)),
    letI : ∀ who, Fintype (FeasibleProgramPureStrategy g who) :=
      fun who => FeasibleProgramPureStrategy.instFintype g LF who
    ∃ β : ReachableProgramBehavioralProfilePMF g hctx,
      reachableProgramOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (pureKernelGameAt g hctx).outcomeKernel σ)

/-- Reachable mixed-to-behavioral realization for concrete finite Vegas
programs. The witness is not a total strategy. -/
theorem mixedPureRealization_reachable_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (FeasibleProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (FeasibleProgramPureStrategy g who) :=
      fun who => FeasibleProgramPureStrategy.instFintype g LF who
    ∃ β : ReachableProgramBehavioralProfilePMF g hctx,
      reachableProgramOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (pureKernelGameAt g hctx).outcomeKernel σ) := by
  exact reachableProgram_mixedPure_realizedByBehavioralPMF_finite
    g hctx LF μ

/-- Concrete finite reachable-strategy realization theorem. -/
theorem reachableKuhnPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L) :
    ReachableKuhnPMF g hctx LF := by
  intro μ
  exact mixedPureRealization_reachable_finite
    g hctx LF μ

/-- FDist-valued mixed-pure realization target.

This is deliberately not named as the general Kuhn property: it can only be
true for mixed pure profiles whose induced behavioural probabilities are
representable by rational `FDist` kernels. -/
def ProtocolRationalMixedPureRealizationProperty [Fintype P] (g : WFProgram P L)
    [∀ who, Fintype (FeasibleProgramPureStrategy g who)] : Prop :=
  ∀ (μ : ∀ who, PMF (FeasibleProgramPureStrategy g who)),
    ∃ β : FeasibleProgramBehavioralProfile g,
      (behavioralKernelGame g).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (pureKernelGame g).outcomeKernel σ)

/-- Machine-native FDist-valued mixed-pure realization target. This is the
`hctx`-indexed machine presentation of
`ProtocolRationalMixedPureRealizationProperty`. -/
def ProtocolRationalMixedPureRealizationMachineProperty
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [∀ who, Fintype (FeasibleProgramPureStrategy g who)] : Prop :=
  ∀ (μ : ∀ who, PMF (FeasibleProgramPureStrategy g who)),
    ∃ β : FeasibleProgramBehavioralProfile g,
      (behavioralKernelGameAt g hctx).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (pureKernelGameAt g hctx).outcomeKernel σ)

theorem protocolRationalMixedPureRealizationMachineProperty_iff
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [∀ who, Fintype (FeasibleProgramPureStrategy g who)] :
    ProtocolRationalMixedPureRealizationMachineProperty g hctx ↔
      ProtocolRationalMixedPureRealizationProperty g := by
  constructor
  · intro h μ
    obtain ⟨β, hβ⟩ := h μ
    refine ⟨β, ?_⟩
    have hconv :
        (behavioralKernelGameAt g hctx).outcomeKernel β =
            (Math.PMFProduct.pmfPi μ).bind
              (fun σ =>
                (pureKernelGameAt g hctx).outcomeKernel σ) ↔
          (behavioralKernelGame g).outcomeKernel β =
            (Math.PMFProduct.pmfPi μ).bind
              (fun σ => (pureKernelGame g).outcomeKernel σ) := by
      rw [behavioralKernelGameAt_outcomeKernel_eq_behavioralKernelGame]
      rw [bind_pureKernelGameAt_outcomeKernel_eq_pureKernelGame]
      rfl
    exact hconv.mp hβ
  · intro h μ
    obtain ⟨β, hβ⟩ := h μ
    refine ⟨β, ?_⟩
    have hconv :
        (behavioralKernelGameAt g hctx).outcomeKernel β =
            (Math.PMFProduct.pmfPi μ).bind
              (fun σ =>
                (pureKernelGameAt g hctx).outcomeKernel σ) ↔
          (behavioralKernelGame g).outcomeKernel β =
            (Math.PMFProduct.pmfPi μ).bind
              (fun σ => (pureKernelGame g).outcomeKernel σ) := by
      rw [behavioralKernelGameAt_outcomeKernel_eq_behavioralKernelGame]
      rw [bind_pureKernelGameAt_outcomeKernel_eq_pureKernelGame]
      rfl
    exact hconv.mpr hβ

/-- Strong correlated variant of protocol realization: every PMF over joint
guard-legal pure profiles admits a guard-legal PMF behavioural profile with the
same outcome distribution.

Stated as a `Prop`-valued definition, not proved here. The product-mixed theorem
above is the independent-profile case; this property asks for arbitrary
correlated mixtures over joint pure profiles. -/
def ProtocolCorrelatedPureRealizationPropertyPMF (g : WFProgram P L) : Prop :=
  ∀ (μ : PMF (FeasibleProgramPureProfile g)),
    ∃ β : FeasibleProgramBehavioralProfilePMF g,
      (pmfBehavioralKernelGame g).outcomeKernel β =
        μ.bind (fun σ => (pureKernelGame g).outcomeKernel σ)

/-- Machine-native PMF correlated pure-realization target. -/
def ProtocolCorrelatedPureRealizationMachinePropertyPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : Prop :=
  ∀ (μ : PMF (FeasibleProgramPureProfile g)),
    ∃ β : FeasibleProgramBehavioralProfilePMF g,
      (pmfBehavioralKernelGameAt g hctx).outcomeKernel β =
        μ.bind
          (fun σ => (pureKernelGameAt g hctx).outcomeKernel σ)

theorem protocolCorrelatedPureRealizationMachinePropertyPMF_iff
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    ProtocolCorrelatedPureRealizationMachinePropertyPMF g hctx ↔
      ProtocolCorrelatedPureRealizationPropertyPMF g := by
  constructor
  · intro h μ
    obtain ⟨β, hβ⟩ := h μ
    refine ⟨β, ?_⟩
    have hconv :
        (pmfBehavioralKernelGameAt g hctx).outcomeKernel β =
            μ.bind
              (fun σ =>
                (pureKernelGameAt g hctx).outcomeKernel σ) ↔
          (pmfBehavioralKernelGame g).outcomeKernel β =
            μ.bind (fun σ => (pureKernelGame g).outcomeKernel σ) := by
      rw [pmfBehavioralKernelGameAt_outcomeKernel_eq_pmfBehavioralKernelGame]
      rw [bind_pureKernelGameAt_outcomeKernel_eq_pureKernelGame]
      rfl
    exact hconv.mp hβ
  · intro h μ
    obtain ⟨β, hβ⟩ := h μ
    refine ⟨β, ?_⟩
    have hconv :
        (pmfBehavioralKernelGameAt g hctx).outcomeKernel β =
            μ.bind
              (fun σ =>
                (pureKernelGameAt g hctx).outcomeKernel σ) ↔
          (pmfBehavioralKernelGame g).outcomeKernel β =
            μ.bind (fun σ => (pureKernelGame g).outcomeKernel σ) := by
      rw [pmfBehavioralKernelGameAt_outcomeKernel_eq_pmfBehavioralKernelGame]
      rw [bind_pureKernelGameAt_outcomeKernel_eq_pureKernelGame]
      rfl
    exact hconv.mpr hβ

/-- FDist-valued correlated realization target. As above, this is a rational
variant rather than the general PMF-level property. -/
def ProtocolRationalCorrelatedPureRealizationProperty
    (g : WFProgram P L) : Prop :=
  ∀ (μ : PMF (FeasibleProgramPureProfile g)),
    ∃ β : FeasibleProgramBehavioralProfile g,
      (behavioralKernelGame g).outcomeKernel β =
        μ.bind (fun σ => (pureKernelGame g).outcomeKernel σ)

/-- Machine-native FDist-valued correlated realization target. -/
def ProtocolRationalCorrelatedPureRealizationMachineProperty
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : Prop :=
  ∀ (μ : PMF (FeasibleProgramPureProfile g)),
    ∃ β : FeasibleProgramBehavioralProfile g,
      (behavioralKernelGameAt g hctx).outcomeKernel β =
        μ.bind
          (fun σ => (pureKernelGameAt g hctx).outcomeKernel σ)

theorem protocolRationalCorrelatedPureRealizationMachineProperty_iff
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    ProtocolRationalCorrelatedPureRealizationMachineProperty g hctx ↔
      ProtocolRationalCorrelatedPureRealizationProperty g := by
  constructor
  · intro h μ
    obtain ⟨β, hβ⟩ := h μ
    refine ⟨β, ?_⟩
    have hconv :
        (behavioralKernelGameAt g hctx).outcomeKernel β =
            μ.bind
              (fun σ =>
                (pureKernelGameAt g hctx).outcomeKernel σ) ↔
          (behavioralKernelGame g).outcomeKernel β =
            μ.bind (fun σ => (pureKernelGame g).outcomeKernel σ) := by
      rw [behavioralKernelGameAt_outcomeKernel_eq_behavioralKernelGame]
      rw [bind_pureKernelGameAt_outcomeKernel_eq_pureKernelGame]
      rfl
    exact hconv.mp hβ
  · intro h μ
    obtain ⟨β, hβ⟩ := h μ
    refine ⟨β, ?_⟩
    have hconv :
        (behavioralKernelGameAt g hctx).outcomeKernel β =
            μ.bind
              (fun σ =>
                (pureKernelGameAt g hctx).outcomeKernel σ) ↔
          (behavioralKernelGame g).outcomeKernel β =
            μ.bind (fun σ => (pureKernelGame g).outcomeKernel σ) := by
      rw [behavioralKernelGameAt_outcomeKernel_eq_behavioralKernelGame]
      rw [bind_pureKernelGameAt_outcomeKernel_eq_pureKernelGame]
      rfl
    exact hconv.mpr hβ

/-- `ProtocolCorrelatedPureRealizationPropertyPMF` is not vacuous: a Dirac
mixture on any legal pure profile is realized by the PMF behavioral point-lift
of that pure profile. -/
theorem protocolCorrelatedPureRealizationPMF_dirac (g : WFProgram P L)
    (σ : FeasibleProgramPureProfile g) :
    ∃ β : FeasibleProgramBehavioralProfilePMF g,
      (pmfBehavioralKernelGame g).outcomeKernel β =
        (PMF.pure σ).bind
          (fun σ => (pureKernelGame g).outcomeKernel σ) := by
  refine ⟨FeasibleProgramPureProfile.toBehavioralPMF σ, ?_⟩
  rw [PMF.pure_bind]
  exact pmfBehavioralKernelGame_outcomeKernel_eq_pureKernelGame_toBehavioralPMF g σ

/-- Machine-native Dirac witness for the PMF correlated realization target. -/
theorem protocolCorrelatedPureRealizationMachinePMF_dirac
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramPureProfile g) :
    ∃ β : FeasibleProgramBehavioralProfilePMF g,
      (pmfBehavioralKernelGameAt g hctx).outcomeKernel β =
        (PMF.pure σ).bind
          (fun σ => (pureKernelGameAt g hctx).outcomeKernel σ) := by
  refine ⟨FeasibleProgramPureProfile.toBehavioralPMF σ, ?_⟩
  rw [PMF.pure_bind]
  rw [pmfBehavioralKernelGameAt_outcomeKernel_eq_pmfBehavioralKernelGame]
  rw [pmfBehavioralKernelGame_outcomeKernel_eq_pureKernelGame_toBehavioralPMF]
  exact (pureKernelGameAt_outcomeKernel_eq_pureKernelGame
    g hctx σ).symm

/-- `ProtocolRationalCorrelatedPureRealizationProperty` is not vacuous: a concrete
witness for a direction-trivialising case is the Dirac mixture on any legal
pure profile, where the behavioural witness is its point-lift `toBehavioral`
and the outcome equation reduces to the bridge theorem
`behavioralKernelGame_outcomeKernel_eq_pureKernelGame_toBehavioral`. The
general property is non-trivial because it quantifies over every correlated
mixture. -/
theorem protocolCorrelatedPureRealization_dirac (g : WFProgram P L)
    (σ : FeasibleProgramPureProfile g) :
    ∃ β : FeasibleProgramBehavioralProfile g,
      (behavioralKernelGame g).outcomeKernel β =
        (PMF.pure σ).bind
          (fun σ => (pureKernelGame g).outcomeKernel σ) := by
  refine ⟨FeasibleProgramPureProfile.toBehavioral σ, ?_⟩
  rw [PMF.pure_bind]
  exact behavioralKernelGame_outcomeKernel_eq_pureKernelGame_toBehavioral g σ

/-- Machine-native Dirac witness for the FDist correlated realization target. -/
theorem protocolCorrelatedPureRealizationMachine_dirac
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramPureProfile g) :
    ∃ β : FeasibleProgramBehavioralProfile g,
      (behavioralKernelGameAt g hctx).outcomeKernel β =
        (PMF.pure σ).bind
          (fun σ => (pureKernelGameAt g hctx).outcomeKernel σ) := by
  refine ⟨FeasibleProgramPureProfile.toBehavioral σ, ?_⟩
  rw [PMF.pure_bind]
  rw [behavioralKernelGameAt_outcomeKernel_eq_behavioralKernelGame]
  rw [behavioralKernelGame_outcomeKernel_eq_pureKernelGame_toBehavioral]
  exact (pureKernelGameAt_outcomeKernel_eq_pureKernelGame
    g hctx σ).symm

end Vegas
