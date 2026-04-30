import Vegas.Equilibrium
import Vegas.FOSG
import Vegas.PureStrategic
import Vegas.StrategicPMF

/-!
# Protocol-native semantics for Vegas

This file defines Vegas's solution concepts directly in terms of the
protocol's own `outcomeDistBehavioral` semantics (rather than through
the `toKernelGame` bridge) and proves that the two definitions agree.
The purpose is to make the protocol picture explicit in-tree: what a
Vegas Nash equilibrium *means* at the protocol level is exactly the
statement of `ProtocolNash`, and the existing `Vegas.IsNash` (defined
via `KernelGame`) is shown to be literally the same proposition.

The file has two regions.

* **Region A (protocol-native definitions, proved).**
  `protocolEU`, `ProtocolNash`, `ProtocolBestResponse`,
  `ProtocolDominant`, `ProtocolStrictNash`. These are defined directly
  on `LegalProgramBehavioralProfile` / `...Strategy`, with the guard-
  legality constraint carried by the subtype. Correspondence theorems
  (`isNash_iff_protocolNash`, etc.) prove each equals its
  `KernelGame`-transported counterpart by definitional unfolding.

* **Region B (realization theorems and named targets).**
  `ProtocolSequentialKuhnPropertyPMF g hctx LF : Prop` is the proved sequential
  realization claim: every independent mixed profile over legal pure
  strategies is outcome-equivalent to a total PMF behavioural profile for the
  sequential denotation. The PMF target is essential: arbitrary mixed pure
  profiles can induce real-valued behavioural probabilities, while the
  original `FDist` behavioural game is rational-valued.
  `ProtocolReachableKuhnPropertyPMF g hctx LF : Prop` is the reachable
  strategy-space version.
  `ProtocolTotalMixedPureRealizationPMF g : Prop` is the syntax-recursive
  Vegas-profile target.
  `ProtocolRationalMixedPureRealizationProperty g : Prop` is the corresponding
  FDist-valued target for rational behavioural witnesses.
  `ProtocolCorrelatedPureRealizationPropertyPMF g : Prop` is the stronger
  correlated variant over arbitrary PMFs on joint pure profiles.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## Region A — protocol-native solution concepts -/

/-- Protocol-level expected utility: evaluate the Vegas program's
behavioural outcome distribution against the legal profile
(unpacking each strategy via `.val`) and take the expected payoff
for player `i`. -/
noncomputable def protocolEU (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) (i : P) : ℝ :=
  (outcomeDistBehavioral g.prog (fun j => (σ j).val) g.env).sum
    (fun o w => (w : ℝ) * (o i : ℝ))

@[simp] theorem toKernelGame_eu_eq_protocolEU (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) (i : P) :
    (toKernelGame g).eu σ i = protocolEU g σ i := by
  simpa [protocolEU] using
    toKernelGame_eu (g := g) (σ := σ) (who := i)

@[simp] theorem eu_eq_protocolEU (g : WFProgram P L)
    (σ : StrategyProfile g) (i : P) :
    Vegas.eu g σ i = protocolEU g σ i := by
  simp [protocolEU, eu, Game]

/-- Protocol-level Nash equilibrium: no player can improve their
protocol-level expected utility by a unilateral deviation within
the guard-legal strategy space. -/
def ProtocolNash (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) : Prop :=
  ∀ (who : P) (s' : LegalProgramBehavioralStrategy g who),
    protocolEU g σ who ≥ protocolEU g (Function.update σ who s') who

theorem isNash_iff_protocolNash (g : WFProgram P L)
    (σ : StrategyProfile g) :
    Vegas.IsNash g σ ↔ ProtocolNash g σ := by
  unfold Vegas.IsNash ProtocolNash
  simp only [KernelGame.IsNash, ge_iff_le]
  constructor
  · intro h who s'
    have := h who s'
    simpa [eu_eq_protocolEU, Game] using this
  · intro h who s'
    have := h who s'
    simpa [eu_eq_protocolEU, Game] using this

/-- Protocol-level best response: `s` maximises player `who`'s
protocol-level expected utility among all legal deviations, holding
opponents' strategies in `σ` fixed. -/
def ProtocolBestResponse (g : WFProgram P L)
    (who : P) (σ : LegalProgramBehavioralProfile g)
    (s : LegalProgramBehavioralStrategy g who) : Prop :=
  ∀ (s' : LegalProgramBehavioralStrategy g who),
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
    simpa [eu_eq_protocolEU, Game, Strategy, StrategyProfile] using this
  · intro h s'
    have := h s'
    simpa [eu_eq_protocolEU, Game, Strategy, StrategyProfile] using this

/-- Protocol-level dominant strategy: `s` is at least as good as any
legal alternative, for player `who`, at every legal profile of
opponents. -/
def ProtocolDominant (g : WFProgram P L)
    (who : P) (s : LegalProgramBehavioralStrategy g who) : Prop :=
  ∀ (σ : LegalProgramBehavioralProfile g)
    (s' : LegalProgramBehavioralStrategy g who),
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
    simpa [eu_eq_protocolEU, Game, Strategy, StrategyProfile] using this
  · intro h σ s'
    have := h σ s'
    simpa [eu_eq_protocolEU, Game, Strategy, StrategyProfile] using this

/-- Protocol-level strict Nash equilibrium: every legal unilateral
deviation strictly decreases the deviator's protocol-level expected
utility. -/
def ProtocolStrictNash (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) : Prop :=
  ∀ (who : P) (s' : LegalProgramBehavioralStrategy g who), s' ≠ σ who →
    protocolEU g σ who > protocolEU g (Function.update σ who s') who

theorem isStrictNash_iff_protocolStrictNash (g : WFProgram P L)
    (σ : StrategyProfile g) :
    Vegas.IsStrictNash g σ ↔ ProtocolStrictNash g σ := by
  unfold Vegas.IsStrictNash ProtocolStrictNash
  simp only [KernelGame.IsStrictNash]
  constructor
  · intro h who s' hne
    have := h who s' hne
    simpa [eu_eq_protocolEU, Game, Strategy, StrategyProfile] using this
  · intro h who s' hne
    have := h who s' hne
    simpa [eu_eq_protocolEU, Game, Strategy, StrategyProfile] using this

/-! ## Region B — named realization targets -/

/-- The protocol-level Kuhn property for a concrete finite Vegas program:
every independent mixed profile over guard-legal pure strategies admits a total
sequential PMF behavioural profile with the same outcome distribution. -/
def ProtocolSequentialKuhnPropertyPMF [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L) : Prop :=
  ∀ (μ : ∀ who, PMF (LegalProgramPureStrategy g who)),
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : SequentialBehavioralProfilePMF g hctx,
      sequentialOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ)

/-- Mixed-to-behavioral realization for concrete finite Vegas programs in the
total sequential strategy space. -/
theorem protocol_mixedPure_realizedBySequentialBehavioralPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : SequentialBehavioralProfilePMF g hctx,
      sequentialOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) := by
  exact sequential_mixedPure_realizedByBehavioralPMF_finite
    g hctx LF μ

/-- Concrete finite sequential-strategy realization theorem. -/
theorem protocolSequentialKuhnPropertyPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L) :
    ProtocolSequentialKuhnPropertyPMF g hctx LF := by
  intro μ
  exact protocol_mixedPure_realizedBySequentialBehavioralPMF_finite
    g hctx LF μ

/-- The protocol-level Kuhn property for a concrete finite Vegas program:
every independent mixed profile over guard-legal pure strategies admits a
reachable PMF behavioural profile with the same outcome distribution.

The PMF target is part of the mathematical statement. Vegas' `FDist`
behavioural strategies have rational weights, so they cannot represent all
behavioural probabilities induced by arbitrary `PMF` mixtures over pure
strategies. The behavioral witness is indexed only by reachable program
observations; total profiles are a stronger representation target and are
named separately below. -/
def ProtocolReachableKuhnPropertyPMF [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L) : Prop :=
  ∀ (μ : ∀ who, PMF (LegalProgramPureStrategy g who)),
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : ReachableProgramBehavioralProfilePMF g hctx,
      reachableProgramOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ)

/-- Reachable mixed-to-behavioral realization for concrete finite Vegas
programs. The witness is not a total strategy. -/
theorem protocol_mixedPure_realizedByReachableBehavioralPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : ReachableProgramBehavioralProfilePMF g hctx,
      reachableProgramOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) := by
  exact reachableProgram_mixedPure_realizedByBehavioralPMF_finite
    g hctx LF μ

/-- Concrete finite reachable-strategy realization theorem. -/
theorem protocolReachableKuhnPropertyPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L) :
    ProtocolReachableKuhnPropertyPMF g hctx LF := by
  intro μ
  exact protocol_mixedPure_realizedByReachableBehavioralPMF_finite
    g hctx LF μ

/-- Syntax-recursive total-profile realization target, PMF
mixed-to-behavioral direction.

Every independent mixed profile over guard-legal pure strategies is realized by
a guard-legal PMF behavioral profile with the same outcome distribution. The
witness lives in Vegas' syntax-recursive behavioral strategy space, so this is
different from the sequential-denotation theorem above. -/
def ProtocolTotalMixedPureRealizationPMF
    [Fintype P] (g : WFProgram P L)
    [∀ who, Fintype (LegalProgramPureStrategy g who)] : Prop :=
  ∀ (μ : ∀ who, PMF (LegalProgramPureStrategy g who)),
    ∃ β : LegalProgramBehavioralProfilePMF g,
      (toKernelGamePMF g).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ)

/-- Mixed-to-behavioral realization for concrete finite Vegas programs in the
syntax-recursive Vegas behavioral strategy space. -/
theorem protocol_mixedPure_realizedByBehavioralPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : LegalProgramBehavioralProfilePMF g,
      (toKernelGamePMF g).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) := by
  exact FOSGBridge.mixedPure_realizedByLegalBehavioralPMF_finite
    g hctx LF μ

/-- Concrete finite syntax-recursive Vegas realization theorem. -/
theorem protocolTotalMixedPureRealizationPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ProtocolTotalMixedPureRealizationPMF g := by
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  intro μ
  exact protocol_mixedPure_realizedByBehavioralPMF_finite
    g hctx LF μ

/-- FDist-valued mixed-pure realization target.

This is deliberately not named as the general Kuhn property: it can only be
true for mixed pure profiles whose induced behavioural probabilities are
representable by rational `FDist` kernels. -/
def ProtocolRationalMixedPureRealizationProperty [Fintype P] (g : WFProgram P L)
    [∀ who, Fintype (LegalProgramPureStrategy g who)] : Prop :=
  ∀ (μ : ∀ who, PMF (LegalProgramPureStrategy g who)),
    ∃ β : LegalProgramBehavioralProfile g,
      (toKernelGame g).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ)

/-- Strong correlated variant of protocol realization: every PMF over joint
guard-legal pure profiles admits a guard-legal PMF behavioural profile with the
same outcome distribution.

Stated as a `Prop`-valued definition, not proved here. The product-mixed theorem
above is the independent-profile case; this property asks for arbitrary
correlated mixtures over joint pure profiles. -/
def ProtocolCorrelatedPureRealizationPropertyPMF (g : WFProgram P L) : Prop :=
  ∀ (μ : PMF (LegalProgramPureProfile g)),
    ∃ β : LegalProgramBehavioralProfilePMF g,
      (toKernelGamePMF g).outcomeKernel β =
        μ.bind (fun σ => (toStrategicKernelGame g).outcomeKernel σ)

/-- FDist-valued correlated realization target. As above, this is a rational
variant rather than the general PMF-level property. -/
def ProtocolRationalCorrelatedPureRealizationProperty
    (g : WFProgram P L) : Prop :=
  ∀ (μ : PMF (LegalProgramPureProfile g)),
    ∃ β : LegalProgramBehavioralProfile g,
      (toKernelGame g).outcomeKernel β =
        μ.bind (fun σ => (toStrategicKernelGame g).outcomeKernel σ)

/-- `ProtocolCorrelatedPureRealizationPropertyPMF` is not vacuous: a Dirac
mixture on any legal pure profile is realized by the PMF behavioral point-lift
of that pure profile. -/
theorem protocolCorrelatedPureRealizationPMF_dirac (g : WFProgram P L)
    (σ : LegalProgramPureProfile g) :
    ∃ β : LegalProgramBehavioralProfilePMF g,
      (toKernelGamePMF g).outcomeKernel β =
        (PMF.pure σ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) := by
  refine ⟨LegalProgramPureProfile.toBehavioralPMF σ, ?_⟩
  rw [PMF.pure_bind]
  exact toKernelGamePMF_outcomeKernel_eq_toStrategicKernelGame_toBehavioralPMF g σ

/-- `ProtocolRationalCorrelatedPureRealizationProperty` is not vacuous: a concrete
witness for a direction-trivialising case is the Dirac mixture on any legal
pure profile, where the behavioural witness is its point-lift `toBehavioral`
and the outcome equation reduces to the bridge theorem
`toKernelGame_outcomeKernel_eq_toStrategicKernelGame_toBehavioral`. The
general property is non-trivial because it quantifies over every correlated
mixture. -/
theorem protocolCorrelatedPureRealization_dirac (g : WFProgram P L)
    (σ : LegalProgramPureProfile g) :
    ∃ β : LegalProgramBehavioralProfile g,
      (toKernelGame g).outcomeKernel β =
        (PMF.pure σ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) := by
  refine ⟨LegalProgramPureProfile.toBehavioral σ, ?_⟩
  rw [PMF.pure_bind]
  exact toKernelGame_outcomeKernel_eq_toStrategicKernelGame_toBehavioral g σ

end Vegas
