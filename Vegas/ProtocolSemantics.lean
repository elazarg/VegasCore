import Vegas.Equilibrium
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

* **Region B (named targets, not theorems).**
  `ProtocolKuhnPropertyPMF g : Prop` is the general protocol-level Kuhn claim:
  every independent mixed profile over legal pure strategies is
  outcome-equivalent to some legal PMF behavioural profile. The PMF target is
  essential: arbitrary mixed pure profiles can induce real-valued behavioural
  probabilities, while the original `FDist` behavioural game is rational-valued.
  `ProtocolRationalKuhnProperty g : Prop` is the corresponding FDist-valued
  target for rational behavioural witnesses.
  `ProtocolCorrelatedPureRealizationPropertyPMF g : Prop` is the stronger
  correlated variant over arbitrary PMFs on joint pure profiles.
  `Vegas.FOSG` gives the outcome-preserving protocol representation for
  arbitrary state-dependent guards; the remaining target is relating the
  Vegas legal pure/behavioral strategy spaces to the corresponding FOSG
  reachable strategy spaces, or proving the realization directly for
  Vegas.

The MAID backend remains useful for the older compilation path, but it is not
the protocol-representing route: its decision nodes quantify over full value
types rather than guard-filtered actions.
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

/-- The general protocol-level Kuhn property for a Vegas program: every
independent mixed profile over guard-legal pure strategies admits a
guard-legal PMF behavioural profile with the same outcome distribution.

The PMF target is part of the mathematical statement. Vegas' `FDist`
behavioural strategies have rational weights, so they cannot represent all
behavioural probabilities induced by arbitrary `PMF` mixtures over pure
strategies. -/
def ProtocolKuhnPropertyPMF [Fintype P] (g : WFProgram P L)
    [∀ who, Fintype (LegalProgramPureStrategy g who)] : Prop :=
  ∀ (μ : ∀ who, PMF (LegalProgramPureStrategy g who)),
    ∃ β : LegalProgramBehavioralProfilePMF g,
      (toKernelGamePMF g).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ)

/-- FDist-valued version of the protocol-level Kuhn target.

This is deliberately not named as the general Kuhn property: it can only be
true for mixed pure profiles whose induced behavioural probabilities are
representable by rational `FDist` kernels. -/
def ProtocolRationalKuhnProperty [Fintype P] (g : WFProgram P L)
    [∀ who, Fintype (LegalProgramPureStrategy g who)] : Prop :=
  ∀ (μ : ∀ who, PMF (LegalProgramPureStrategy g who)),
    ∃ β : LegalProgramBehavioralProfile g,
      (toKernelGame g).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ)

/-- Strong correlated variant of protocol realization: every PMF over joint
guard-legal pure profiles admits a guard-legal PMF behavioural profile with the
same outcome distribution.

Stated as a `Prop`-valued definition, not proved here. The FOSG bridge proves
the right protocol outcome semantics. The remaining strategy-space step is not
mere subtype unpacking: the generic FOSG witness is indexed by full reachable
player-view histories, while `LegalProgramBehavioralProfilePMF g` is indexed by
the current Vegas cursor and visible environment. Closing this property requires
either proving the FOSG witness is current-observation-local for compiled Vegas
programs, or applying the core Kuhn theorem directly to that current-observation
state space. -/
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
