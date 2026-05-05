import Vegas.Protocol.FOSG
import Vegas.Protocol.Strategic
import GameTheory.Languages.FOSG.Kuhn

/-!
# Machine-native Kuhn theorem

A Kuhn-style mixed-to-behavioral realization theorem stated entirely in terms
of an asynchronous protocol `Machine` and one of its `FOSGView`s, with no
detour through external syntactic carriers.

The witness type is a behavioral profile of the machine view; the asserted
equality is between two `PMF M.Outcome` distributions produced by running the
machine under the resulting strategies.

This file is a thin wrapper that surfaces upstream
`GameTheory.FOSG.Kuhn.reachable_mixed_to_legal_behavioral_runDist` as a
machine-native API. The substantive Kuhn proof lives upstream; what is new
here is the carrier on which the theorem is stated: an arbitrary
`Machine.FOSGView`, with all conclusions phrased in machine-side observables.
-/

namespace Vegas

open GameTheory

namespace Machine

variable {Player : Type} [DecidableEq Player]

namespace FOSGView

variable {M : Machine Player}

/-- Outcome distribution from sampling a pure profile from the independent
mixed profile and running the machine under that pure profile. -/
noncomputable def outcomeFromMixed
    (view : M.FOSGView)
    [Fintype Player] [Fintype M.State]
    [Fintype view.toFOSG.History]
    [∀ i, Fintype (Option (view.Act i))]
    [DecidablePred view.toFOSG.terminal]
    (μ : view.MixedProfile) (horizon : Nat) :
    PMF M.Outcome :=
  (FOSG.Kuhn.reachableMixedProfileJoint (G := view.toFOSG) μ).bind
    (fun π => view.outcomeFromPure π horizon)

/-- **Machine-native Kuhn theorem (mixed → behavioral).**

Given any FOSG view of a machine and any independent mixed profile of pure
strategies, there exists a behavioral profile that produces the same
distribution over the machine's terminal outcomes.

This is the abstract upstream FOSG Kuhn theorem
(`reachable_mixed_to_legal_behavioral_runDist`) restated with the machine as
the carrier of record: the witness type is a `Machine.FOSGView` behavioral
profile and the equality lives in `PMF M.Outcome`, with no mention of any
external syntactic strategy space.

`hLeg` is the legal-observability hypothesis on the derived FOSG (perfect
recall up to the FOSG observation factoring); finiteness of `Player`,
`M.State`, `view.toFOSG.History`, and `Option (view.Act _)` packages the
finite-horizon assumption. -/
theorem kuhn_mixed_to_behavioral
    (view : M.FOSGView)
    [Fintype Player] [Fintype M.State]
    [Fintype view.toFOSG.History]
    [∀ i, Fintype (Option (view.Act i))]
    [DecidablePred view.toFOSG.terminal]
    (hLeg : view.toFOSG.LegalObservable)
    (μ : view.MixedProfile) (horizon : Nat) :
    ∃ β : view.BehavioralProfile,
      view.outcomeFromBehavioral β horizon =
        view.outcomeFromMixed μ horizon := by
  obtain ⟨β, hβ⟩ :=
    FOSG.Kuhn.reachable_mixed_to_legal_behavioral_runDist
      (G := view.toFOSG) hLeg μ horizon
  refine ⟨β, ?_⟩
  unfold outcomeFromBehavioral outcomeFromMixed outcomeFromPure
  rw [hβ, PMF.map_bind]

/-! ## Bounded-horizon variant

The same Machine-native Kuhn theorem stated for the horizon-bounded FOSG view
`view.toBoundedFOSG horizon`. Worlds are `M.BoundedState horizon`; this is
the form that matches finite Vegas-program executions, where the action graph
fixes the horizon and the bounded state presentation is automatically
`Fintype`.
-/

/-- Outcome distribution from sampling a bounded pure profile and running. -/
noncomputable def boundedOutcomeFromMixed
    (view : M.FOSGView) (horizon : Nat)
    [Fintype Player] [Fintype (M.BoundedState horizon)]
    [Fintype (view.toBoundedFOSG horizon).History]
    [∀ i, Fintype (Option (view.Act i))]
    [DecidablePred (view.toBoundedFOSG horizon).terminal]
    (μ : view.BoundedMixedProfile horizon)
    (steps : Nat) : PMF M.Outcome :=
  (FOSG.Kuhn.reachableMixedProfileJoint
      (G := view.toBoundedFOSG horizon) μ).bind
    (fun π => view.boundedOutcomeFromPure horizon π steps)

/-- **Machine-native Kuhn theorem (mixed → behavioral), bounded horizon.**

The same realization theorem as `kuhn_mixed_to_behavioral`, stated on the
horizon-bounded FOSG view. This is the form that applies to finite Vegas
protocols: when the action graph fixes a syntactic step bound,
`(view.toBoundedFOSG horizon).History` is automatically `Fintype` and `hLeg`
is discharged by an existing legal-observability proof for the bounded view.
-/
theorem kuhn_mixed_to_behavioral_bounded
    (view : M.FOSGView) (horizon : Nat)
    [Fintype Player]
    [Fintype (M.BoundedState horizon)]
    [Fintype (view.toBoundedFOSG horizon).History]
    [∀ i, Fintype (Option (view.Act i))]
    [DecidablePred (view.toBoundedFOSG horizon).terminal]
    (hLeg : (view.toBoundedFOSG horizon).LegalObservable)
    (μ : view.BoundedMixedProfile horizon) (steps : Nat) :
    ∃ β : view.BoundedBehavioralProfile horizon,
      view.boundedOutcomeFromBehavioral horizon β steps =
        view.boundedOutcomeFromMixed horizon μ steps := by
  obtain ⟨β, hβ⟩ :=
    FOSG.Kuhn.reachable_mixed_to_legal_behavioral_runDist
      (G := view.toBoundedFOSG horizon) hLeg μ steps
  refine ⟨β, ?_⟩
  unfold boundedOutcomeFromBehavioral boundedOutcomeFromMixed
    boundedOutcomeFromPure
  rw [hβ, PMF.map_bind]

end FOSGView

end Machine

/-! ## Checked syntax-graph FOSG corollary

Specialization of the Machine-native bounded Kuhn theorem to the syntax graph
of a checked Vegas program. The witness, the input mixed profile, and the
asserted distributional equality are all stated against the graph-native syntax
machine and `syntaxGraphFOSGView g`; no cursor or syntax-recursive strategy
space is used.
-/

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- **Syntax-graph FOSG Kuhn helper for a checked Vegas program.**

The graph-native syntax machine `syntaxGraphMachine g` is the executable
protocol carrier of a checked Vegas program. This corollary applies
`Machine.FOSGView.kuhn_mixed_to_behavioral_bounded` to its canonical FOSG view
at the syntactic horizon.

The witness β is a behavioral profile of the bounded syntax-graph FOSG view;
the equality is between two `PMF (syntaxGraphMachine g).Outcome` distributions
produced by running the machine under the realized strategies. This is a
protocol/FOSG helper; the public Vegas theorem is `kuhn_finiteKernelGame`
below, stated over the Vegas kernel-game API. -/
theorem kuhn_mixed_to_behavioral_syntaxGraph
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (μ :
      (syntaxGraphFOSGView g).BoundedMixedProfile (syntaxSteps g.prog))
    (steps : Nat) :
    ∃ β :
      (syntaxGraphFOSGView g).BoundedBehavioralProfile
        (syntaxSteps g.prog),
      (syntaxGraphFOSGView g).boundedOutcomeFromBehavioral
          (syntaxSteps g.prog) β steps =
        (syntaxGraphFOSGView g).boundedOutcomeFromMixed
          (syntaxSteps g.prog) μ steps := by
  classical
  have hLeg :
      ((syntaxGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).LegalObservable :=
    syntaxGraphFOSGView_toBoundedFOSG_legalObservable g
      (syntaxSteps g.prog)
  exact (syntaxGraphFOSGView g).kuhn_mixed_to_behavioral_bounded
    (syntaxSteps g.prog) hLeg μ steps

/-- Finite Vegas Kuhn theorem stated directly for the public kernel games.

This is the replacement headline shape: the independent mixed profile ranges
over the pure strategy carrier of `pureKernelGameAt`, and the behavioral
witness inhabits the PMF behavioral carrier of `pmfBehavioralKernelGameAt`.
The equality is an equality of the games' public outcome kernels. -/
theorem kuhn_finiteKernelGame
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (μ : ∀ who, PMF ((pureKernelGameAt g).Strategy who)) :
    ∃ β : (pmfBehavioralKernelGameAt g).Profile,
      (pmfBehavioralKernelGameAt g).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun π => (pureKernelGameAt g).outcomeKernel π) := by
  classical
  have hLeg :
      ((syntaxGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).LegalObservable :=
    syntaxGraphFOSGView_toBoundedFOSG_legalObservable g
      (syntaxSteps g.prog)
  obtain ⟨β, hβ⟩ :=
    (syntaxGraphFOSGView g).kuhn_mixed_to_behavioral_bounded
      (syntaxSteps g.prog) hLeg μ (syntaxSteps g.prog)
  refine ⟨β, ?_⟩
  simpa [pmfBehavioralKernelGameAt,
    pureKernelGameAt, Machine.FOSGView.boundedOutcomeFromMixed,
    GameTheory.FOSG.Kuhn.reachableMixedProfileJoint] using hβ

end Vegas
