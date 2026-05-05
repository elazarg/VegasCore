import Vegas.Protocol.FOSG
import Vegas.Protocol.Checked
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
    [Fintype Player] [Fintype M.RunPrefix]
    [Fintype view.toFOSG.History]
    [∀ i, Fintype (Option (M.Action i))]
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
`M.RunPrefix`, `view.toFOSG.History`, and `Option (M.Action _)` packages the
finite-horizon assumption. -/
theorem kuhn_mixed_to_behavioral
    (view : M.FOSGView)
    [Fintype Player] [Fintype M.RunPrefix]
    [Fintype view.toFOSG.History]
    [∀ i, Fintype (Option (M.Action i))]
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
`view.toBoundedFOSG horizon`. Worlds are `M.BoundedRunPrefix horizon`; this is
the form that matches finite Vegas-program executions, where the action graph
fixes the horizon and the bounded run prefix is automatically `Fintype`.
-/

/-- Outcome distribution from sampling a bounded pure profile and running. -/
noncomputable def boundedOutcomeFromMixed
    (view : M.FOSGView) (horizon : Nat)
    [Fintype Player] [Fintype (M.BoundedRunPrefix horizon)]
    [Fintype (view.toBoundedFOSG horizon).History]
    [∀ i, Fintype (Option (M.Action i))]
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
    [Fintype (M.BoundedRunPrefix horizon)]
    [Fintype (view.toBoundedFOSG horizon).History]
    [∀ i, Fintype (Option (M.Action i))]
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

/-! ## Checked graph-machine FOSG corollary

Specialization of the Machine-native bounded Kuhn theorem to the graph machine
of a checked Vegas program. The witness, the input mixed profile, and the
asserted distributional equality are all stated against
`graphMachine g hctx` and `fosgView g hctx`; no syntactic strategy space or
syntax-side outcome kernel is used.
-/

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- **Graph-FOSG Kuhn helper for a checked Vegas program.**

The graph machine `graphMachine g hctx` is the executable protocol carrier of
a checked Vegas program. This corollary applies
`Machine.FOSGView.kuhn_mixed_to_behavioral_bounded` to its canonical FOSG view
at the syntactic horizon.

The witness β is a behavioral profile of the bounded graph-machine FOSG view;
the equality is between two `PMF (graphMachine g hctx).Outcome` distributions
produced by running the machine under the realized strategies. This is a
protocol/FOSG helper; the public Vegas theorem is `kuhn_finiteKernelGame`
below, stated over the Vegas kernel-game API. -/
theorem kuhn_mixed_to_behavioral_graphFOSG
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L)
    (μ :
      (fosgView g hctx).BoundedMixedProfile (syntaxSteps g.prog))
    (steps : Nat) :
    letI : Fintype (graphMachine g hctx).State :=
      graphMachine.instFintypeState g hctx LF
    letI : ∀ who : P,
        Fintype (Option ((graphMachine g hctx).Action who)) :=
      fun who => graphMachine.instFintypeOptionAction g hctx LF who
    letI : Fintype (graphMachine g hctx).Event :=
      graphMachine.instFintypeEvent g hctx LF
    letI : Fintype
        ((graphMachine g hctx).BoundedRunPrefix (syntaxSteps g.prog)) :=
      Machine.BoundedRunPrefix.instFintype
    letI : Fintype
        (((fosgView g hctx).toBoundedFOSG
            (syntaxSteps g.prog)).History) :=
      boundedFOSG.instFintypeHistory g hctx (syntaxSteps g.prog)
    letI : DecidablePred
        (((fosgView g hctx).toBoundedFOSG
            (syntaxSteps g.prog)).terminal) :=
      Classical.decPred _
    ∃ β :
      (fosgView g hctx).BoundedBehavioralProfile
        (syntaxSteps g.prog),
      (fosgView g hctx).boundedOutcomeFromBehavioral
          (syntaxSteps g.prog) β steps =
        (fosgView g hctx).boundedOutcomeFromMixed
          (syntaxSteps g.prog) μ steps := by
  classical
  letI : Fintype (graphMachine g hctx).State :=
    graphMachine.instFintypeState g hctx LF
  letI : ∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who)) :=
    fun who => graphMachine.instFintypeOptionAction g hctx LF who
  letI : Fintype (graphMachine g hctx).Event :=
    graphMachine.instFintypeEvent g hctx LF
  letI : Fintype
      ((graphMachine g hctx).BoundedRunPrefix (syntaxSteps g.prog)) :=
    Machine.BoundedRunPrefix.instFintype
  letI : Fintype
      (((fosgView g hctx).toBoundedFOSG
          (syntaxSteps g.prog)).History) :=
    boundedFOSG.instFintypeHistory g hctx (syntaxSteps g.prog)
  letI : DecidablePred
      (((fosgView g hctx).toBoundedFOSG
          (syntaxSteps g.prog)).terminal) :=
    Classical.decPred _
  have hLeg :
      ((fosgView g hctx).toBoundedFOSG
        (syntaxSteps g.prog)).LegalObservable :=
    finiteFOSG_legalObservable g hctx
  exact (fosgView g hctx).kuhn_mixed_to_behavioral_bounded
    (syntaxSteps g.prog) hLeg μ steps

/-- Finite Vegas Kuhn theorem stated directly for the public kernel games.

This is the replacement headline shape: the independent mixed profile ranges
over the pure strategy carrier of `pureKernelGameAt`, and the behavioral
witness inhabits the PMF behavioral carrier of `pmfBehavioralKernelGameAt`.
The equality is an equality of the games' public outcome kernels. -/
theorem kuhn_finiteKernelGame
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L)
    (μ : ∀ who, PMF ((pureKernelGameAt g hctx LF).Strategy who)) :
    ∃ β : (pmfBehavioralKernelGameAt g hctx LF).Profile,
      (pmfBehavioralKernelGameAt g hctx LF).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun π => (pureKernelGameAt g hctx LF).outcomeKernel π) := by
  classical
  letI : Fintype (graphMachine g hctx).State :=
    graphMachine.instFintypeState g hctx LF
  letI : ∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who)) :=
    fun who => graphMachine.instFintypeOptionAction g hctx LF who
  letI : Fintype (graphMachine g hctx).Event :=
    graphMachine.instFintypeEvent g hctx LF
  letI : Fintype
      ((graphMachine g hctx).BoundedRunPrefix (syntaxSteps g.prog)) :=
    Machine.BoundedRunPrefix.instFintype
  letI : Fintype
      (((fosgView g hctx).toBoundedFOSG
          (syntaxSteps g.prog)).History) :=
    boundedFOSG.instFintypeHistory g hctx (syntaxSteps g.prog)
  letI : DecidablePred
      (((fosgView g hctx).toBoundedFOSG
          (syntaxSteps g.prog)).terminal) :=
    Classical.decPred _
  letI : ∀ who : P,
      Fintype ((pureKernelGameAt g hctx LF).Strategy who) := by
    intro who
    dsimp [pureKernelGameAt, pureStrategyAt,
      Machine.FOSGView.BoundedPureStrategy]
    infer_instance
  have hLeg :
      ((fosgView g hctx).toBoundedFOSG
        (syntaxSteps g.prog)).LegalObservable :=
    finiteFOSG_legalObservable g hctx
  obtain ⟨β, hβ⟩ :=
    (fosgView g hctx).kuhn_mixed_to_behavioral_bounded
      (syntaxSteps g.prog) hLeg μ (syntaxSteps g.prog)
  refine ⟨β, ?_⟩
  simpa [pmfBehavioralKernelGameAt,
    pureKernelGameAt, Machine.FOSGView.boundedOutcomeFromMixed,
    GameTheory.FOSG.Kuhn.reachableMixedProfileJoint] using hβ

end Vegas
