import Vegas.GameBridge.FOSG.Basic
import Vegas.GameBridge.FOSG.FromCore
import Vegas.GameBridge.FOSG.NativeEquiv
import Vegas.Strategic.KernelGame
import GameTheory.Languages.FOSG.Kuhn

/-!
# Machine-carried FOSG Kuhn theorem

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

/-- **Machine-carried FOSG Kuhn theorem (mixed → behavioral).**

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

The same machine-carried FOSG Kuhn theorem stated for the horizon-bounded FOSG view
`view.toBoundedFOSG horizon`. Worlds are `M.BoundedState horizon`; this is
the form that matches finite Vegas-program executions, where the event graph
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

/-- **Machine-carried FOSG Kuhn theorem (mixed → behavioral), bounded horizon.**

The same realization theorem as `kuhn_mixed_to_behavioral`, stated on the
horizon-bounded FOSG view. This is the form that applies to finite Vegas
protocols: when the event graph fixes a syntactic step bound,
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

/-! ## Checked event-graph FOSG corollary

Specialization of the bounded FOSG Kuhn theorem to the event graph of a
checked Vegas program. The witness, the input mixed profile, and the asserted
distributional equality are all stated against the canonical event-graph
machine and `eventGraphFOSGView g`; no cursor or syntax-recursive strategy
space is used.
-/

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- **Event-graph FOSG Kuhn helper for a checked Vegas program.**

The canonical event-graph machine `eventGraphMachine g` is the executable
protocol carrier of a checked Vegas program. This corollary applies
`Machine.FOSGView.kuhn_mixed_to_behavioral_bounded` to its canonical FOSG view
at the syntactic horizon.

The witness β is a behavioral profile of the bounded event-graph FOSG view;
the equality is between two `PMF (eventGraphMachine g).Outcome` distributions
produced by running the machine under the realized strategies. This is a
protocol/FOSG helper; the public Vegas theorem is `kuhn_finiteKernelGame`
below, stated over the Vegas kernel-game API. -/
theorem kuhn_mixed_to_behavioral_eventGraph
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (μ :
      (eventGraphFOSGView g).BoundedMixedProfile (syntaxSteps g.prog))
    (steps : Nat) :
    ∃ β :
      (eventGraphFOSGView g).BoundedBehavioralProfile
        (syntaxSteps g.prog),
      (eventGraphFOSGView g).boundedOutcomeFromBehavioral
          (syntaxSteps g.prog) β steps =
        (eventGraphFOSGView g).boundedOutcomeFromMixed
          (syntaxSteps g.prog) μ steps := by
  classical
  have hLeg :
      ((eventGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).LegalObservable :=
    eventGraphFOSGView_toBoundedFOSG_legalObservable g
      (syntaxSteps g.prog)
  exact (eventGraphFOSGView g).kuhn_mixed_to_behavioral_bounded
    (syntaxSteps g.prog) hLeg μ steps

/-- Transport a native independent mixed profile to the event-graph FOSG
presentation through the native/FOSG pure-strategy equivalence. -/
noncomputable def nativeMixedProfileToFOSG
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (μ :
      ∀ who,
        PMF ((eventGraphRoundView g).BoundedPureStrategy horizon who)) :
    (eventGraphFOSGView g).BoundedMixedProfile horizon :=
  fun who =>
    PMF.map (NativeFOSG.nativePureStrategyToFOSG g horizon who) (μ who)

/-- Product mixed-profile transport commutes with the native/FOSG pure-profile
equivalence. -/
theorem reachableMixedProfileJoint_nativeToFOSG
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (μ :
      ∀ who,
        PMF ((eventGraphRoundView g).BoundedPureStrategy horizon who)) :
    FOSG.Kuhn.reachableMixedProfileJoint
        (G := (eventGraphFOSGView g).toBoundedFOSG horizon)
        (nativeMixedProfileToFOSG g horizon μ) =
      PMF.map (NativeFOSG.nativePureProfileToFOSG g horizon)
        (Math.PMFProduct.pmfPi μ) := by
  simpa [nativeMixedProfileToFOSG,
    NativeFOSG.nativePureProfileToFOSG,
    Math.ProbabilityMassFunction.pushforward] using
    (Math.PMFProduct.pmfPi_push_coordwise μ
      (fun who => NativeFOSG.nativePureStrategyToFOSG g horizon who)).symm

/-- Finite Vegas Kuhn theorem stated directly for the public native kernel
games.  The proof uses the FOSG Kuhn theorem only after transporting native
pure strategies into the event-graph FOSG presentation, then transports the
resulting behavioral witness and outcome laws back to the native machine
semantics. -/
theorem kuhn_finiteKernelGame
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (μ : ∀ who, PMF ((pureKernelGameAt g).Strategy who)) :
    ∃ β : (pmfBehavioralKernelGameAt g).Profile,
      (pmfBehavioralKernelGameAt g).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun π => (pureKernelGameAt g).outcomeKernel π) := by
  classical
  let horizon := syntaxSteps g.prog
  let μF : (eventGraphFOSGView g).BoundedMixedProfile horizon :=
    nativeMixedProfileToFOSG g horizon μ
  obtain ⟨βF, hβF⟩ :=
    kuhn_mixed_to_behavioral_eventGraph g μF horizon
  let βN : (eventGraphRoundView g).BoundedBehavioralProfile horizon :=
    NativeFOSG.fosgBehavioralProfileToNative g horizon βF
  refine ⟨βN, ?_⟩
  have hbehavioral :
      (eventGraphRoundView g).boundedOutcomeFromBehavioral horizon βN horizon =
        (eventGraphFOSGView g).boundedOutcomeFromBehavioral horizon βF horizon := by
    have htransport :=
      NativeFOSG.boundedOutcomeFromBehavioral_nativeToFOSG
        g horizon βN horizon
    have hprofile :
        NativeFOSG.nativeBehavioralProfileToFOSG g horizon βN = βF := by
      funext who
      simp [βN, NativeFOSG.nativeBehavioralProfileToFOSG,
        NativeFOSG.fosgBehavioralProfileToNative]
    rw [← htransport]
    rw [hprofile]
  have hmixed :
      (eventGraphFOSGView g).boundedOutcomeFromMixed horizon μF horizon =
        (Math.PMFProduct.pmfPi μ).bind
          (fun π =>
            (eventGraphRoundView g).boundedOutcomeFromPure horizon π horizon) := by
    unfold Machine.FOSGView.boundedOutcomeFromMixed
    rw [reachableMixedProfileJoint_nativeToFOSG g horizon μ]
    rw [PMF.bind_map]
    apply congrArg
      (fun f =>
        (Math.PMFProduct.pmfPi μ).bind f)
    funext π
    exact NativeFOSG.boundedOutcomeFromPure_nativeToFOSG g horizon π horizon
  change
    (eventGraphRoundView g).boundedOutcomeFromBehavioral horizon βN horizon =
      (Math.PMFProduct.pmfPi μ).bind
        (fun π =>
          (eventGraphRoundView g).boundedOutcomeFromPure horizon π horizon)
  rw [hbehavioral]
  have hβF' :
      (eventGraphFOSGView g).boundedOutcomeFromBehavioral horizon βF horizon =
        (eventGraphFOSGView g).boundedOutcomeFromMixed horizon μF horizon := by
    simpa [horizon] using hβF
  rw [hβF']
  exact hmixed

end Vegas
