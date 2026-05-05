import Vegas.Protocol.Checked
import GameTheory.Languages.FOSG.Kuhn

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-!
# FOSG denotations for checked Vegas programs

This file is the public entrypoint for FOSG integration. The canonical
protocol carrier is the asynchronous `Machine`. Checked syntax
elaborates to `syntaxActionGraph`, then to
`graphMachine`; `toGraphFOSG`, `toGraphBoundedFOSG`, and
`toFiniteFOSG` are sequential FOSG presentations derived from that
single graph machine. The `toFOSG`/`toBoundedFOSG` names are aliases for that
same graph-machine presentation.

The cursor-world adapter `cursorFOSG` remains as a projection proof tool for
syntax-facing modules. It is not a semantic owner.
-/

/-- Canonical sequential denotation of a checked Vegas program as a FOSG.

This is the direct sequential presentation of the checked program's
action-graph machine. -/
noncomputable abbrev toGraphFOSG
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :=
  fosg g hctx

/-- Horizon-bounded graph-machine FOSG view of a checked Vegas program. -/
noncomputable abbrev toGraphBoundedFOSG
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat) :=
  boundedFOSG g hctx horizon

/-- Canonical sequential denotation of a checked Vegas program as a FOSG. -/
noncomputable abbrev toFOSG
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :=
  toGraphFOSG g hctx

/-- Horizon-bounded graph-machine FOSG view of a checked Vegas program. -/
noncomputable abbrev toBoundedFOSG
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat) :=
  toGraphBoundedFOSG g hctx horizon

/-- Syntax-horizon bounded graph-machine FOSG view. -/
noncomputable abbrev toFiniteFOSG
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :=
  finiteFOSG g hctx

theorem toBoundedFOSG_boundedHorizon
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat) :
    (toBoundedFOSG g hctx horizon).BoundedHorizon horizon :=
  (fosgView g hctx)
    |>.toBoundedFOSG_boundedHorizon horizon

theorem toGraphBoundedFOSG_boundedHorizon
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat) :
    (toGraphBoundedFOSG g hctx horizon).BoundedHorizon horizon :=
  (fosgView g hctx)
    |>.toBoundedFOSG_boundedHorizon horizon

/-- Endpoint outcome read from a bounded graph-machine FOSG history. -/
noncomputable def fosgHistoryOutcome
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat)
    (h : (toGraphBoundedFOSG g hctx horizon).History) : Outcome P :=
  (graphMachine g hctx).outcome h.lastState.lastState

/-- Outcome kernel for a reachable behavioral profile of the graph-machine
finite FOSG. Finite enumeration instances are fixed by `LF` and kept inside
the definition. -/
noncomputable def finiteFOSGReachableBehavioralOutcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (β : (toFiniteFOSG g hctx).ReachableLegalBehavioralProfile) :
    PMF (Outcome P) := by
  classical
  letI : Fintype (graphMachine g hctx).State :=
    graphMachine.instFintypeState g hctx LF
  letI : ∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who)) :=
    fun who => graphMachine.instFintypeOptionAction
      g hctx LF who
  letI : Fintype (graphMachine g hctx).Event :=
    graphMachine.instFintypeEvent g hctx LF
  letI :
      Fintype
        ((graphMachine g hctx).BoundedRunPrefix
          (syntaxSteps g.prog)) :=
    Machine.BoundedRunPrefix.instFintype
  letI : Fintype (toFiniteFOSG g hctx).History :=
    finiteFOSG.instFintypeHistory g hctx LF
  letI : DecidablePred (toFiniteFOSG g hctx).terminal :=
    Classical.decPred _
  exact
    PMF.map (fosgHistoryOutcome g hctx (syntaxSteps g.prog))
      ((toFiniteFOSG g hctx).runDist
        (syntaxSteps g.prog) β.extend)

/-- Graph-machine finite-FOSG Kuhn M→B theorem, stated over the reachable
legal pure strategy coordinates of the bounded graph-machine FOSG.

This is the machine-side finite Kuhn entry point for the canonical
action-graph machine. -/
theorem toFiniteFOSG_reachableMixedPure_realizedByLegalBehavioral_runDist
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who))]
    [Fintype
      ((graphMachine g hctx).BoundedRunPrefix
        (syntaxSteps g.prog))]
    [Fintype (toFiniteFOSG g hctx).History]
    [DecidablePred (toFiniteFOSG g hctx).terminal]
    (μ : GameTheory.FOSG.Kuhn.ReachableMixedProfile
      (G := toFiniteFOSG g hctx)) :
    ∃ β : (toFiniteFOSG g hctx).ReachableLegalBehavioralProfile,
      (toFiniteFOSG g hctx).runDist
          (syntaxSteps g.prog) β.extend =
        (GameTheory.FOSG.Kuhn.reachableMixedProfileJoint
          (G := toFiniteFOSG g hctx) μ).bind
          (fun π =>
            (toFiniteFOSG g hctx).runDist
              (syntaxSteps g.prog)
              ((toFiniteFOSG g hctx).legalPureToBehavioral
                π.extend)) := by
  exact
    GameTheory.FOSG.Kuhn.reachable_mixed_to_legal_behavioral_runDist
      (G := toFiniteFOSG g hctx)
      (finiteFOSG_legalObservable g hctx)
      μ (syntaxSteps g.prog)

/-- Outcome-pushforward form of graph-machine finite-FOSG Kuhn. -/
theorem toFiniteFOSG_reachableMixedPure_realizedByLegalBehavioral_mappedRunDist
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who))]
    [Fintype
      ((graphMachine g hctx).BoundedRunPrefix
        (syntaxSteps g.prog))]
    [Fintype (toFiniteFOSG g hctx).History]
    [DecidablePred (toFiniteFOSG g hctx).terminal]
    (μ : GameTheory.FOSG.Kuhn.ReachableMixedProfile
      (G := toFiniteFOSG g hctx)) :
    ∃ β : (toFiniteFOSG g hctx).ReachableLegalBehavioralProfile,
      PMF.map (fosgHistoryOutcome g hctx (syntaxSteps g.prog))
          ((toFiniteFOSG g hctx).runDist
            (syntaxSteps g.prog) β.extend) =
        (GameTheory.FOSG.Kuhn.reachableMixedProfileJoint
          (G := toFiniteFOSG g hctx) μ).bind
          (fun π =>
            PMF.map (fosgHistoryOutcome g hctx (syntaxSteps g.prog))
              ((toFiniteFOSG g hctx).runDist
                (syntaxSteps g.prog)
                ((toFiniteFOSG g hctx).legalPureToBehavioral
                  π.extend))) := by
  obtain ⟨β, hβ⟩ :=
    toFiniteFOSG_reachableMixedPure_realizedByLegalBehavioral_runDist
      g hctx μ
  refine ⟨β, ?_⟩
  have hmap :=
    congrArg
      (PMF.map (fosgHistoryOutcome g hctx (syntaxSteps g.prog)))
      hβ
  exact hmap.trans (PMF.map_bind
    (p := GameTheory.FOSG.Kuhn.reachableMixedProfileJoint
      (G := toFiniteFOSG g hctx) μ)
    (q := fun π =>
      (toFiniteFOSG g hctx).runDist
        (syntaxSteps g.prog)
        ((toFiniteFOSG g hctx).legalPureToBehavioral
          π.extend))
    (f := fosgHistoryOutcome g hctx (syntaxSteps g.prog)))

end Vegas
