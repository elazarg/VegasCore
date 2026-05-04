import Vegas.FOSG.Observed.Collapse
import Vegas.FOSG.Observed.Refinement
import Vegas.FOSG.Observed.Strategic
import Vegas.FOSG.SmallStep
import Vegas.Protocol.Checked
import Vegas.Protocol.Strategic
import Vegas.Protocol.StrategicCompatibility

namespace Vegas
namespace FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-!
# FOSG denotations for checked Vegas programs

This file is the public entrypoint for FOSG integration. The canonical
protocol carrier is the asynchronous `Machine`. Checked syntax
elaborates to `syntaxActionGraph`, then to
`graphMachine`; `toGraphFOSG`, `toGraphBoundedFOSG`, and
`toFiniteGraphMachineFOSG` are sequential FOSG presentations derived from that
single graph machine. The `toFOSG`/`toBoundedFOSG` names are aliases for that
same graph-machine presentation.

The cursor-world FOSG is still exposed as `toObservedFOSG`. It is not a
semantic owner; it is a syntax-facing projection layer related back to the
machine-derived semantics.
-/

/-- Canonical sequential denotation of a checked Vegas program as a FOSG.

This is the direct sequential presentation of the checked program's
action-graph machine. -/
noncomputable abbrev toGraphFOSG
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :=
  graphMachineFOSG g hctx

/-- Horizon-bounded graph-machine FOSG view of a checked Vegas program. -/
noncomputable abbrev toGraphBoundedFOSG
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat) :=
  boundedGraphMachineFOSG g hctx horizon

/-- Canonical sequential denotation of a checked Vegas program as a FOSG. -/
noncomputable abbrev toFOSG
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :=
  toGraphFOSG g hctx

/-- Horizon-bounded graph-machine FOSG view of a checked Vegas program. -/
noncomputable abbrev toBoundedFOSG
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat) :=
  toGraphBoundedFOSG g hctx horizon

/-- Syntax-horizon bounded graph-machine FOSG view. -/
noncomputable abbrev toFiniteGraphMachineFOSG
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :=
  finiteGraphMachineFOSG g hctx

/-- Finite observed FOSG adapter.

This is not the semantic ground truth. It is a syntax-facing projection layer;
the graph-machine FOSG is the sequential semantic carrier. -/
noncomputable abbrev toObservedFOSG
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :=
  observedProgramFOSG g hctx

theorem toObservedFOSG_legalObservable
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (toObservedFOSG g hctx).LegalObservable :=
  Observed.observedProgramFOSG_legalObservable g hctx

theorem toObservedFOSG_boundedHorizon
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (toObservedFOSG g hctx).BoundedHorizon (syntaxSteps g.prog) :=
  observedProgramFOSG_boundedHorizon g hctx

/-- Strategic KernelGame view of the finite observed FOSG adapter. -/
noncomputable abbrev toObservedFOSGKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P] : KernelGame P :=
  Observed.observedProgramReachableKernelGame g hctx LF

@[simp] theorem toObservedFOSGKernelGame_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (β : (toObservedFOSG g hctx).ReachableLegalBehavioralProfile) :
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
      fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
    letI : DecidablePred (toObservedFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    (toObservedFOSGKernelGame g hctx LF).outcomeKernel β =
      PMF.map (observedProgramHistoryOutcome g hctx)
        ((toObservedFOSG g hctx).runDist
          (syntaxSteps g.prog) β.extend) := by
  exact Observed.observedProgramReachableKernelGame_outcomeKernel
    g hctx LF β

/-- Finite observed-FOSG Kuhn M→B, specialized to product-mixed Vegas pure
strategies and stated as preservation of the Vegas outcome distribution. -/
theorem toObservedFOSG_mixedPure_realizedByBehavioral_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : KernelGame.Profile (toObservedFOSGKernelGame g hctx LF),
      (toObservedFOSGKernelGame g hctx LF).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toMachineStrategicKernelGame g hctx).outcomeKernel σ) := by
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  obtain ⟨β, hβ⟩ :=
    Observed.observedProgramReachableKernelGame_mixedPure_realization
      g hctx LF μ
  refine ⟨β, ?_⟩
  rw [hβ]
  exact (bind_toMachineStrategicKernelGame_outcomeKernel_eq_toStrategicKernelGame
    g hctx (Math.PMFProduct.pmfPi μ)).symm

/-- Finite observed-FOSG Kuhn M→B with a total legal FOSG behavioral witness.

The theorem preserves the Vegas outcome distribution. The behavioral witness is
total for the compiled FOSG information-state space; this is stronger than the
reachable-profile wrapper below, but it is still a FOSG strategy, not a Vegas
`SyntaxLegalProgramBehavioralProfilePMF`. -/
theorem toObservedFOSG_mixedPure_realizedByLegalBehavioral_runDist
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
      fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
    letI : Fintype (toObservedFOSG g hctx).History :=
      observedProgramFOSG.instFintypeHistory g hctx LF
    letI : DecidablePred (toObservedFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    ∃ β : (toObservedFOSG g hctx).LegalBehavioralProfile,
      PMF.map (observedProgramHistoryOutcome g hctx)
          ((toObservedFOSG g hctx).runDist (syntaxSteps g.prog) β) =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toMachineStrategicKernelGame g hctx).outcomeKernel σ) := by
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
    fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
  letI : Fintype (toObservedFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory g hctx LF
  letI : DecidablePred (toObservedFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  obtain ⟨β, hβ⟩ :=
    Observed.observedProgramFullFOSG_vegasMixedPure_runDist_toStrategicKernelGame_finite
      g hctx LF μ
  refine ⟨β, ?_⟩
  rw [hβ]
  exact (bind_toMachineStrategicKernelGame_outcomeKernel_eq_toStrategicKernelGame
    g hctx (Math.PMFProduct.pmfPi μ)).symm

theorem toBoundedFOSG_boundedHorizon
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat) :
    (toBoundedFOSG g hctx horizon).BoundedHorizon horizon :=
  (graphMachineFOSGView g hctx)
    |>.toBoundedFOSG_boundedHorizon horizon

theorem toGraphBoundedFOSG_boundedHorizon
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat) :
    (toGraphBoundedFOSG g hctx horizon).BoundedHorizon horizon :=
  (graphMachineFOSGView g hctx)
    |>.toBoundedFOSG_boundedHorizon horizon

/-- Endpoint outcome read from a bounded graph-machine FOSG history. -/
noncomputable def graphMachineFOSGHistoryOutcome
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (horizon : Nat)
    (h : (toGraphBoundedFOSG g hctx horizon).History) : Outcome P :=
  (graphMachine g hctx).outcome h.lastState.lastState

/-- Outcome kernel for a reachable behavioral profile of the graph-machine
finite FOSG. Finite enumeration instances are fixed by `LF` and kept inside
the definition. -/
noncomputable def finiteGraphMachineFOSGReachableBehavioralOutcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (β : (toFiniteGraphMachineFOSG g hctx).ReachableLegalBehavioralProfile) :
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
  letI : Fintype (toFiniteGraphMachineFOSG g hctx).History :=
    finiteGraphMachineFOSG.instFintypeHistory g hctx LF
  letI : DecidablePred (toFiniteGraphMachineFOSG g hctx).terminal :=
    Classical.decPred _
  exact
    PMF.map (graphMachineFOSGHistoryOutcome g hctx (syntaxSteps g.prog))
      ((toFiniteGraphMachineFOSG g hctx).runDist
        (syntaxSteps g.prog) β.extend)

/-- Graph-machine finite-FOSG Kuhn M→B theorem, stated over the reachable
legal pure strategy coordinates of the bounded graph-machine FOSG.

This is the machine-side finite Kuhn entry point for the canonical
action-graph machine. -/
theorem toFiniteGraphMachineFOSG_reachableMixedPure_realizedByLegalBehavioral_runDist
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who))]
    [Fintype
      ((graphMachine g hctx).BoundedRunPrefix
        (syntaxSteps g.prog))]
    [Fintype (toFiniteGraphMachineFOSG g hctx).History]
    [DecidablePred (toFiniteGraphMachineFOSG g hctx).terminal]
    (μ : GameTheory.FOSG.Kuhn.ReachableMixedProfile
      (G := toFiniteGraphMachineFOSG g hctx)) :
    ∃ β : (toFiniteGraphMachineFOSG g hctx).ReachableLegalBehavioralProfile,
      (toFiniteGraphMachineFOSG g hctx).runDist
          (syntaxSteps g.prog) β.extend =
        (GameTheory.FOSG.Kuhn.reachableMixedProfileJoint
          (G := toFiniteGraphMachineFOSG g hctx) μ).bind
          (fun π =>
            (toFiniteGraphMachineFOSG g hctx).runDist
              (syntaxSteps g.prog)
              ((toFiniteGraphMachineFOSG g hctx).legalPureToBehavioral
                π.extend)) := by
  exact
    GameTheory.FOSG.Kuhn.reachable_mixed_to_legal_behavioral_runDist
      (G := toFiniteGraphMachineFOSG g hctx)
      (finiteGraphMachineFOSG_legalObservable g hctx)
      μ (syntaxSteps g.prog)

/-- Outcome-pushforward form of graph-machine finite-FOSG Kuhn. -/
theorem toFiniteGraphMachineFOSG_reachableMixedPure_realizedByLegalBehavioral_mappedRunDist
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who))]
    [Fintype
      ((graphMachine g hctx).BoundedRunPrefix
        (syntaxSteps g.prog))]
    [Fintype (toFiniteGraphMachineFOSG g hctx).History]
    [DecidablePred (toFiniteGraphMachineFOSG g hctx).terminal]
    (μ : GameTheory.FOSG.Kuhn.ReachableMixedProfile
      (G := toFiniteGraphMachineFOSG g hctx)) :
    ∃ β : (toFiniteGraphMachineFOSG g hctx).ReachableLegalBehavioralProfile,
      PMF.map (graphMachineFOSGHistoryOutcome g hctx (syntaxSteps g.prog))
          ((toFiniteGraphMachineFOSG g hctx).runDist
            (syntaxSteps g.prog) β.extend) =
        (GameTheory.FOSG.Kuhn.reachableMixedProfileJoint
          (G := toFiniteGraphMachineFOSG g hctx) μ).bind
          (fun π =>
            PMF.map (graphMachineFOSGHistoryOutcome g hctx (syntaxSteps g.prog))
              ((toFiniteGraphMachineFOSG g hctx).runDist
                (syntaxSteps g.prog)
                ((toFiniteGraphMachineFOSG g hctx).legalPureToBehavioral
                  π.extend))) := by
  obtain ⟨β, hβ⟩ :=
    toFiniteGraphMachineFOSG_reachableMixedPure_realizedByLegalBehavioral_runDist
      g hctx μ
  refine ⟨β, ?_⟩
  have hmap :=
    congrArg
      (PMF.map (graphMachineFOSGHistoryOutcome g hctx (syntaxSteps g.prog)))
      hβ
  exact hmap.trans (PMF.map_bind
    (p := GameTheory.FOSG.Kuhn.reachableMixedProfileJoint
      (G := toFiniteGraphMachineFOSG g hctx) μ)
    (q := fun π =>
      (toFiniteGraphMachineFOSG g hctx).runDist
        (syntaxSteps g.prog)
        ((toFiniteGraphMachineFOSG g hctx).legalPureToBehavioral
          π.extend))
    (f := graphMachineFOSGHistoryOutcome g hctx (syntaxSteps g.prog)))

/-- Pure FOSG strategy induced by a Vegas legal pure strategy on the
syntax-horizon graph-machine FOSG. -/
noncomputable def toFiniteGraphMachineFOSGPureStrategyCandidate
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who) :
    GameTheory.FOSG.PureStrategy (toFiniteGraphMachineFOSG g hctx) who :=
  GameTheory.FOSG.PureStrategy.ofLatestObservation
    (G := toFiniteGraphMachineFOSG g hctx)
    (i := who)
    (Observed.movePureStrategyAtCursorWorld
      g hctx who σ (CursorCheckedWorld.initial g hctx))
    (Observed.movePureStrategyAtProgramObservation? g hctx who σ)

@[simp] theorem toFiniteGraphMachineFOSGPureStrategyCandidate_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who) :
    toFiniteGraphMachineFOSGPureStrategyCandidate g hctx who σ
        ((GameTheory.FOSG.History.nil
          (toFiniteGraphMachineFOSG g hctx)).playerView who) =
      Observed.movePureStrategyAtCursorWorld
        g hctx who σ (CursorCheckedWorld.initial g hctx) := by
  simp [toFiniteGraphMachineFOSGPureStrategyCandidate]

theorem toFiniteGraphMachineFOSGPureStrategyCandidate_history
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    (h : (toFiniteGraphMachineFOSG g hctx).History) :
    toFiniteGraphMachineFOSGPureStrategyCandidate g hctx who σ
        (h.playerView who) =
      Observed.movePureStrategyAtCursorWorld
        g hctx who σ
        (cursorWorldOfGraphConfiguration
          g hctx h.lastState.lastState) := by
  by_cases hnil : h.steps = []
  · have hh :
        h = GameTheory.FOSG.History.nil
          (toFiniteGraphMachineFOSG g hctx) := by
      cases h with
      | mk steps chain =>
          cases hnil
          rfl
    rw [hh]
    change
      Observed.movePureStrategyAtCursorWorld
          g hctx who σ (CursorCheckedWorld.initial g hctx) =
        Observed.movePureStrategyAtCursorWorld
          g hctx who σ
          (cursorWorldOfGraphConfiguration g hctx
            (ActionGraph.Configuration.initial
              (syntaxActionGraph g)))
    rw [cursorWorldOfGraphConfiguration_initial]
  · have hlatest :
        GameTheory.FOSG.InfoState.latestObservation?
            (G := toFiniteGraphMachineFOSG g hctx) (i := who)
            (h.playerView who) =
          some (privateObsOfCursorWorld who
              (cursorWorldOfGraphConfiguration
                g hctx h.lastState.lastState),
            publicObsOfCursorWorld (hctx := hctx)
              (cursorWorldOfGraphConfiguration
                g hctx h.lastState.lastState)) := by
      simpa [toFiniteGraphMachineFOSG, finiteGraphMachineFOSG,
        boundedGraphMachineFOSG,
        graphMachine, graphSemantics] using
        (graphMachineFOSGView g hctx)
          |>.toBoundedFOSG_latestObservation?_history_of_ne_nil
            (syntaxSteps g.prog) who h hnil
    simp [toFiniteGraphMachineFOSGPureStrategyCandidate,
      GameTheory.FOSG.PureStrategy.ofLatestObservation, hlatest,
      Observed.movePureStrategyAtProgramObservation?_of_cursorWorld]

theorem toFiniteGraphMachineFOSGPureStrategyCandidate_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    (h : (toFiniteGraphMachineFOSG g hctx).History) :
    toFiniteGraphMachineFOSGPureStrategyCandidate g hctx who σ
        (h.playerView who) ∈
      (toFiniteGraphMachineFOSG g hctx).availableMoves h who := by
  rw [toFiniteGraphMachineFOSGPureStrategyCandidate_history]
  by_cases hcut : syntaxSteps g.prog ≤ h.lastState.pref.events.length
  · have hterm :
        CursorCheckedWorld.terminal
          (cursorWorldOfGraphConfiguration
            g hctx h.lastState.lastState) :=
      finiteGraphMachineFOSG_terminal_endpoint_of_cutoff
        g hctx h hcut
    let move :=
      Observed.movePureStrategyAtCursorWorld
        g hctx who σ
        (cursorWorldOfGraphConfiguration
          g hctx h.lastState.lastState)
    have hobsAvail :
        move ∈ (observedProgramFOSG g hctx).availableMovesAtState
          (cursorWorldOfGraphConfiguration
            g hctx h.lastState.lastState) who :=
      Observed.movePureStrategyAtCursorWorld_available
        g hctx who σ
        (cursorWorldOfGraphConfiguration
          g hctx h.lastState.lastState)
    have hactiveEmpty :
        CursorCheckedWorld.active
          (cursorWorldOfGraphConfiguration
            g hctx h.lastState.lastState) = ∅ :=
      cursor_terminal_active_eq_empty hterm
    let G := toFiniteGraphMachineFOSG g hctx
    change move ∈ G.availableMoves h who
    have hInactive : who ∉ G.active h.lastState := by
      have hactiveG : G.active h.lastState = ∅ := by
        exact G.terminal_active_eq_empty (Or.inr hcut)
      rw [hactiveG]
      simp
    rw [G.availableMoves_eq_singleton_none_of_not_mem_active h hInactive]
    cases hmove : move with
    | none =>
        exact Set.mem_singleton
          (none : Option ((graphMachine g hctx).Action who))
    | some action =>
        have hmemActive :
            who ∈ CursorCheckedWorld.active
              (cursorWorldOfGraphConfiguration
                g hctx h.lastState.lastState) := by
          have hpair :
              who ∈ CursorCheckedWorld.active
                (cursorWorldOfGraphConfiguration
                  g hctx h.lastState.lastState) ∧
                action ∈
                  CursorCheckedWorld.availableProgramActions
                    (cursorWorldOfGraphConfiguration
                      g hctx h.lastState.lastState) who := by
            simpa [move, observedProgramFOSG,
              GameTheory.FOSG.availableMovesAtState,
              GameTheory.FOSG.locallyLegalAtState, hmove] using hobsAvail
          exact hpair.1
        rw [hactiveEmpty] at hmemActive
        simp at hmemActive
  · have havailable :=
      finiteGraphMachineFOSG_availableMoves_eq_observedProgram_of_not_cutoff
        g hctx who h hcut
    have hobs :
        Observed.movePureStrategyAtCursorWorld
            g hctx who σ
            (cursorWorldOfGraphConfiguration
              g hctx h.lastState.lastState) ∈
          (observedProgramFOSG g hctx).availableMovesAtState
            (cursorWorldOfGraphConfiguration
              g hctx h.lastState.lastState) who :=
      Observed.movePureStrategyAtCursorWorld_available
        g hctx who σ
        (cursorWorldOfGraphConfiguration
          g hctx h.lastState.lastState)
    exact havailable.symm ▸ hobs

/-- Legal pure strategy induced by a Vegas legal pure strategy on the
graph-machine finite FOSG. -/
noncomputable def toFiniteGraphMachineFOSGLegalPureStrategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who) :
    (toFiniteGraphMachineFOSG g hctx).LegalPureStrategy who :=
  ⟨toFiniteGraphMachineFOSGPureStrategyCandidate g hctx who σ,
    toFiniteGraphMachineFOSGPureStrategyCandidate_available g hctx who σ⟩

/-- Reachable-coordinate graph-machine-FOSG pure strategy induced by a Vegas
legal pure strategy. -/
noncomputable def toFiniteGraphMachineFOSGReachableLegalPureStrategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who) :
    (toFiniteGraphMachineFOSG g hctx).ReachableLegalPureStrategy who :=
  (toFiniteGraphMachineFOSGLegalPureStrategy g hctx who σ).restrictReachable

/-- Reachable-coordinate graph-machine-FOSG pure profile induced pointwise by
a Vegas legal pure profile. -/
noncomputable def toFiniteGraphMachineFOSGReachableLegalPureProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) :
    (toFiniteGraphMachineFOSG g hctx).ReachableLegalPureProfile :=
  fun who =>
    toFiniteGraphMachineFOSGReachableLegalPureStrategy g hctx who (σ who)

theorem toFiniteGraphMachineFOSG_pure_actionLaw_bind_checkedTransition_eq_checkedProfileStepPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who))]
    (σ : LegalProgramPureProfile g)
    (h : (toFiniteGraphMachineFOSG g hctx).History)
    (hterm : ¬ (toFiniteGraphMachineFOSG g hctx).terminal h.lastState) :
    ((toFiniteGraphMachineFOSG g hctx).legalActionLaw
        ((toFiniteGraphMachineFOSG g hctx).legalPureToBehavioral
          (toFiniteGraphMachineFOSGReachableLegalPureProfile
            g hctx σ).extend)
        h hterm).bind
      (fun action =>
        PMF.map
          (fun dst :
            (graphMachine g hctx).BoundedRunPrefix
              (syntaxSteps g.prog) =>
            CheckedWorld.ofCursorChecked (hctx := hctx)
              (cursorWorldOfGraphConfiguration
                g hctx dst.lastState))
          ((toFiniteGraphMachineFOSG g hctx).transition
            h.lastState action)) =
      Observed.checkedProfileStepPMF g hctx
        (LegalProgramPureProfile.toBehavioralPMF σ)
        (CheckedWorld.ofCursorChecked (hctx := hctx)
          (cursorWorldOfGraphConfiguration
            g hctx h.lastState.lastState)) := by
  classical
  let G := toFiniteGraphMachineFOSG g hctx
  let β : G.LegalBehavioralProfile :=
    G.legalPureToBehavioral
      (toFiniteGraphMachineFOSGReachableLegalPureProfile g hctx σ).extend
  have hnotCut :
      ¬ syntaxSteps g.prog ≤ h.lastState.pref.events.length := by
    intro hcut
    exact hterm (Or.inr hcut)
  have hcursor :
      ¬ CursorCheckedWorld.terminal
        (cursorWorldOfGraphConfiguration
          g hctx h.lastState.lastState) :=
    finiteGraphMachineFOSG_cursor_nonterminal_of_not_terminal
      g hctx h hterm
  have hnotGraph :
      ¬ (graphMachine g hctx).terminal
        h.lastState.lastState := by
    intro hgraph
    exact hterm (Or.inl hgraph)
  by_cases hactive : G.active h.lastState = ∅
  · rw [G.legalActionLaw_eq_pure_noop_of_active_empty β h hterm hactive]
    simp only [PMF.pure_bind]
    have hactiveCursor :
        CursorCheckedWorld.active
          (cursorWorldOfGraphConfiguration
            g hctx h.lastState.lastState) = ∅ := by
      have hview :
          (graphMachineFOSGView g hctx).active
              h.lastState.pref = ∅ := by
        have hbounded :
            (if syntaxSteps g.prog ≤ h.lastState.pref.events.length then ∅
             else (graphMachineFOSGView g hctx).active
                h.lastState.pref) = ∅ := by
          simpa [G, toFiniteGraphMachineFOSG,
            finiteGraphMachineFOSG,
            boundedGraphMachineFOSG,
            Machine.FOSGView.boundedActive] using hactive
        rwa [if_neg hnotCut] at hbounded
      simpa [graphMachineFOSGView_active_eq_cursor_active_of_not_terminal
        g hctx h.lastState.pref hnotGraph,
        Machine.BoundedRunPrefix.lastState] using hview
    let noop : G.LegalAction h.lastState :=
      ⟨GameTheory.FOSG.noopAction
          (graphMachine g hctx).Action,
        G.legal_noopAction_of_active_empty_of_not_terminal hactive hterm⟩
    have htrans :=
      boundedGraphMachineFOSG_transition_map_checkedWorld_eq_checkedTransition
        g hctx (syntaxSteps g.prog) h.lastState noop hcursor
    calc
      PMF.map
          (fun dst :
            (graphMachine g hctx).BoundedRunPrefix
              (syntaxSteps g.prog) =>
            CheckedWorld.ofCursorChecked (hctx := hctx)
              (cursorWorldOfGraphConfiguration
                g hctx dst.lastState))
          (G.transition h.lastState noop)
        =
          checkedTransition
            (CheckedWorld.ofCursorChecked (hctx := hctx)
              (cursorWorldOfGraphConfiguration
                g hctx h.lastState.lastState))
            ⟨ProgramJointAction.toAction
                (graphMachineJointAction g hctx
                  ((graphMachineFOSGView g hctx)
                    |>.boundedEventOfLegalJointAction
                      (syntaxSteps g.prog) h.lastState noop)),
              CursorProgramJointActionLegal.toAction
                (cursorProgramJointActionLegal_of_graphMachine_available
                  g hctx hcursor
                  ((graphMachineFOSGView g hctx)
                    |>.boundedEventOfLegalJointAction_available
                      (syntaxSteps g.prog) h.lastState noop))⟩ := by
            simpa [G, toFiniteGraphMachineFOSG,
              finiteGraphMachineFOSG] using htrans
      _ =
          Observed.checkedProfileStepPMF g hctx
            (LegalProgramPureProfile.toBehavioralPMF σ)
            (CheckedWorld.ofCursorChecked (hctx := hctx)
              (cursorWorldOfGraphConfiguration
                g hctx h.lastState.lastState)) := by
            apply Observed.checkedTransition_eq_checkedProfileStepPMF_of_active_empty
            simpa [checkedActive, CheckedWorld.ofCursorChecked,
              CursorCheckedWorld.active] using hactiveCursor
  · have hne : (G.active h.lastState).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hactive
    rcases hne with ⟨who, hmem⟩
    have hmemCursor :
        who ∈ (observedProgramFOSG g hctx).active
          (cursorWorldOfGraphConfiguration
            g hctx h.lastState.lastState) := by
      have hmemRaw :
          who ∈
            (if syntaxSteps g.prog ≤ h.lastState.pref.events.length then ∅
             else (graphMachineFOSGView g hctx).active
                h.lastState.pref) := by
        simpa [G, toFiniteGraphMachineFOSG,
          finiteGraphMachineFOSG,
          boundedGraphMachineFOSG,
          Machine.FOSGView.boundedActive]
          using hmem
      rw [if_neg hnotCut] at hmemRaw
      have hmem' :
          who ∈ CursorCheckedWorld.active
            (cursorWorldOfGraphConfiguration
              g hctx h.lastState.pref.lastState) := by
        simpa [graphMachineFOSGView_active_eq_cursor_active_of_not_terminal
          g hctx h.lastState.pref hnotGraph,
          Machine.BoundedRunPrefix.lastState] using hmemRaw
      simpa [observedProgramFOSG,
        Machine.BoundedRunPrefix.lastState] using hmem'
    rcases Observed.observedProgram_active_mem_commitData
        g hctx
        (cursorWorldOfGraphConfiguration
          g hctx h.lastState.lastState) hmemCursor with
      ⟨Γ, x, b, R, k, env, suffix, wctx, fresh, viewScoped,
        normalized, legal, hchecked, hworld, _hobs⟩
    have hK : ∀ action : G.LegalAction h.lastState,
        PMF.map
          (fun dst :
            (graphMachine g hctx).BoundedRunPrefix
              (syntaxSteps g.prog) =>
            CheckedWorld.ofCursorChecked (hctx := hctx)
              (cursorWorldOfGraphConfiguration
                g hctx dst.lastState))
          (G.transition h.lastState action) =
        Observed.checkedCommitContinuation
          g hctx env suffix wctx fresh viewScoped normalized legal
          (action.1 who) := by
      intro action
      let selectedEvent :=
        (graphMachineFOSGView g hctx).boundedEventOfLegalJointAction
          (syntaxSteps g.prog) h.lastState action
      let selectedAction :=
        graphMachineJointAction g hctx selectedEvent
      have hselectedAvailable :
          (graphMachine g hctx).EventAvailable
            h.lastState.lastState selectedEvent := by
        simpa [selectedEvent] using
          ((graphMachineFOSGView g hctx)
            |>.boundedEventOfLegalJointAction_available
              (syntaxSteps g.prog) h.lastState action)
      have hselectedLegalCursor :
          CursorProgramJointActionLegal
            (cursorWorldOfGraphConfiguration
              g hctx h.lastState.lastState) selectedAction := by
        simpa [selectedAction] using
          cursorProgramJointActionLegal_of_graphMachine_available
            g hctx hcursor hselectedAvailable
      have hmemBounded :
          who ∈
            (boundedGraphMachineFOSG
              g hctx (syntaxSteps g.prog)).active h.lastState := by
        simpa [G, toFiniteGraphMachineFOSG,
          finiteGraphMachineFOSG] using hmem
      have hselectedWho : selectedAction who = action.1 who := by
        simpa [selectedAction, selectedEvent] using
          graphMachineJointAction_selected_eq_of_active
            g hctx (syntaxSteps g.prog) action hmemBounded
      have htrans :=
        boundedGraphMachineFOSG_transition_map_checkedWorld_eq_checkedTransition
          g hctx (syntaxSteps g.prog) h.lastState action hcursor
      have haRaw : JointActionLegal
          ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } :
            World P L)
          (ProgramJointAction.toAction selectedAction) := by
        have hto :=
          CursorProgramJointActionLegal.toAction
            hselectedLegalCursor
        simpa [hworld, selectedAction] using hto
      calc
        PMF.map
            (fun dst :
              (graphMachine g hctx).BoundedRunPrefix
                (syntaxSteps g.prog) =>
              CheckedWorld.ofCursorChecked (hctx := hctx)
                (cursorWorldOfGraphConfiguration
                  g hctx dst.lastState))
            (G.transition h.lastState action)
          =
            checkedTransition
              (CheckedWorld.ofCursorChecked (hctx := hctx)
                (cursorWorldOfGraphConfiguration
                  g hctx h.lastState.lastState))
              ⟨ProgramJointAction.toAction selectedAction,
                CursorProgramJointActionLegal.toAction
                  hselectedLegalCursor⟩ := by
              simpa [G, toFiniteGraphMachineFOSG,
                finiteGraphMachineFOSG,
                selectedEvent, selectedAction] using htrans
        _ =
            Observed.checkedCommitContinuation
              g hctx env suffix wctx fresh viewScoped normalized legal
              (action.1 who) := by
              rw [checkedTransition_congr_checkedWorld
                (hw := hchecked)
                (a := ProgramJointAction.toAction selectedAction)
                (ha₂ := by
                  simpa [CheckedJointActionLegal, checkedActive, checkedTerminal,
                    checkedAvailableActions, CheckedWorld.toWorld] using haRaw)]
              simpa [Observed.checkedCommitContinuation, hselectedWho] using
                checkedTransition_commit_eq_programActionContinuation
                  g hctx env suffix wctx fresh viewScoped
                  normalized legal selectedAction haRaw
    calc
      (G.legalActionLaw β h hterm).bind
          (fun action =>
            PMF.map
              (fun dst :
                (graphMachine g hctx).BoundedRunPrefix
                  (syntaxSteps g.prog) =>
                CheckedWorld.ofCursorChecked (hctx := hctx)
                  (cursorWorldOfGraphConfiguration
                    g hctx dst.lastState))
              (G.transition h.lastState action))
        =
          (G.legalActionLaw β h hterm).bind
            (fun action =>
              Observed.checkedCommitContinuation
                g hctx env suffix wctx fresh viewScoped normalized legal
                (action.1 who)) := by
            congr
            funext action
            exact hK action
      _ =
          ((β.toProfile who) (h.playerView who)).bind
            (Observed.checkedCommitContinuation
              g hctx env suffix wctx fresh viewScoped normalized legal) := by
            exact G.legalActionLaw_bind_coord β h hterm who
              (Observed.checkedCommitContinuation
                g hctx env suffix wctx fresh viewScoped normalized legal)
      _ =
          Observed.checkedProfileStepPMF g hctx
            (LegalProgramPureProfile.toBehavioralPMF σ)
            (CheckedWorld.ofCursorChecked (hctx := hctx)
              (cursorWorldOfGraphConfiguration
                g hctx h.lastState.lastState)) := by
            have hprofile :
                ((β.toProfile who) (h.playerView who)) =
                  PMF.pure
                    (Observed.movePureStrategyAtCursorWorld
                      g hctx who (σ who)
                      (cursorWorldOfGraphConfiguration
                        g hctx h.lastState.lastState)) := by
              change
                PMF.pure
                    (((toFiniteGraphMachineFOSGReachableLegalPureProfile
                        g hctx σ).toProfile who).extend
                      (h.playerView who)) =
                  PMF.pure
                    (Observed.movePureStrategyAtCursorWorld
                      g hctx who (σ who)
                      (cursorWorldOfGraphConfiguration
                        g hctx h.lastState.lastState))
              rw [GameTheory.FOSG.ReachablePureStrategy.extend_apply_history]
              change
                PMF.pure
                    ((toFiniteGraphMachineFOSGReachableLegalPureStrategy
                        g hctx who (σ who)).1
                      (G.reachableInfoStateOfHistory who h)) =
                  PMF.pure
                    (Observed.movePureStrategyAtCursorWorld
                      g hctx who (σ who)
                      (cursorWorldOfGraphConfiguration
                        g hctx h.lastState.lastState))
              change
                PMF.pure
                    ((toFiniteGraphMachineFOSGLegalPureStrategy
                        g hctx who (σ who)).1.restrictReachable
                      (G.reachableInfoStateOfHistory who h)) =
                  PMF.pure
                    (Observed.movePureStrategyAtCursorWorld
                      g hctx who (σ who)
                      (cursorWorldOfGraphConfiguration
                        g hctx h.lastState.lastState))
              change
                PMF.pure
                    (toFiniteGraphMachineFOSGPureStrategyCandidate
                      g hctx who (σ who)
                      ((G.reachableInfoStateOfHistory who h).1)) =
                  PMF.pure
                    (Observed.movePureStrategyAtCursorWorld
                      g hctx who (σ who)
                      (cursorWorldOfGraphConfiguration
                        g hctx h.lastState.lastState))
              simp only [GameTheory.FOSG.reachableInfoStateOfHistory_val]
              rw [toFiniteGraphMachineFOSGPureStrategyCandidate_history]
              rfl
            rw [hprofile]
            have hpureMove :
                Observed.movePureAtCursorWorld g hctx σ who
                    (cursorWorldOfGraphConfiguration
                      g hctx h.lastState.lastState) =
                  Observed.movePureStrategyAtCursorWorld
                    g hctx who (σ who)
                    (cursorWorldOfGraphConfiguration
                      g hctx h.lastState.lastState) := by
              unfold Observed.movePureAtCursorWorld
                Observed.movePureStrategyAtCursorWorld
              exact Observed.movePureAtProgramCursor_eq_strategy
                g hctx σ who _ _
            rw [← hpureMove]
            rw [← Observed.moveAtCursorWorldPMF_toBehavioralPMF_eq_pure
              g hctx σ who
              (cursorWorldOfGraphConfiguration
                g hctx h.lastState.lastState)]
            rw [← Observed.moveAtCheckedWorldPMF_ofCursorChecked
              g hctx (LegalProgramPureProfile.toBehavioralPMF σ)
              who
              (cursorWorldOfGraphConfiguration
                g hctx h.lastState.lastState)]
            rw [hchecked]
            exact
              Observed.moveAtProgramCursorPMF_bind_commitContinuation_eq_checkedProfileStepPMF
                g hctx (LegalProgramPureProfile.toBehavioralPMF σ)
                env suffix wctx fresh viewScoped normalized legal

/-- History-indexed continuation value for the finite graph-machine FOSG under
a Vegas pure profile. -/
noncomputable def finiteGraphMachineFOSGPureOutcomeValuePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who))]
    (σ : LegalProgramPureProfile g) :
    GameTheory.FOSG.History.OutcomeValue
      (G := toFiniteGraphMachineFOSG g hctx)
      ((toFiniteGraphMachineFOSG g hctx).legalPureToBehavioral
        (toFiniteGraphMachineFOSGReachableLegalPureProfile
          g hctx σ).extend)
      (Outcome P) where
  rank := fun h =>
    (cursorWorldOfGraphConfiguration
      g hctx h.lastState.lastState).remainingSyntaxSteps
  observe := fun h =>
    cursorWorldOutcome
      (cursorWorldOfGraphConfiguration
        g hctx h.lastState.lastState)
  value := fun h =>
    Observed.cursorVegasOutcomeKernelPMF
      (LegalProgramPureProfile.toBehavioralPMF σ)
      (cursorWorldOfGraphConfiguration
        g hctx h.lastState.lastState)
  terminal_of_rank_zero := by
    intro h hrank
    have hinv :=
      finiteGraphMachineFOSG_history_remainingSyntaxSteps
        g hctx h
    have hcut : Vegas.syntaxSteps g.prog ≤ h.lastState.pref.events.length := by
      have hsteps : Vegas.syntaxSteps g.prog ≤ h.steps.length := by
        rw [hrank] at hinv
        omega
      have hlen :=
        (graphMachineFOSGView g hctx)
          |>.toBoundedFOSG_history_events_length (syntaxSteps g.prog) h
      have hlen' :
          h.lastState.pref.events.length = h.steps.length := by
        simpa [GameTheory.FOSG.History.lastState,
          finiteGraphMachineFOSG,
          boundedGraphMachineFOSG] using hlen
      rw [← hlen'] at hsteps
      exact hsteps
    exact Or.inr hcut
  terminal_value := by
    intro h hterm
    have hterm' :
        (finiteGraphMachineFOSG g hctx).terminal
          h.lastState := by
      simpa [toFiniteGraphMachineFOSG] using hterm
    have hcursor :=
      finiteGraphMachineFOSG_cursor_terminal_of_terminal
        g hctx h hterm'
    exact Observed.cursorVegasOutcomeKernelPMF_terminal
      (hctx := hctx) (LegalProgramPureProfile.toBehavioralPMF σ)
      (cursorWorldOfGraphConfiguration
        g hctx h.lastState.lastState) hcursor
  step_value := by
    intro h hterm
    let G := toFiniteGraphMachineFOSG g hctx
    let β : G.LegalBehavioralProfile :=
      G.legalPureToBehavioral
        (toFiniteGraphMachineFOSGReachableLegalPureProfile g hctx σ).extend
    have hcheckedStep :=
      toFiniteGraphMachineFOSG_pure_actionLaw_bind_checkedTransition_eq_checkedProfileStepPMF
        g hctx σ h hterm
    calc
      (G.legalActionLaw β h hterm).bind
          (fun action =>
            (G.transition h.lastState action).bind
              (fun dst =>
                Observed.cursorVegasOutcomeKernelPMF
                  (LegalProgramPureProfile.toBehavioralPMF σ)
                  (cursorWorldOfGraphConfiguration
                    g hctx
                    (h.extendByOutcome action dst).lastState.lastState))) =
        (G.legalActionLaw β h hterm).bind
          (fun action =>
            (G.transition h.lastState action).bind
              (fun dst =>
                Observed.cursorVegasOutcomeKernelPMF
                  (LegalProgramPureProfile.toBehavioralPMF σ)
                  (cursorWorldOfGraphConfiguration
                    g hctx dst.lastState))) := by
            congr
            funext action
            refine Math.ProbabilityMassFunction.bind_congr_on_support
              (G.transition h.lastState action)
              (fun dst =>
                Observed.cursorVegasOutcomeKernelPMF
                  (LegalProgramPureProfile.toBehavioralPMF σ)
                  (cursorWorldOfGraphConfiguration
                    g hctx
                    (h.extendByOutcome action dst).lastState.lastState))
              (fun dst =>
                Observed.cursorVegasOutcomeKernelPMF
                  (LegalProgramPureProfile.toBehavioralPMF σ)
                  (cursorWorldOfGraphConfiguration
                    g hctx dst.lastState)) ?_
            intro dst hdst
            have hsupp : G.transition h.lastState action dst ≠ 0 := by
              simpa [PMF.mem_support_iff] using hdst
            have hlast :
                (h.extendByOutcome action dst).lastState = dst := by
              rw [GameTheory.FOSG.History.extendByOutcome_of_support
                (h := h) (a := action) (dst := dst) hsupp]
              simp
            simp [hlast]
      _ =
        ((G.legalActionLaw β h hterm).bind
          (fun action =>
            PMF.map
              (fun dst :
                (graphMachine g hctx).BoundedRunPrefix
                  (syntaxSteps g.prog) =>
                CheckedWorld.ofCursorChecked (hctx := hctx)
                  (cursorWorldOfGraphConfiguration
                    g hctx dst.lastState))
              (G.transition h.lastState action))).bind
            (Observed.checkedVegasOutcomeKernelPMF
              (hctx := hctx)
              (LegalProgramPureProfile.toBehavioralPMF σ)) := by
            rw [PMF.bind_bind]
            congr
            funext action
            simp [PMF.map, PMF.bind_bind, Function.comp_def]
      _ =
        (Observed.checkedProfileStepPMF g hctx
          (LegalProgramPureProfile.toBehavioralPMF σ)
          (CheckedWorld.ofCursorChecked (hctx := hctx)
            (cursorWorldOfGraphConfiguration
              g hctx h.lastState.lastState))).bind
          (Observed.checkedVegasOutcomeKernelPMF
            (hctx := hctx)
            (LegalProgramPureProfile.toBehavioralPMF σ)) := by
            rw [hcheckedStep]
      _ =
        Observed.checkedVegasOutcomeKernelPMF
          (hctx := hctx)
          (LegalProgramPureProfile.toBehavioralPMF σ)
          (CheckedWorld.ofCursorChecked (hctx := hctx)
            (cursorWorldOfGraphConfiguration
              g hctx h.lastState.lastState)) := by
            exact Observed.checkedProfileStepPMF_bind_checkedVegasOutcomeKernelPMF
              g hctx (LegalProgramPureProfile.toBehavioralPMF σ)
              (CheckedWorld.ofCursorChecked (hctx := hctx)
                (cursorWorldOfGraphConfiguration
                  g hctx h.lastState.lastState))
      _ =
        Observed.cursorVegasOutcomeKernelPMF
          (LegalProgramPureProfile.toBehavioralPMF σ)
          (cursorWorldOfGraphConfiguration
            g hctx h.lastState.lastState) := rfl
  step_rank := by
    intro h hterm action dst hsupp
    have hterm' :
        ¬ (finiteGraphMachineFOSG g hctx).terminal
          h.lastState := by
      simpa [toFiniteGraphMachineFOSG] using hterm
    have hcursor :=
      finiteGraphMachineFOSG_cursor_nonterminal_of_not_terminal
        g hctx h hterm'
    have hsupp' :
        (boundedGraphMachineFOSG g hctx
            (syntaxSteps g.prog)).transition h.lastState action dst ≠ 0 := by
      simpa [toFiniteGraphMachineFOSG, finiteGraphMachineFOSG]
        using hsupp
    have hlast :
        (h.extendByOutcome action dst).lastState = dst := by
      rw [GameTheory.FOSG.History.extendByOutcome_of_support
        (h := h) (a := action) (dst := dst) hsupp]
      simp
    have hremaining :=
      boundedGraphMachineFOSG_transition_support_remainingSyntaxSteps
        (dst := dst) g hctx (syntaxSteps g.prog) h.lastState
        action hsupp' hcursor
    simpa [hlast] using hremaining

/-- Pure Vegas strategies have the same outcome distribution through the
finite graph-machine-derived FOSG as through the native strategic kernel game. -/
theorem toFiniteGraphMachineFOSG_vegasPure_runDist_eq_toMachineStrategicKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who))]
    [Fintype
      ((graphMachine g hctx).BoundedRunPrefix
        (syntaxSteps g.prog))]
    [DecidablePred (toFiniteGraphMachineFOSG g hctx).terminal]
    (σ : LegalProgramPureProfile g) :
    PMF.map (graphMachineFOSGHistoryOutcome g hctx (syntaxSteps g.prog))
        ((toFiniteGraphMachineFOSG g hctx).runDist
          (syntaxSteps g.prog)
          ((toFiniteGraphMachineFOSG g hctx).legalPureToBehavioral
            (toFiniteGraphMachineFOSGReachableLegalPureProfile
              g hctx σ).extend)) =
      (toMachineStrategicKernelGame g hctx).outcomeKernel σ := by
  classical
  let R := finiteGraphMachineFOSGPureOutcomeValuePMF g hctx σ
  have hclosure :=
    R.map_observe_runDist_eq_value
      (syntaxSteps g.prog)
      (by
        change syntaxSteps g.prog ≤ syntaxSteps g.prog
        exact Nat.le_refl _)
  have hvalue :
      Observed.cursorVegasOutcomeKernelPMF
          (LegalProgramPureProfile.toBehavioralPMF σ)
          (CursorCheckedWorld.initial g hctx) =
        (toKernelGamePMF g).outcomeKernel
          (LegalProgramPureProfile.toBehavioralPMF σ) := by
    exact
      (GraphEventLaw.lawOfBehavioralPMF_outcomeKernel_eq_cursorVegasOutcomeKernelPMF
        (g := g) (hctx := hctx)
        (σ := LegalProgramPureProfile.toBehavioralPMF σ)).symm.trans
        (GraphEventLaw.lawOfBehavioralPMF_outcomeKernel_eq_toKernelGamePMF
          (g := g) (LegalProgramPureProfile.toBehavioralPMF σ) hctx)
  have hmachine :
      PMF.map (graphMachineFOSGHistoryOutcome g hctx (syntaxSteps g.prog))
          ((toFiniteGraphMachineFOSG g hctx).runDist
            (syntaxSteps g.prog)
            ((toFiniteGraphMachineFOSG g hctx).legalPureToBehavioral
              (toFiniteGraphMachineFOSGReachableLegalPureProfile
                g hctx σ).extend)) =
        Observed.cursorVegasOutcomeKernelPMF
          (LegalProgramPureProfile.toBehavioralPMF σ)
          (CursorCheckedWorld.initial g hctx) := by
    simpa [graphMachineFOSGHistoryOutcome, graphMachine,
      graphSemantics, graphMachine_init,
      cursorWorldOfGraphConfiguration_initial, R,
      finiteGraphMachineFOSGPureOutcomeValuePMF] using hclosure
  rw [hmachine, hvalue]
  rw [toKernelGamePMF_outcomeKernel_eq_toStrategicKernelGame_toBehavioralPMF]
  exact (toMachineStrategicKernelGame_outcomeKernel_eq_toStrategicKernelGame
    g hctx σ).symm

/-- Legacy spelling of the pure finite graph-machine FOSG bridge, stated
against `toStrategicKernelGame`. New code should use
`toFiniteGraphMachineFOSG_vegasPure_runDist_eq_toMachineStrategicKernelGame`. -/
theorem toFiniteGraphMachineFOSG_vegasPure_runDist_eq_toStrategicKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who))]
    [Fintype
      ((graphMachine g hctx).BoundedRunPrefix
        (syntaxSteps g.prog))]
    [DecidablePred (toFiniteGraphMachineFOSG g hctx).terminal]
    (σ : LegalProgramPureProfile g) :
    PMF.map (graphMachineFOSGHistoryOutcome g hctx (syntaxSteps g.prog))
        ((toFiniteGraphMachineFOSG g hctx).runDist
          (syntaxSteps g.prog)
          ((toFiniteGraphMachineFOSG g hctx).legalPureToBehavioral
            (toFiniteGraphMachineFOSGReachableLegalPureProfile
              g hctx σ).extend)) =
      (toStrategicKernelGame g).outcomeKernel σ := by
  rw [toFiniteGraphMachineFOSG_vegasPure_runDist_eq_toMachineStrategicKernelGame]
  exact toMachineStrategicKernelGame_outcomeKernel_eq_toStrategicKernelGame
    g hctx σ

/-- Product mixed profile over finite graph-machine-FOSG reachable pure
strategies induced by a product mixed profile over Vegas legal pure strategies. -/
noncomputable def toFiniteGraphMachineFOSGReachableMixedPureProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    GameTheory.FOSG.Kuhn.ReachableMixedProfile
      (G := toFiniteGraphMachineFOSG g hctx) :=
  fun who =>
    PMF.map (toFiniteGraphMachineFOSGReachableLegalPureStrategy g hctx who)
      (μ who)

theorem toFiniteGraphMachineFOSGReachableMixedPureProfile_joint
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who, Fintype (LegalProgramPureStrategy g who)]
    [∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who))]
    [Fintype (toFiniteGraphMachineFOSG g hctx).History]
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    GameTheory.FOSG.Kuhn.reachableMixedProfileJoint
        (G := toFiniteGraphMachineFOSG g hctx)
        (toFiniteGraphMachineFOSGReachableMixedPureProfile g hctx μ) =
      PMF.map (toFiniteGraphMachineFOSGReachableLegalPureProfile g hctx)
        (Math.PMFProduct.pmfPi μ) := by
  classical
  change Math.PMFProduct.pmfPi
      (fun who =>
        PMF.map (toFiniteGraphMachineFOSGReachableLegalPureStrategy g hctx who)
          (μ who)) =
    PMF.map
      (fun σ => fun who =>
        toFiniteGraphMachineFOSGReachableLegalPureStrategy g hctx who (σ who))
      (Math.PMFProduct.pmfPi μ)
  exact (Math.PMFProduct.pmfPi_push_coordwise μ
    (fun who => toFiniteGraphMachineFOSGReachableLegalPureStrategy g hctx who)).symm

/-- Product-mixed Vegas-pure specialization of the graph-machine finite-FOSG
Kuhn theorem. -/
theorem toFiniteGraphMachineFOSG_vegasMixedPure_realizedByLegalBehavioral_mappedRunDist
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who, Fintype (LegalProgramPureStrategy g who)]
    [∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who))]
    [Fintype
      ((graphMachine g hctx).BoundedRunPrefix
        (syntaxSteps g.prog))]
    [Finite (toFiniteGraphMachineFOSG g hctx).History]
    [DecidablePred (toFiniteGraphMachineFOSG g hctx).terminal]
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    ∃ β : (toFiniteGraphMachineFOSG g hctx).ReachableLegalBehavioralProfile,
      PMF.map (graphMachineFOSGHistoryOutcome g hctx (syntaxSteps g.prog))
          ((toFiniteGraphMachineFOSG g hctx).runDist
            (syntaxSteps g.prog) β.extend) =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toMachineStrategicKernelGame g hctx).outcomeKernel σ) := by
  letI : Fintype (toFiniteGraphMachineFOSG g hctx).History :=
    Fintype.ofFinite _
  obtain ⟨β, hβ⟩ :=
    toFiniteGraphMachineFOSG_reachableMixedPure_realizedByLegalBehavioral_mappedRunDist
      g hctx (toFiniteGraphMachineFOSGReachableMixedPureProfile g hctx μ)
  refine ⟨β, ?_⟩
  rw [toFiniteGraphMachineFOSGReachableMixedPureProfile_joint] at hβ
  rw [PMF.bind_map] at hβ
  rw [hβ]
  apply congrArg
  funext σ
  exact toFiniteGraphMachineFOSG_vegasPure_runDist_eq_toMachineStrategicKernelGame
    g hctx σ

/-- Finite observed-FOSG Kuhn M→B projected back to Vegas'
syntax-recursive PMF behavioral strategy space.

The witness is a total guard-legal Vegas behavioral profile. Off-path syntax
views are filled from an arbitrary pure profile selected from the input mixed
profile's support; the outcome equation is independent of this completion. -/
theorem mixedPure_realizedBySyntaxLegalBehavioralPMF_finite
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : SyntaxLegalProgramBehavioralProfilePMF g,
      (toMachineKernelGamePMF g hctx).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toMachineStrategicKernelGame g hctx).outcomeKernel σ) := by
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
    fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
  letI : Fintype (toObservedFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory g hctx LF
  letI : DecidablePred (toObservedFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  obtain ⟨βF, hβF⟩ :=
    toObservedFOSG_mixedPure_realizedByLegalBehavioral_runDist
      g hctx LF μ
  let fallbackPure : LegalProgramPureProfile g := fun who =>
    (μ who).support_nonempty.choose
  let fallback : SyntaxLegalProgramBehavioralProfilePMF g :=
    LegalProgramPureProfile.toBehavioralPMF fallbackPure
  refine
    ⟨Observed.collapsedLegalBehavioralProfilePMF
        g hctx βF fallback, ?_⟩
  rw [toMachineKernelGamePMF_outcomeKernel_eq_toKernelGamePMF]
  rw [← Observed.observedProgramCollapsedOutcomeKernelPMF_eq_toKernelGamePMF
    g hctx LF βF fallback]
  simpa [Observed.observedProgramCollapsedOutcomeKernelPMF] using hβF

end FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- IR-based legal PMF behavioral strategy for a checked Vegas program.

The carrier is the reachable information-state strategy space of the
syntax-horizon FOSG derived from the checked action-graph machine. A future
syntax-oriented strategy type for client generation should be introduced only
as a presentation proved equivalent to this IR carrier, not as an independent
semantics. -/
abbrev LegalProgramBehavioralStrategyPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) : Type :=
  (FOSGBridge.toFiniteGraphMachineFOSG g hctx).ReachableLegalBehavioralStrategy who

/-- IR-based legal PMF behavioral profile for a checked Vegas program. -/
structure LegalProgramBehavioralProfilePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) where
  profile : (FOSGBridge.toFiniteGraphMachineFOSG g hctx).ReachableLegalBehavioralProfile

/-- Sequential-game name for the same IR-based PMF behavioral profile. -/
abbrev SequentialBehavioralProfilePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) : Type :=
  LegalProgramBehavioralProfilePMF g hctx

/-- Outcome kernel for a machine-derived reachable sequential behavioral
profile. -/
noncomputable def sequentialOutcomeKernelPMF
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (β : SequentialBehavioralProfilePMF g hctx) :
    PMF (Outcome P) :=
  FOSGBridge.finiteGraphMachineFOSGReachableBehavioralOutcomeKernel
    g hctx LF β.profile

/-- Finite-game Kuhn theorem in the machine-derived sequential strategy space.

The witness is a reachable behavioral profile of the syntax-horizon
graph-machine-derived FOSG. The outcome distribution is already collapsed to
the native Vegas pure strategic kernel. -/
theorem sequential_mixedPure_realizedByBehavioralPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : SequentialBehavioralProfilePMF g hctx,
      sequentialOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toMachineStrategicKernelGame g hctx).outcomeKernel σ) := by
  classical
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  letI : Fintype (graphMachine g hctx).State :=
    graphMachine.instFintypeState g hctx LF
  letI : ∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who)) :=
    fun who => graphMachine.instFintypeOptionAction
      g hctx LF who
  obtain ⟨βF, hβF⟩ :=
    @FOSGBridge.toFiniteGraphMachineFOSG_vegasMixedPure_realizedByLegalBehavioral_mappedRunDist
      P inferInstance L g hctx inferInstance
      (fun who => LegalProgramPureStrategy.instFintype g LF who)
      (fun who =>
        graphMachine.instFintypeOptionAction
          g hctx LF who)
      (@Machine.BoundedRunPrefix.instFintype
        P (graphMachine g hctx) (syntaxSteps g.prog)
        (graphMachine.instFintypeEvent g hctx LF)
        (graphMachine.instFintypeState g hctx LF))
      (@Finite.of_fintype
        (FOSGBridge.toFiniteGraphMachineFOSG g hctx).History
        (finiteGraphMachineFOSG.instFintypeHistory g hctx LF))
      (Classical.decPred (FOSGBridge.toFiniteGraphMachineFOSG g hctx).terminal)
      μ
  refine ⟨⟨βF⟩, ?_⟩
  simpa [sequentialOutcomeKernelPMF,
    FOSGBridge.finiteGraphMachineFOSGReachableBehavioralOutcomeKernel]
    using hβF

/-- A syntax-recursive Vegas behavioral profile defined only on reachable
program observations.

This is the partial syntax strategy space: unlike
`SyntaxLegalProgramBehavioralProfilePMF`,
it does not assign behavior to syntactically well-typed views that cannot occur
as player observations in the sequential execution. -/
structure ReachableProgramBehavioralProfilePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) where
  profile :
    (FOSGBridge.toObservedFOSG g hctx).ReachableLegalBehavioralProfile

/-- Outcome kernel for a reachable Vegas behavioral profile. -/
noncomputable def reachableProgramOutcomeKernelPMF
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (β : ReachableProgramBehavioralProfilePMF g hctx) : PMF (Outcome P) :=
  (FOSGBridge.toObservedFOSGKernelGame g hctx LF).outcomeKernel β.profile

/-- Finite-game Kuhn theorem in the reachable Vegas strategy space. -/
theorem reachableProgram_mixedPure_realizedByBehavioralPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : ReachableProgramBehavioralProfilePMF g hctx,
      reachableProgramOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toMachineStrategicKernelGame g hctx).outcomeKernel σ) := by
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  obtain ⟨βF, hβF⟩ :=
    FOSGBridge.toObservedFOSG_mixedPure_realizedByBehavioral_outcomeKernel
      g hctx LF μ
  exact ⟨⟨βF⟩, hβF⟩

end Vegas
