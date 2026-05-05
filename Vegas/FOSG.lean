import Vegas.Protocol.Checked
import Vegas.Protocol.Strategic
import Vegas.Protocol.StrategicCompatibility

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

The cursor-world FOSG is still exposed as `toObservedFOSG`. It is not a
semantic owner; it is a syntax-facing projection layer related back to the
machine-derived semantics.
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

/-- Pure FOSG strategy induced by a Vegas legal pure strategy on the
syntax-horizon graph-machine FOSG. -/
noncomputable def toFiniteFOSGPureStrategyCandidate
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : FeasibleProgramPureStrategy g who) :
    GameTheory.FOSG.PureStrategy (toFiniteFOSG g hctx) who :=
  GameTheory.FOSG.PureStrategy.ofLatestObservation
    (G := toFiniteFOSG g hctx)
    (i := who)
    (Observed.movePureStrategyAtCursorWorld
      g hctx who σ (CursorCheckedWorld.initial g hctx))
    (Observed.movePureStrategyAtProgramObservation? g hctx who σ)

@[simp] theorem toFiniteFOSGPureStrategyCandidate_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : FeasibleProgramPureStrategy g who) :
    toFiniteFOSGPureStrategyCandidate g hctx who σ
        ((GameTheory.FOSG.History.nil
          (toFiniteFOSG g hctx)).playerView who) =
      Observed.movePureStrategyAtCursorWorld
        g hctx who σ (CursorCheckedWorld.initial g hctx) := by
  simp [toFiniteFOSGPureStrategyCandidate]

theorem toFiniteFOSGPureStrategyCandidate_history
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : FeasibleProgramPureStrategy g who)
    (h : (toFiniteFOSG g hctx).History) :
    toFiniteFOSGPureStrategyCandidate g hctx who σ
        (h.playerView who) =
      Observed.movePureStrategyAtCursorWorld
        g hctx who σ
        (cursorWorldOfGraphConfiguration
          g hctx h.lastState.lastState) := by
  by_cases hnil : h.steps = []
  · have hh :
        h = GameTheory.FOSG.History.nil
          (toFiniteFOSG g hctx) := by
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
            (G := toFiniteFOSG g hctx) (i := who)
            (h.playerView who) =
          some (privateObsOfCursorWorld who
              (cursorWorldOfGraphConfiguration
                g hctx h.lastState.lastState),
            publicObsOfCursorWorld (hctx := hctx)
              (cursorWorldOfGraphConfiguration
                g hctx h.lastState.lastState)) := by
      simpa [toFiniteFOSG, finiteFOSG,
        boundedFOSG,
        graphMachine, graphSemantics] using
        (fosgView g hctx)
          |>.toBoundedFOSG_latestObservation?_history_of_ne_nil
            (syntaxSteps g.prog) who h hnil
    simp [toFiniteFOSGPureStrategyCandidate,
      GameTheory.FOSG.PureStrategy.ofLatestObservation, hlatest,
      Observed.movePureStrategyAtProgramObservation?_of_cursorWorld]

theorem toFiniteFOSGPureStrategyCandidate_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : FeasibleProgramPureStrategy g who)
    (h : (toFiniteFOSG g hctx).History) :
    toFiniteFOSGPureStrategyCandidate g hctx who σ
        (h.playerView who) ∈
      (toFiniteFOSG g hctx).availableMoves h who := by
  rw [toFiniteFOSGPureStrategyCandidate_history]
  by_cases hcut : syntaxSteps g.prog ≤ h.lastState.pref.events.length
  · have hterm :
        terminal (cursorWorldOfGraphConfiguration g hctx h.lastState.lastState).toWorld :=
      finiteFOSG_terminal_endpoint_of_cutoff
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
        active (cursorWorldOfGraphConfiguration g hctx h.lastState.lastState).toWorld = ∅ :=
      cursor_terminal_active_eq_empty hterm
    let G := toFiniteFOSG g hctx
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
            who ∈ active
              (cursorWorldOfGraphConfiguration g hctx h.lastState.lastState).toWorld := by
          have hpair :
              who ∈ active
                  (cursorWorldOfGraphConfiguration g hctx h.lastState.lastState).toWorld ∧
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
      finiteFOSG_availableMoves_eq_observedProgram_of_not_cutoff
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
noncomputable def toFiniteFOSGLegalPureStrategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : FeasibleProgramPureStrategy g who) :
    (toFiniteFOSG g hctx).LegalPureStrategy who :=
  ⟨toFiniteFOSGPureStrategyCandidate g hctx who σ,
    toFiniteFOSGPureStrategyCandidate_available g hctx who σ⟩

/-- Reachable-coordinate graph-machine-FOSG pure strategy induced by a Vegas
legal pure strategy. -/
noncomputable def toFiniteFOSGReachableLegalPureStrategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : FeasibleProgramPureStrategy g who) :
    (toFiniteFOSG g hctx).ReachableLegalPureStrategy who :=
  (toFiniteFOSGLegalPureStrategy g hctx who σ).restrictReachable

/-- Reachable-coordinate graph-machine-FOSG pure profile induced pointwise by
a Vegas legal pure profile. -/
noncomputable def toFiniteFOSGReachableLegalPureProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramPureProfile g) :
    (toFiniteFOSG g hctx).ReachableLegalPureProfile :=
  fun who =>
    toFiniteFOSGReachableLegalPureStrategy g hctx who (σ who)

theorem toFiniteFOSG_pure_actionLaw_bind_checkedTransition_eq_checkedProfileStepPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who))]
    (σ : FeasibleProgramPureProfile g)
    (h : (toFiniteFOSG g hctx).History)
    (hterm : ¬ (toFiniteFOSG g hctx).terminal h.lastState) :
    ((toFiniteFOSG g hctx).legalActionLaw
        ((toFiniteFOSG g hctx).legalPureToBehavioral
          (toFiniteFOSGReachableLegalPureProfile
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
          ((toFiniteFOSG g hctx).transition
            h.lastState action)) =
      Observed.checkedProfileStepPMF g hctx
        (FeasibleProgramPureProfile.toBehavioralPMF σ)
        (CheckedWorld.ofCursorChecked (hctx := hctx)
          (cursorWorldOfGraphConfiguration
            g hctx h.lastState.lastState)) := by
  classical
  let G := toFiniteFOSG g hctx
  let β : G.LegalBehavioralProfile :=
    G.legalPureToBehavioral
      (toFiniteFOSGReachableLegalPureProfile g hctx σ).extend
  have hnotCut :
      ¬ syntaxSteps g.prog ≤ h.lastState.pref.events.length := by
    intro hcut
    exact hterm (Or.inr hcut)
  have hcursor :
      ¬ terminal (cursorWorldOfGraphConfiguration g hctx h.lastState.lastState).toWorld :=
    finiteFOSG_cursor_nonterminal_of_not_terminal
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
        active (cursorWorldOfGraphConfiguration g hctx h.lastState.lastState).toWorld = ∅ := by
      have hview :
          (fosgView g hctx).active
              h.lastState.pref = ∅ := by
        have hbounded :
            (if syntaxSteps g.prog ≤ h.lastState.pref.events.length then ∅
             else (fosgView g hctx).active
                h.lastState.pref) = ∅ := by
          simpa [G, toFiniteFOSG,
            finiteFOSG,
            boundedFOSG,
            Machine.FOSGView.boundedActive] using hactive
        rwa [if_neg hnotCut] at hbounded
      simpa [fosgView_active_eq_cursor_active_of_not_terminal
        g hctx h.lastState.pref hnotGraph,
        Machine.BoundedRunPrefix.lastState] using hview
    let noop : G.LegalAction h.lastState :=
      ⟨GameTheory.FOSG.noopAction
          (graphMachine g hctx).Action,
        G.legal_noopAction_of_active_empty_of_not_terminal hactive hterm⟩
    have htrans :=
      boundedFOSG_transition_map_checkedWorld_eq_checkedTransition
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
                  ((fosgView g hctx)
                    |>.boundedEventOfLegalJointAction
                      (syntaxSteps g.prog) h.lastState noop)),
              CursorProgramJointActionLegal.toAction
                (cursorProgramJointActionLegal_of_graphMachine_available
                  g hctx hcursor
                  ((fosgView g hctx)
                    |>.boundedEventOfLegalJointAction_available
                      (syntaxSteps g.prog) h.lastState noop))⟩ := by
            simpa [G, toFiniteFOSG,
              finiteFOSG] using htrans
      _ =
          Observed.checkedProfileStepPMF g hctx
            (FeasibleProgramPureProfile.toBehavioralPMF σ)
            (CheckedWorld.ofCursorChecked (hctx := hctx)
              (cursorWorldOfGraphConfiguration
                g hctx h.lastState.lastState)) := by
            apply Observed.checkedTransition_eq_checkedProfileStepPMF_of_active_empty
            simpa [active, CheckedWorld.ofCursorChecked,
              active] using hactiveCursor
  · have hne : (G.active h.lastState).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hactive
    rcases hne with ⟨who, hmem⟩
    have hmemCursor :
        who ∈ (observedProgramFOSG g hctx).active
          (cursorWorldOfGraphConfiguration g hctx h.lastState.lastState) := by
      have hmemRaw :
          who ∈
            (if syntaxSteps g.prog ≤ h.lastState.pref.events.length then ∅
             else (fosgView g hctx).active
                h.lastState.pref) := by
        simpa [G, toFiniteFOSG,
          finiteFOSG,
          boundedFOSG,
          Machine.FOSGView.boundedActive]
          using hmem
      rw [if_neg hnotCut] at hmemRaw
      have hmem' :
          who ∈ active
            (cursorWorldOfGraphConfiguration g hctx
              h.lastState.pref.lastState).toWorld := by
        simpa [fosgView_active_eq_cursor_active_of_not_terminal
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
        (fosgView g hctx).boundedEventOfLegalJointAction
          (syntaxSteps g.prog) h.lastState action
      let selectedAction :=
        graphMachineJointAction g hctx selectedEvent
      have hselectedAvailable :
          (graphMachine g hctx).EventAvailable
            h.lastState.lastState selectedEvent := by
        simpa [selectedEvent] using
          ((fosgView g hctx)
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
            (boundedFOSG
              g hctx (syntaxSteps g.prog)).active h.lastState := by
        simpa [G, toFiniteFOSG,
          finiteFOSG] using hmem
      have hselectedWho : selectedAction who = action.1 who := by
        simpa [selectedAction, selectedEvent] using
          graphMachineJointAction_selected_eq_of_active
            g hctx (syntaxSteps g.prog) action hmemBounded
      have htrans :=
        boundedFOSG_transition_map_checkedWorld_eq_checkedTransition
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
              simpa [G, toFiniteFOSG,
                finiteFOSG,
                selectedEvent, selectedAction] using htrans
        _ =
            Observed.checkedCommitContinuation
              g hctx env suffix wctx fresh viewScoped normalized legal
              (action.1 who) := by
              rw [checkedTransition_congr_checkedWorld
                (hw := hchecked)
                (a := ProgramJointAction.toAction selectedAction)
                (ha₂ := by
                  simpa [CheckedJointActionLegal, active, terminal,
                    availableActions, CheckedWorld.toWorld] using haRaw)]
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
            (FeasibleProgramPureProfile.toBehavioralPMF σ)
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
                    (((toFiniteFOSGReachableLegalPureProfile
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
                    ((toFiniteFOSGReachableLegalPureStrategy
                        g hctx who (σ who)).1
                      (G.reachableInfoStateOfHistory who h)) =
                  PMF.pure
                    (Observed.movePureStrategyAtCursorWorld
                      g hctx who (σ who)
                      (cursorWorldOfGraphConfiguration
                        g hctx h.lastState.lastState))
              change
                PMF.pure
                    ((toFiniteFOSGLegalPureStrategy
                        g hctx who (σ who)).1.restrictReachable
                      (G.reachableInfoStateOfHistory who h)) =
                  PMF.pure
                    (Observed.movePureStrategyAtCursorWorld
                      g hctx who (σ who)
                      (cursorWorldOfGraphConfiguration
                        g hctx h.lastState.lastState))
              change
                PMF.pure
                    (toFiniteFOSGPureStrategyCandidate
                      g hctx who (σ who)
                      ((G.reachableInfoStateOfHistory who h).1)) =
                  PMF.pure
                    (Observed.movePureStrategyAtCursorWorld
                      g hctx who (σ who)
                      (cursorWorldOfGraphConfiguration
                        g hctx h.lastState.lastState))
              simp only [GameTheory.FOSG.reachableInfoStateOfHistory_val]
              rw [toFiniteFOSGPureStrategyCandidate_history]
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
              g hctx (FeasibleProgramPureProfile.toBehavioralPMF σ)
              who
              (cursorWorldOfGraphConfiguration
                g hctx h.lastState.lastState)]
            rw [hchecked]
            exact
              Observed.moveAtProgramCursorPMF_bind_commitContinuation_eq_checkedProfileStepPMF
                g hctx (FeasibleProgramPureProfile.toBehavioralPMF σ)
                env suffix wctx fresh viewScoped normalized legal

/-- History-indexed continuation value for the finite graph-machine FOSG under
a Vegas pure profile. -/
noncomputable def finiteFOSGPureOutcomeValuePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who))]
    (σ : FeasibleProgramPureProfile g) :
    GameTheory.FOSG.History.OutcomeValue
      (G := toFiniteFOSG g hctx)
      ((toFiniteFOSG g hctx).legalPureToBehavioral
        (toFiniteFOSGReachableLegalPureProfile
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
      (FeasibleProgramPureProfile.toBehavioralPMF σ)
      (cursorWorldOfGraphConfiguration
        g hctx h.lastState.lastState)
  terminal_of_rank_zero := by
    intro h hrank
    have hinv :=
      finiteFOSG_history_remainingSyntaxSteps
        g hctx h
    have hcut : Vegas.syntaxSteps g.prog ≤ h.lastState.pref.events.length := by
      have hsteps : Vegas.syntaxSteps g.prog ≤ h.steps.length := by
        rw [hrank] at hinv
        omega
      have hlen :=
        (fosgView g hctx)
          |>.toBoundedFOSG_history_events_length (syntaxSteps g.prog) h
      have hlen' :
          h.lastState.pref.events.length = h.steps.length := by
        simpa [GameTheory.FOSG.History.lastState,
          finiteFOSG,
          boundedFOSG] using hlen
      rw [← hlen'] at hsteps
      exact hsteps
    exact Or.inr hcut
  terminal_value := by
    intro h hterm
    have hterm' :
        (finiteFOSG g hctx).terminal
          h.lastState := by
      simpa [toFiniteFOSG] using hterm
    have hcursor :=
      finiteFOSG_cursor_terminal_of_terminal
        g hctx h hterm'
    exact Observed.cursorVegasOutcomeKernelPMF_terminal
      (hctx := hctx) (FeasibleProgramPureProfile.toBehavioralPMF σ)
      (cursorWorldOfGraphConfiguration
        g hctx h.lastState.lastState) hcursor
  step_value := by
    intro h hterm
    let G := toFiniteFOSG g hctx
    let β : G.LegalBehavioralProfile :=
      G.legalPureToBehavioral
        (toFiniteFOSGReachableLegalPureProfile g hctx σ).extend
    have hcheckedStep :=
      toFiniteFOSG_pure_actionLaw_bind_checkedTransition_eq_checkedProfileStepPMF
        g hctx σ h hterm
    calc
      (G.legalActionLaw β h hterm).bind
          (fun action =>
            (G.transition h.lastState action).bind
              (fun dst =>
                Observed.cursorVegasOutcomeKernelPMF
                  (FeasibleProgramPureProfile.toBehavioralPMF σ)
                  (cursorWorldOfGraphConfiguration
                    g hctx
                    (h.extendByOutcome action dst).lastState.lastState))) =
        (G.legalActionLaw β h hterm).bind
          (fun action =>
            (G.transition h.lastState action).bind
              (fun dst =>
                Observed.cursorVegasOutcomeKernelPMF
                  (FeasibleProgramPureProfile.toBehavioralPMF σ)
                  (cursorWorldOfGraphConfiguration
                    g hctx dst.lastState))) := by
            congr
            funext action
            refine Math.ProbabilityMassFunction.bind_congr_on_support
              (G.transition h.lastState action)
              (fun dst =>
                Observed.cursorVegasOutcomeKernelPMF
                  (FeasibleProgramPureProfile.toBehavioralPMF σ)
                  (cursorWorldOfGraphConfiguration
                    g hctx
                    (h.extendByOutcome action dst).lastState.lastState))
              (fun dst =>
                Observed.cursorVegasOutcomeKernelPMF
                  (FeasibleProgramPureProfile.toBehavioralPMF σ)
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
              (FeasibleProgramPureProfile.toBehavioralPMF σ)) := by
            rw [PMF.bind_bind]
            congr
            funext action
            simp [PMF.map, PMF.bind_bind, Function.comp_def]
      _ =
        (Observed.checkedProfileStepPMF g hctx
          (FeasibleProgramPureProfile.toBehavioralPMF σ)
          (CheckedWorld.ofCursorChecked (hctx := hctx)
            (cursorWorldOfGraphConfiguration
              g hctx h.lastState.lastState))).bind
          (Observed.checkedVegasOutcomeKernelPMF
            (hctx := hctx)
            (FeasibleProgramPureProfile.toBehavioralPMF σ)) := by
            rw [hcheckedStep]
      _ =
        Observed.checkedVegasOutcomeKernelPMF
          (hctx := hctx)
          (FeasibleProgramPureProfile.toBehavioralPMF σ)
          (CheckedWorld.ofCursorChecked (hctx := hctx)
            (cursorWorldOfGraphConfiguration
              g hctx h.lastState.lastState)) := by
            exact Observed.checkedProfileStepPMF_bind_checkedVegasOutcomeKernelPMF
              g hctx (FeasibleProgramPureProfile.toBehavioralPMF σ)
              (CheckedWorld.ofCursorChecked (hctx := hctx)
                (cursorWorldOfGraphConfiguration
                  g hctx h.lastState.lastState))
      _ =
        Observed.cursorVegasOutcomeKernelPMF
          (FeasibleProgramPureProfile.toBehavioralPMF σ)
          (cursorWorldOfGraphConfiguration
            g hctx h.lastState.lastState) := rfl
  step_rank := by
    intro h hterm action dst hsupp
    have hterm' :
        ¬ (finiteFOSG g hctx).terminal
          h.lastState := by
      simpa [toFiniteFOSG] using hterm
    have hcursor :=
      finiteFOSG_cursor_nonterminal_of_not_terminal
        g hctx h hterm'
    have hsupp' :
        (boundedFOSG g hctx
            (syntaxSteps g.prog)).transition h.lastState action dst ≠ 0 := by
      simpa [toFiniteFOSG, finiteFOSG]
        using hsupp
    have hlast :
        (h.extendByOutcome action dst).lastState = dst := by
      rw [GameTheory.FOSG.History.extendByOutcome_of_support
        (h := h) (a := action) (dst := dst) hsupp]
      simp
    have hremaining :=
      boundedFOSG_transition_support_remainingSyntaxSteps
        (dst := dst) g hctx (syntaxSteps g.prog) h.lastState
        action hsupp' hcursor
    simpa [hlast] using hremaining

/-- Pure Vegas strategies have the same outcome distribution through the
finite graph-machine-derived FOSG as through the native strategic kernel game. -/
theorem toFiniteFOSG_vegasPure_runDist_eq_pureKernelGameAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who))]
    [Fintype
      ((graphMachine g hctx).BoundedRunPrefix
        (syntaxSteps g.prog))]
    [DecidablePred (toFiniteFOSG g hctx).terminal]
    (σ : FeasibleProgramPureProfile g) :
    PMF.map (fosgHistoryOutcome g hctx (syntaxSteps g.prog))
        ((toFiniteFOSG g hctx).runDist
          (syntaxSteps g.prog)
          ((toFiniteFOSG g hctx).legalPureToBehavioral
            (toFiniteFOSGReachableLegalPureProfile
              g hctx σ).extend)) =
      (pureKernelGameAt g hctx).outcomeKernel σ := by
  classical
  let R := finiteFOSGPureOutcomeValuePMF g hctx σ
  have hclosure :=
    R.map_observe_runDist_eq_value
      (syntaxSteps g.prog)
      (by
        change syntaxSteps g.prog ≤ syntaxSteps g.prog
        exact Nat.le_refl _)
  have hvalue :
      Observed.cursorVegasOutcomeKernelPMF
          (FeasibleProgramPureProfile.toBehavioralPMF σ)
          (CursorCheckedWorld.initial g hctx) =
        (pmfBehavioralKernelGame g).outcomeKernel
          (FeasibleProgramPureProfile.toBehavioralPMF σ) := by
    exact
      (GraphEventLaw.pmfBehavioralEventLaw_outcomeKernel_eq_cursorVegasOutcomeKernelPMF
        (g := g) (hctx := hctx)
        (σ := FeasibleProgramPureProfile.toBehavioralPMF σ)).symm.trans
        (GraphEventLaw.pmfBehavioralEventLaw_outcomeKernel_eq_pmfBehavioralKernelGame
          (g := g) (FeasibleProgramPureProfile.toBehavioralPMF σ) hctx)
  have hmachine :
      PMF.map (fosgHistoryOutcome g hctx (syntaxSteps g.prog))
          ((toFiniteFOSG g hctx).runDist
            (syntaxSteps g.prog)
            ((toFiniteFOSG g hctx).legalPureToBehavioral
              (toFiniteFOSGReachableLegalPureProfile
                g hctx σ).extend)) =
        Observed.cursorVegasOutcomeKernelPMF
          (FeasibleProgramPureProfile.toBehavioralPMF σ)
          (CursorCheckedWorld.initial g hctx) := by
    simpa [fosgHistoryOutcome, graphMachine,
      graphSemantics, graphMachine_init,
      cursorWorldOfGraphConfiguration_initial, R,
      finiteFOSGPureOutcomeValuePMF] using hclosure
  rw [hmachine, hvalue]
  rw [pmfBehavioralKernelGame_outcomeKernel_eq_pureKernelGame_toBehavioralPMF]
  exact (pureKernelGameAt_outcomeKernel_eq_pureKernelGame
    g hctx σ).symm

/-- Legacy spelling of the pure finite graph-machine FOSG bridge, stated
against `pureKernelGame`. New code should use
`toFiniteFOSG_vegasPure_runDist_eq_pureKernelGameAt`. -/
theorem toFiniteFOSG_vegasPure_runDist_eq_pureKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who))]
    [Fintype
      ((graphMachine g hctx).BoundedRunPrefix
        (syntaxSteps g.prog))]
    [DecidablePred (toFiniteFOSG g hctx).terminal]
    (σ : FeasibleProgramPureProfile g) :
    PMF.map (fosgHistoryOutcome g hctx (syntaxSteps g.prog))
        ((toFiniteFOSG g hctx).runDist
          (syntaxSteps g.prog)
          ((toFiniteFOSG g hctx).legalPureToBehavioral
            (toFiniteFOSGReachableLegalPureProfile
              g hctx σ).extend)) =
      (pureKernelGame g).outcomeKernel σ := by
  rw [toFiniteFOSG_vegasPure_runDist_eq_pureKernelGameAt]
  exact pureKernelGameAt_outcomeKernel_eq_pureKernelGame
    g hctx σ

/-- Product mixed profile over finite graph-machine-FOSG reachable pure
strategies induced by a product mixed profile over Vegas legal pure strategies. -/
noncomputable def toFiniteFOSGReachableMixedPureProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (μ : ∀ who, PMF (FeasibleProgramPureStrategy g who)) :
    GameTheory.FOSG.Kuhn.ReachableMixedProfile
      (G := toFiniteFOSG g hctx) :=
  fun who =>
    PMF.map (toFiniteFOSGReachableLegalPureStrategy g hctx who)
      (μ who)

theorem toFiniteFOSGReachableMixedPureProfile_joint
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who, Fintype (FeasibleProgramPureStrategy g who)]
    [∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who))]
    [Fintype (toFiniteFOSG g hctx).History]
    (μ : ∀ who, PMF (FeasibleProgramPureStrategy g who)) :
    GameTheory.FOSG.Kuhn.reachableMixedProfileJoint
        (G := toFiniteFOSG g hctx)
        (toFiniteFOSGReachableMixedPureProfile g hctx μ) =
      PMF.map (toFiniteFOSGReachableLegalPureProfile g hctx)
        (Math.PMFProduct.pmfPi μ) := by
  classical
  change Math.PMFProduct.pmfPi
      (fun who =>
        PMF.map (toFiniteFOSGReachableLegalPureStrategy g hctx who)
          (μ who)) =
    PMF.map
      (fun σ => fun who =>
        toFiniteFOSGReachableLegalPureStrategy g hctx who (σ who))
      (Math.PMFProduct.pmfPi μ)
  exact (Math.PMFProduct.pmfPi_push_coordwise μ
    (fun who => toFiniteFOSGReachableLegalPureStrategy g hctx who)).symm

/-- Product-mixed Vegas-pure specialization of the graph-machine finite-FOSG
Kuhn theorem. -/
theorem toFiniteFOSG_vegasMixedPure_realizedByLegalBehavioral_mappedRunDist
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who, Fintype (FeasibleProgramPureStrategy g who)]
    [∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who))]
    [Fintype
      ((graphMachine g hctx).BoundedRunPrefix
        (syntaxSteps g.prog))]
    [Finite (toFiniteFOSG g hctx).History]
    [DecidablePred (toFiniteFOSG g hctx).terminal]
    (μ : ∀ who, PMF (FeasibleProgramPureStrategy g who)) :
    ∃ β : (toFiniteFOSG g hctx).ReachableLegalBehavioralProfile,
      PMF.map (fosgHistoryOutcome g hctx (syntaxSteps g.prog))
          ((toFiniteFOSG g hctx).runDist
            (syntaxSteps g.prog) β.extend) =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (pureKernelGameAt g hctx).outcomeKernel σ) := by
  letI : Fintype (toFiniteFOSG g hctx).History :=
    Fintype.ofFinite _
  obtain ⟨β, hβ⟩ :=
    toFiniteFOSG_reachableMixedPure_realizedByLegalBehavioral_mappedRunDist
      g hctx (toFiniteFOSGReachableMixedPureProfile g hctx μ)
  refine ⟨β, ?_⟩
  rw [toFiniteFOSGReachableMixedPureProfile_joint] at hβ
  rw [PMF.bind_map] at hβ
  rw [hβ]
  apply congrArg
  funext σ
  exact toFiniteFOSG_vegasPure_runDist_eq_pureKernelGameAt
    g hctx σ



open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- IR-based legal PMF behavioral strategy for a checked Vegas program.

The carrier is the reachable information-state strategy space of the
syntax-horizon FOSG derived from the checked action-graph machine. A future
syntax-oriented strategy type for client generation should be introduced only
as a presentation proved equivalent to this IR carrier, not as an independent
semantics. -/
abbrev SequentialBehavioralStrategyPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) : Type :=
  (toFiniteFOSG g hctx).ReachableLegalBehavioralStrategy who

/-- IR-based PMF behavioral profile for a checked Vegas program: a
reachable feasible (guard-respecting) behavioral profile of the
finite graph-machine-derived FOSG. -/
structure SequentialBehavioralProfilePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) where
  profile : (toFiniteFOSG g hctx).ReachableLegalBehavioralProfile

/-- Outcome kernel for a machine-derived reachable sequential behavioral
profile. -/
noncomputable def sequentialOutcomeKernelPMF
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (β : SequentialBehavioralProfilePMF g hctx) :
    PMF (Outcome P) :=
  finiteFOSGReachableBehavioralOutcomeKernel
    g hctx LF β.profile

/-- Finite-game Kuhn theorem in the machine-derived sequential strategy space.

The witness is a reachable behavioral profile of the syntax-horizon
graph-machine-derived FOSG. The outcome distribution is already collapsed to
the native Vegas pure strategic kernel. -/
theorem sequential_mixedPure_realizedByBehavioralPMF_finite
    [Fintype P] (g : WFProgram P L)
    (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (FeasibleProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (FeasibleProgramPureStrategy g who) :=
      fun who => FeasibleProgramPureStrategy.instFintype g LF who
    ∃ β : SequentialBehavioralProfilePMF g hctx,
      sequentialOutcomeKernelPMF g hctx LF β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (pureKernelGameAt g hctx).outcomeKernel σ) := by
  classical
  letI : ∀ who, Fintype (FeasibleProgramPureStrategy g who) :=
    fun who => FeasibleProgramPureStrategy.instFintype g LF who
  letI : Fintype (graphMachine g hctx).State :=
    graphMachine.instFintypeState g hctx LF
  letI : ∀ who : P,
      Fintype (Option ((graphMachine g hctx).Action who)) :=
    fun who => graphMachine.instFintypeOptionAction
      g hctx LF who
  obtain ⟨βF, hβF⟩ :=
    @toFiniteFOSG_vegasMixedPure_realizedByLegalBehavioral_mappedRunDist
      P inferInstance L g hctx inferInstance
      (fun who => FeasibleProgramPureStrategy.instFintype g LF who)
      (fun who =>
        graphMachine.instFintypeOptionAction
          g hctx LF who)
      (@Machine.BoundedRunPrefix.instFintype
        P (graphMachine g hctx) (syntaxSteps g.prog)
        (graphMachine.instFintypeEvent g hctx LF)
        (graphMachine.instFintypeState g hctx LF))
      (@Finite.of_fintype
        (toFiniteFOSG g hctx).History
        (finiteFOSG.instFintypeHistory g hctx LF))
      (Classical.decPred (toFiniteFOSG g hctx).terminal)
      μ
  refine ⟨⟨βF⟩, ?_⟩
  simpa [sequentialOutcomeKernelPMF,
    finiteFOSGReachableBehavioralOutcomeKernel]
    using hβF

end Vegas
