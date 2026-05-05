import Vegas.Protocol.Trace
import Vegas.Protocol.Checked
import Vegas.Syntax.Cursor.Kernel
import Vegas.Syntax.Strategy.Conversions

/-!
# Strategic profiles as graph-machine event laws

This module adapts the syntax-facing Vegas strategy profiles to the canonical
checked graph machine's `Machine.EventLaw` API. The adapters are intentionally
thin: player turns reuse the existing observed-program move kernels, while
administrative syntax heads schedule the graph machine's unit internal event.
-/

namespace Vegas

open GameTheory

namespace GraphEventLaw

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {g : WFProgram P L}

/-- Interpret an optional program move for one player as one primitive
graph-machine event. In commit branches below, `none` has zero support for the
active owner; at administrative heads, the law schedules `.internal ()`
directly. -/
def eventOfProgramMove
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    Option (ProgramAction g.prog who) → (graphMachine g hctx).Event
  | some action => .play who action
  | none => .internal ()

/-- PMF-valued syntax-recursive behavioral profiles induce a state-local event
law for the checked graph machine. -/
noncomputable def pmfBehavioralEventKernel
    (σ : FeasibleProgramBehavioralProfilePMF g)
    (hctx : WFCtx g.Γ) :
    (graphMachine g hctx).EventLaw := fun cfg =>
  let w := cursorWorldOfGraphConfiguration g hctx cfg
  match w.1.prog with
  | .commit _ who _ _ =>
      (moveAtCursorWorldPMF g hctx σ who w).map
        (eventOfProgramMove g hctx who)
  | _ =>
      PMF.pure (.internal ())

private theorem internal_event_available_of_active_empty
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {state : (graphMachine g hctx).State}
    (hgraph : ¬ state.isTerminal)
    (hactive :
      active (cursorWorldOfGraphConfiguration g hctx state).toWorld = ∅) :
    (graphMachine g hctx).EventAvailable state (.internal ()) := by
  change () ∈ graphAvailableInternal g hctx state
  exact ⟨hgraph, hactive⟩

private theorem graphStep_remainingSyntaxSteps
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {state next : (graphMachine g hctx).State}
    {event : (graphMachine g hctx).Event}
    (hcursor :
      ¬ terminal (cursorWorldOfGraphConfiguration g hctx state).toWorld)
    (havailable : (graphMachine g hctx).EventAvailable state event)
    (hsupp : (graphMachine g hctx).step event state next ≠ 0) :
    (cursorWorldOfGraphConfiguration g hctx next).remainingSyntaxSteps + 1 =
      (cursorWorldOfGraphConfiguration g hctx state).remainingSyntaxSteps :=
  graphMachine_step_support_remainingSyntaxSteps_of_event_available_of_cursor_nonterminal
    g hctx hcursor havailable hsupp

/-- Legal event law induced by a syntax-recursive PMF behavioral profile. -/
noncomputable def pmfBehavioralEventLaw
    (σ : FeasibleProgramBehavioralProfilePMF g)
    (hctx : WFCtx g.Γ) :
    (graphMachine g hctx).LegalEventLaw :=
  ⟨pmfBehavioralEventKernel σ hctx, by
    intro state hterminal event hmem
    have hgraph : ¬ state.isTerminal := by
      simpa [graphMachine_terminal] using hterminal
    let w := cursorWorldOfGraphConfiguration g hctx state
    cases hhead : w.1.prog with
    | ret payoffs =>
        have hevent : event = .internal () := by
          simpa [pmfBehavioralEventKernel, w, hhead] using hmem
        subst event
        exact internal_event_available_of_active_empty g hctx hgraph
          (by
            have hhead' : w.1.cursor.prog = .ret payoffs := by
              simpa [CursorWorldData.prog] using hhead
            simp [w, active, CursorCheckedWorld.toWorld,
              CursorWorldData.prog, hhead'])
    | letExpr x e k =>
        have hevent : event = .internal () := by
          simpa [pmfBehavioralEventKernel, w, hhead] using hmem
        subst event
        have hhead' : w.1.cursor.prog = .letExpr x e k := by
          simpa [CursorWorldData.prog] using hhead
        exact internal_event_available_of_active_empty g hctx hgraph
          (cursor_active_eq_empty_of_letExpr
            (by simpa [w, CursorWorldData.prog] using hhead'))
    | sample x D k =>
        have hevent : event = .internal () := by
          simpa [pmfBehavioralEventKernel, w, hhead] using hmem
        subst event
        have hhead' : w.1.cursor.prog = .sample x D k := by
          simpa [CursorWorldData.prog] using hhead
        exact internal_event_available_of_active_empty g hctx hgraph
          (cursor_active_eq_empty_of_sample
            (by simpa [w, CursorWorldData.prog] using hhead'))
    | commit x who R k =>
        have hmap :
            ∃ move,
              move ∈
                (moveAtCursorWorldPMF g hctx σ who w).support ∧
              eventOfProgramMove g hctx who move = event := by
          simpa [pmfBehavioralEventKernel, w, hhead] using hmem
        rcases hmap with ⟨move, hmove, heq⟩
        rw [← heq]
        have havailableMove :=
          moveAtCursorWorldPMF_support_available
            g hctx σ who w hmove
        cases move with
        | none =>
            have hnotActive : who ∉ active w.toWorld := by
              simpa [cursorFOSG, GameTheory.FOSG.availableMovesAtState,
                GameTheory.FOSG.locallyLegalAtState,
                CursorCheckedWorld.availableProgramMovesAt,
                active, CursorCheckedWorld.toWorld]
                using havailableMove
            have hhead' : w.1.cursor.prog = .commit x who R k := by
              simpa [CursorWorldData.prog] using hhead
            have hactive : who ∈ active w.toWorld := by
              rw [cursor_active_eq_singleton_of_commit
                (by simpa [w, CursorWorldData.prog] using hhead')]
              simp
            exact False.elim (hnotActive hactive)
        | some action =>
            change action ∈ graphAvailable g hctx state who
            refine ⟨hgraph, ?_⟩
            have haction :
                action ∈ CursorCheckedWorld.availableProgramActions w who := by
              have hpair :
                  who ∈ active w.toWorld ∧
                    action ∈ CursorCheckedWorld.availableProgramActions w who := by
                simpa [cursorFOSG,
                  GameTheory.FOSG.availableMovesAtState,
                  GameTheory.FOSG.locallyLegalAtState,
                  CursorCheckedWorld.availableProgramMovesAt,
                  CursorCheckedWorld.availableProgramActions,
                  CursorCheckedWorld.availableProgramActionsAt,
                  availableActions,
                  active, CursorCheckedWorld.toWorld,
                  availableActions]
                  using havailableMove
              exact hpair.2
            simpa [w] using haction
    | reveal y who x hx k =>
        have hevent : event = .internal () := by
          simpa [pmfBehavioralEventKernel, w, hhead] using hmem
        subst event
        have hhead' : w.1.cursor.prog = .reveal y who x hx k := by
          simpa [CursorWorldData.prog] using hhead
        exact internal_event_available_of_active_empty g hctx hgraph
          (cursor_active_eq_empty_of_reveal
            (by simpa [w, CursorWorldData.prog] using hhead'))⟩

/-- One graph-machine step under the PMF behavioral event law projects to the
existing checked-world profile step. -/
theorem pmfBehavioralEventKernel_bind_step_map_checkedWorld_eq_checkedProfileStepPMF
    (σ : FeasibleProgramBehavioralProfilePMF g)
    (hctx : WFCtx g.Γ)
    (state : (graphMachine g hctx).State)
    (hterminal : ¬ (graphMachine g hctx).terminal state)
    (hcursor :
      ¬ terminal (cursorWorldOfGraphConfiguration g hctx state).toWorld) :
    (pmfBehavioralEventKernel σ hctx state).bind
        (fun event =>
          PMF.map
            (fun next : (graphMachine g hctx).State =>
              CheckedWorld.ofCursorChecked (hctx := hctx)
                (cursorWorldOfGraphConfiguration g hctx next))
            ((graphMachine g hctx).step event state)) =
      checkedProfileStepPMF g hctx σ
        (CheckedWorld.ofCursorChecked (hctx := hctx)
          (cursorWorldOfGraphConfiguration g hctx state)) := by
  classical
  have hgraph : ¬ state.isTerminal := by
    simpa [graphMachine_terminal] using hterminal
  let w := cursorWorldOfGraphConfiguration g hctx state
  cases hhead : w.1.prog with
  | ret payoffs =>
      have hterm : terminal w.toWorld := by
        change Vegas.terminal
          ({ Γ := w.1.cursor.Γ, prog := w.1.prog,
             env := w.1.env } : World P L)
        rw [hhead]
        simp
      exact False.elim (hcursor hterm)
  | letExpr x e k =>
      have hactive : active w.toWorld = ∅ :=
        cursor_active_eq_empty_of_letExpr
          (by simpa [w, CursorWorldData.prog] using hhead)
      have havailable :
          (graphMachine g hctx).EventAvailable state (.internal ()) :=
        internal_event_available_of_active_empty g hctx hgraph hactive
      calc
        (pmfBehavioralEventKernel σ hctx state).bind
            (fun event =>
              PMF.map
                (fun next : (graphMachine g hctx).State =>
                  CheckedWorld.ofCursorChecked (hctx := hctx)
                    (cursorWorldOfGraphConfiguration g hctx next))
                ((graphMachine g hctx).step event state))
            =
          PMF.map
            (fun next : (graphMachine g hctx).State =>
              CheckedWorld.ofCursorChecked (hctx := hctx)
                (cursorWorldOfGraphConfiguration g hctx next))
            ((graphMachine g hctx).step (.internal ()) state) := by
              simp [pmfBehavioralEventKernel, w, hhead]
        _ =
          checkedTransition
            (CheckedWorld.ofCursorChecked (hctx := hctx) w)
            ⟨ProgramJointAction.toAction
                (graphMachineJointAction g hctx (.internal ())),
              CursorProgramJointActionLegal.toAction
                (cursorProgramJointActionLegal_of_graphMachine_available
                  g hctx (by simpa [w] using hcursor) havailable)⟩ := by
              simpa [w] using
                graphMachine_step_map_checkedWorld_eq_checkedTransition_of_available
                  g hctx (state := state) (event := .internal ())
                  (by simpa [w] using hcursor) havailable
        _ =
          checkedProfileStepPMF g hctx σ
            (CheckedWorld.ofCursorChecked (hctx := hctx) w) := by
              apply checkedTransition_eq_checkedProfileStepPMF_of_active_empty
              simpa [active, CheckedWorld.ofCursorChecked,
                active] using hactive
  | sample x D k =>
      have hactive : active w.toWorld = ∅ :=
        cursor_active_eq_empty_of_sample
          (by simpa [w, CursorWorldData.prog] using hhead)
      have havailable :
          (graphMachine g hctx).EventAvailable state (.internal ()) :=
        internal_event_available_of_active_empty g hctx hgraph hactive
      calc
        (pmfBehavioralEventKernel σ hctx state).bind
            (fun event =>
              PMF.map
                (fun next : (graphMachine g hctx).State =>
                  CheckedWorld.ofCursorChecked (hctx := hctx)
                    (cursorWorldOfGraphConfiguration g hctx next))
                ((graphMachine g hctx).step event state))
            =
          PMF.map
            (fun next : (graphMachine g hctx).State =>
              CheckedWorld.ofCursorChecked (hctx := hctx)
                (cursorWorldOfGraphConfiguration g hctx next))
            ((graphMachine g hctx).step (.internal ()) state) := by
              simp [pmfBehavioralEventKernel, w, hhead]
        _ =
          checkedTransition
            (CheckedWorld.ofCursorChecked (hctx := hctx) w)
            ⟨ProgramJointAction.toAction
                (graphMachineJointAction g hctx (.internal ())),
              CursorProgramJointActionLegal.toAction
                (cursorProgramJointActionLegal_of_graphMachine_available
                  g hctx (by simpa [w] using hcursor) havailable)⟩ := by
              simpa [w] using
                graphMachine_step_map_checkedWorld_eq_checkedTransition_of_available
                  g hctx (state := state) (event := .internal ())
                  (by simpa [w] using hcursor) havailable
        _ =
          checkedProfileStepPMF g hctx σ
            (CheckedWorld.ofCursorChecked (hctx := hctx) w) := by
              apply checkedTransition_eq_checkedProfileStepPMF_of_active_empty
              simpa [active, CheckedWorld.ofCursorChecked,
                active] using hactive
  | commit x who R k =>
      have hactiveMem : who ∈ active w.toWorld := by
        rw [cursor_active_eq_singleton_of_commit
          (by simpa [w, CursorWorldData.prog] using hhead)]
        simp
      rcases cursorFOSG_active_mem_commitData
          g hctx w
          (by
            simpa [cursorFOSG, active, w]
              using hactiveMem) with
        ⟨Γ, x', b, R', k', env, suffix, wctx, fresh, viewScoped,
          normalized, legal, hchecked, hworld, _hobs⟩
      have hK :
          ∀ oi ∈ (moveAtCursorWorldPMF g hctx σ who w).support,
            PMF.map
              (fun next : (graphMachine g hctx).State =>
                CheckedWorld.ofCursorChecked (hctx := hctx)
                  (cursorWorldOfGraphConfiguration g hctx next))
              ((graphMachine g hctx).step
                (eventOfProgramMove g hctx who oi) state) =
            checkedCommitContinuation g hctx env suffix wctx
              fresh viewScoped normalized legal oi := by
        intro oi hoi
        have havailableMove :=
          moveAtCursorWorldPMF_support_available
            g hctx σ who w hoi
        cases oi with
        | none =>
            have hnotActive : who ∉ active w.toWorld := by
              simpa [cursorFOSG, GameTheory.FOSG.availableMovesAtState,
                GameTheory.FOSG.locallyLegalAtState,
                CursorCheckedWorld.availableProgramMovesAt,
                active, CursorCheckedWorld.toWorld]
                using havailableMove
            exact False.elim (hnotActive hactiveMem)
        | some action =>
            have haction :
                action ∈ CursorCheckedWorld.availableProgramActions w who := by
              have hpair :
                  who ∈ active w.toWorld ∧
                    action ∈ CursorCheckedWorld.availableProgramActions w who := by
                simpa [cursorFOSG,
                  GameTheory.FOSG.availableMovesAtState,
                  GameTheory.FOSG.locallyLegalAtState,
                  CursorCheckedWorld.availableProgramMovesAt,
                  CursorCheckedWorld.availableProgramActions,
                  CursorCheckedWorld.availableProgramActionsAt,
                  availableActions,
                  active, CursorCheckedWorld.toWorld,
                  availableActions]
                  using havailableMove
              exact hpair.2
            have havailable :
                (graphMachine g hctx).EventAvailable state
                  (.play who action) := by
              change action ∈ graphAvailable g hctx state who
              exact ⟨hgraph, by simpa [w] using haction⟩
            have hstep :=
              graphMachine_step_map_checkedWorld_eq_checkedTransition_of_available
                g hctx (state := state) (event := .play who action)
                (by simpa [w] using hcursor) havailable
            have haRaw : JointActionLegal
                ({ Γ := Γ, prog := VegasCore.commit x' who R' k',
                   env := env } : World P L)
                (ProgramJointAction.toAction
                  (graphMachineJointAction g hctx (.play who action))) := by
              have hto :=
                CursorProgramJointActionLegal.toAction
                  (cursorProgramJointActionLegal_of_graphMachine_available
                    g hctx (by simpa [w] using hcursor) havailable)
              simpa [w, hworld] using hto
            calc
              PMF.map
                  (fun next : (graphMachine g hctx).State =>
                    CheckedWorld.ofCursorChecked (hctx := hctx)
                      (cursorWorldOfGraphConfiguration g hctx next))
                  ((graphMachine g hctx).step
                    (eventOfProgramMove g hctx who (some action)) state)
                  =
                checkedTransition
                  (CheckedWorld.ofCursorChecked (hctx := hctx) w)
                  ⟨ProgramJointAction.toAction
                      (graphMachineJointAction g hctx (.play who action)),
                    CursorProgramJointActionLegal.toAction
                      (cursorProgramJointActionLegal_of_graphMachine_available
                        g hctx (by simpa [w] using hcursor) havailable)⟩ := by
                    simpa [eventOfProgramMove, w] using hstep
              _ =
                checkedCommitContinuation g hctx env suffix wctx
                  fresh viewScoped normalized legal (some action) := by
                    rw [checkedTransition_congr_checkedWorld
                      (hw := hchecked)
                      (a := ProgramJointAction.toAction
                        (graphMachineJointAction g hctx (.play who action)))
                      (ha₂ := by
                        simpa [CheckedJointActionLegal, active,
                          terminal, availableActions,
                          CheckedWorld.toWorld] using haRaw)]
                    simpa [checkedCommitContinuation,
                      graphMachineJointAction, singleProgramJointAction] using
                      checkedTransition_commit_eq_programActionContinuation
                        g hctx env suffix wctx fresh viewScoped
                        normalized legal
                        (graphMachineJointAction g hctx (.play who action))
                        haRaw
      calc
        (pmfBehavioralEventKernel σ hctx state).bind
            (fun event =>
              PMF.map
                (fun next : (graphMachine g hctx).State =>
                  CheckedWorld.ofCursorChecked (hctx := hctx)
                    (cursorWorldOfGraphConfiguration g hctx next))
                ((graphMachine g hctx).step event state))
            =
          (moveAtCursorWorldPMF g hctx σ who w).bind
            (fun oi =>
              PMF.map
                (fun next : (graphMachine g hctx).State =>
                  CheckedWorld.ofCursorChecked (hctx := hctx)
                    (cursorWorldOfGraphConfiguration g hctx next))
                ((graphMachine g hctx).step
                  (eventOfProgramMove g hctx who oi) state)) := by
              simp [pmfBehavioralEventKernel, w, hhead, PMF.bind_map,
                Function.comp_def]
        _ =
          (moveAtCursorWorldPMF g hctx σ who w).bind
            (checkedCommitContinuation g hctx env suffix wctx
              fresh viewScoped normalized legal) := by
              exact Math.ProbabilityMassFunction.bind_congr_on_support
                (moveAtCursorWorldPMF g hctx σ who w) _ _
                (by intro oi hoi; exact hK oi hoi)
        _ =
          checkedProfileStepPMF g hctx σ
            (CheckedWorld.ofCursorChecked (hctx := hctx) w) := by
              rw [← moveAtCheckedWorldPMF_ofCursorChecked
                g hctx σ who w]
              rw [hchecked]
              exact
                moveAtProgramCursorPMF_bind_commitContinuation_eq_checkedProfileStepPMF
                  g hctx σ env suffix wctx fresh viewScoped normalized legal
  | reveal y who x hx k =>
      have hactive : active w.toWorld = ∅ :=
        cursor_active_eq_empty_of_reveal
          (by simpa [w, CursorWorldData.prog] using hhead)
      have havailable :
          (graphMachine g hctx).EventAvailable state (.internal ()) :=
        internal_event_available_of_active_empty g hctx hgraph hactive
      calc
        (pmfBehavioralEventKernel σ hctx state).bind
            (fun event =>
              PMF.map
                (fun next : (graphMachine g hctx).State =>
                  CheckedWorld.ofCursorChecked (hctx := hctx)
                    (cursorWorldOfGraphConfiguration g hctx next))
                ((graphMachine g hctx).step event state))
            =
          PMF.map
            (fun next : (graphMachine g hctx).State =>
              CheckedWorld.ofCursorChecked (hctx := hctx)
                (cursorWorldOfGraphConfiguration g hctx next))
            ((graphMachine g hctx).step (.internal ()) state) := by
              simp [pmfBehavioralEventKernel, w, hhead]
        _ =
          checkedTransition
            (CheckedWorld.ofCursorChecked (hctx := hctx) w)
            ⟨ProgramJointAction.toAction
                (graphMachineJointAction g hctx (.internal ())),
              CursorProgramJointActionLegal.toAction
                (cursorProgramJointActionLegal_of_graphMachine_available
                  g hctx (by simpa [w] using hcursor) havailable)⟩ := by
              simpa [w] using
                graphMachine_step_map_checkedWorld_eq_checkedTransition_of_available
                  g hctx (state := state) (event := .internal ())
                  (by simpa [w] using hcursor) havailable
        _ =
          checkedProfileStepPMF g hctx σ
            (CheckedWorld.ofCursorChecked (hctx := hctx) w) := by
              apply checkedTransition_eq_checkedProfileStepPMF_of_active_empty
              simpa [active, CheckedWorld.ofCursorChecked,
                active] using hactive

/-- The legacy cursor outcome kernel is preserved by one graph-machine step
under the PMF behavioral event law. -/
theorem pmfBehavioralEventKernel_bind_step_cursorVegasOutcomeKernelPMF
    (σ : FeasibleProgramBehavioralProfilePMF g)
    (hctx : WFCtx g.Γ)
    (state : (graphMachine g hctx).State)
    (hterminal : ¬ (graphMachine g hctx).terminal state)
    (hcursor :
      ¬ terminal (cursorWorldOfGraphConfiguration g hctx state).toWorld) :
    (pmfBehavioralEventKernel σ hctx state).bind
        (fun event =>
          ((graphMachine g hctx).step event state).bind
            (fun next =>
              cursorVegasOutcomeKernelPMF σ
                (cursorWorldOfGraphConfiguration g hctx next))) =
      cursorVegasOutcomeKernelPMF σ
        (cursorWorldOfGraphConfiguration g hctx state) := by
  let w := cursorWorldOfGraphConfiguration g hctx state
  calc
    (pmfBehavioralEventKernel σ hctx state).bind
        (fun event =>
          ((graphMachine g hctx).step event state).bind
            (fun next =>
              cursorVegasOutcomeKernelPMF σ
                (cursorWorldOfGraphConfiguration g hctx next)))
        =
      ((pmfBehavioralEventKernel σ hctx state).bind
        (fun event =>
          PMF.map
            (fun next : (graphMachine g hctx).State =>
              CheckedWorld.ofCursorChecked (hctx := hctx)
                (cursorWorldOfGraphConfiguration g hctx next))
            ((graphMachine g hctx).step event state))).bind
        (checkedVegasOutcomeKernelPMF (hctx := hctx) σ) := by
          rw [PMF.bind_bind]
          congr 1
          funext event
          rw [PMF.bind_map]
          rfl
    _ =
      (checkedProfileStepPMF g hctx σ
        (CheckedWorld.ofCursorChecked (hctx := hctx)
          (cursorWorldOfGraphConfiguration g hctx state))).bind
        (checkedVegasOutcomeKernelPMF (hctx := hctx) σ) := by
          rw [pmfBehavioralEventKernel_bind_step_map_checkedWorld_eq_checkedProfileStepPMF
            (g := g) (σ := σ) hctx state hterminal hcursor]
    _ =
      checkedVegasOutcomeKernelPMF (hctx := hctx) σ
        (CheckedWorld.ofCursorChecked (hctx := hctx)
          (cursorWorldOfGraphConfiguration g hctx state)) := by
          exact checkedProfileStepPMF_bind_checkedVegasOutcomeKernelPMF
            g hctx σ
            (CheckedWorld.ofCursorChecked (hctx := hctx)
              (cursorWorldOfGraphConfiguration g hctx state))
    _ =
      cursorVegasOutcomeKernelPMF σ
        (cursorWorldOfGraphConfiguration g hctx state) := rfl

/-- From any graph state whose frontier is synchronized with the projected
cursor, running the graph-machine event law for exactly the remaining cursor
syntax budget gives the legacy cursor outcome kernel. -/
theorem pmfBehavioralEventKernel_outcomeKernelFrom_eq_cursorVegasOutcomeKernelPMF
    (σ : FeasibleProgramBehavioralProfilePMF g)
    (hctx : WFCtx g.Γ) :
    ∀ (fuel : Nat) (state : (graphMachine g hctx).State),
      (cursorWorldOfGraphConfiguration g hctx state).remainingSyntaxSteps =
        fuel →
      syntaxGraphDoneBeforeCursor g state.frontier.done
        (cursorWorldOfGraphConfiguration g hctx state).1.cursor →
      (graphMachine g hctx).outcomeKernelFrom
          (pmfBehavioralEventKernel σ hctx) fuel state =
        cursorVegasOutcomeKernelPMF σ
          (cursorWorldOfGraphConfiguration g hctx state)
  | 0, state, hfuel, _hinv => by
      have hcursor :
          terminal (cursorWorldOfGraphConfiguration g hctx state).toWorld :=
        (CursorCheckedWorld.terminal_iff_remainingSyntaxSteps_eq_zero
          (g := g)
          (w := cursorWorldOfGraphConfiguration g hctx state)).2 hfuel
      rw [Machine.outcomeKernelFrom_zero]
      rw [cursorVegasOutcomeKernelPMF_terminal
        (hctx := hctx) σ
        (cursorWorldOfGraphConfiguration g hctx state) hcursor]
      rfl
  | fuel + 1, state, hfuel, hinv => by
      classical
      let w := cursorWorldOfGraphConfiguration g hctx state
      have hpositive : 0 < w.remainingSyntaxSteps := by
        rw [hfuel]
        exact Nat.succ_pos fuel
      have hcursorPositive : 0 < syntaxSteps w.1.cursor.prog := by
        simpa [w, CursorCheckedWorld.remainingSyntaxSteps,
          CursorWorldData.prog] using hpositive
      have hcurrentMem : w.1.cursor ∈ syntaxGraphActions g := by
        letI : Fintype (ProgramCursor g.prog) :=
          ProgramCursor.instFintype g.prog
        simp [syntaxGraphActions, hcursorPositive]
      have hcursor :
          ¬ terminal w.toWorld := by
        intro hterm
        have hzero :
            w.remainingSyntaxSteps = 0 :=
          (CursorCheckedWorld.terminal_iff_remainingSyntaxSteps_eq_zero
            (g := g) (w := w)).1 hterm
        omega
      have hterminal :
          ¬ (graphMachine g hctx).terminal state := by
        intro hterm
        have hcomplete :
            (syntaxActionGraph g).CompleteAt state.frontier.done := by
          simpa [graphMachine_terminal, ActionGraph.Configuration.isTerminal,
            ActionGraph.FrontierMachine.isComplete] using hterm
        have hnotDone :
            w.1.cursor ∉ state.frontier.done :=
          syntaxGraphDoneBeforeCursor_current_not_done
            (g := g) (by simpa [w] using hinv)
        exact hnotDone (hcomplete hcurrentMem)
      rw [Machine.outcomeKernelFrom_succ]
      calc
        (pmfBehavioralEventKernel σ hctx state).bind
            (fun event =>
              ((graphMachine g hctx).step event state).bind
                (fun next =>
                  (graphMachine g hctx).outcomeKernelFrom
                    (pmfBehavioralEventKernel σ hctx) fuel next))
            =
          (pmfBehavioralEventKernel σ hctx state).bind
            (fun event =>
              ((graphMachine g hctx).step event state).bind
                (fun next =>
                  cursorVegasOutcomeKernelPMF σ
                    (cursorWorldOfGraphConfiguration g hctx next))) := by
              refine Math.ProbabilityMassFunction.bind_congr_on_support
                (pmfBehavioralEventKernel σ hctx state) _ _ ?_
              intro event hevent
              have havailable :
                  (graphMachine g hctx).EventAvailable state event :=
                (pmfBehavioralEventLaw σ hctx).2 state hterminal hevent
              refine Math.ProbabilityMassFunction.bind_congr_on_support
                ((graphMachine g hctx).step event state) _ _ ?_
              intro next hnext
              have hstep : (graphMachine g hctx).step event state next ≠ 0 :=
                (PMF.mem_support_iff _ _).1 hnext
              have hremaining :
                  (cursorWorldOfGraphConfiguration g hctx next
                    ).remainingSyntaxSteps + 1 =
                    (cursorWorldOfGraphConfiguration g hctx state
                    ).remainingSyntaxSteps :=
                graphStep_remainingSyntaxSteps
                  g hctx (by simpa [w] using hcursor) havailable hstep
              have hnextFuel :
                  (cursorWorldOfGraphConfiguration g hctx next
                    ).remainingSyntaxSteps = fuel := by
                rw [hfuel] at hremaining
                omega
              have hrankNext :
                  syntaxGraphRank g
                      (cursorWorldOfGraphConfiguration g hctx next).1.cursor =
                    syntaxGraphRank g
                        (cursorWorldOfGraphConfiguration g hctx state
                        ).1.cursor + 1 := by
                exact syntaxGraphRank_cursor_eq_succ_of_remainingSyntaxSteps
                  (g := g) hremaining
              have hdone :
                  next.frontier.done =
                    (syntaxActionGraph g).advance state.frontier.done :=
                graphMachine_step_support_done_eq_advance_of_event_available
                  g hctx havailable hstep
              have hnextInv :
                  syntaxGraphDoneBeforeCursor g next.frontier.done
                    (cursorWorldOfGraphConfiguration g hctx next).1.cursor := by
                rw [hdone]
                exact syntaxGraphDoneBeforeCursor_advance
                  (g := g) hcurrentMem (by simpa [w] using hinv)
                  (by simpa [w] using hrankNext)
              exact
                pmfBehavioralEventKernel_outcomeKernelFrom_eq_cursorVegasOutcomeKernelPMF
                  σ hctx fuel next hnextFuel hnextInv
        _ =
          cursorVegasOutcomeKernelPMF σ
            (cursorWorldOfGraphConfiguration g hctx state) := by
              exact
                pmfBehavioralEventKernel_bind_step_cursorVegasOutcomeKernelPMF
                  (g := g) (σ := σ) hctx state hterminal
                  (by simpa [w] using hcursor)

/-- Initial-state specialization of
`pmfBehavioralEventKernel_outcomeKernelFrom_eq_cursorVegasOutcomeKernelPMF`. -/
theorem pmfBehavioralEventLaw_outcomeKernel_eq_cursorVegasOutcomeKernelPMF
    (σ : FeasibleProgramBehavioralProfilePMF g)
    (hctx : WFCtx g.Γ) :
    (graphMachine g hctx).outcomeKernel
        (pmfBehavioralEventLaw σ hctx).val (syntaxSteps g.prog) =
      cursorVegasOutcomeKernelPMF σ
        (CursorCheckedWorld.initial g hctx) := by
  change
    (graphMachine g hctx).outcomeKernelFrom
        (pmfBehavioralEventKernel σ hctx) (syntaxSteps g.prog)
        (graphMachine g hctx).init =
      cursorVegasOutcomeKernelPMF σ
        (CursorCheckedWorld.initial g hctx)
  have hbridge :=
    pmfBehavioralEventKernel_outcomeKernelFrom_eq_cursorVegasOutcomeKernelPMF
      (g := g) σ hctx (syntaxSteps g.prog) (graphMachine g hctx).init
      (by
        change
          (cursorWorldOfGraphConfiguration g hctx
            (ActionGraph.Configuration.initial
              (syntaxActionGraph g))).remainingSyntaxSteps =
            syntaxSteps g.prog
        rw [cursorWorldOfGraphConfiguration_initial]
        rfl)
      (by
        change
          syntaxGraphDoneBeforeCursor g
            (ActionGraph.Configuration.initial
              (syntaxActionGraph g)).frontier.done
            (cursorWorldOfGraphConfiguration g hctx
              (ActionGraph.Configuration.initial
                (syntaxActionGraph g))).1.cursor
        simpa [ActionGraph.Configuration.initial,
          ActionGraph.FrontierMachine.initial,
          cursorWorldOfGraphConfiguration_initial] using
          syntaxGraphDoneBeforeCursor_initial g)
  simpa [graphMachine_init, cursorWorldOfGraphConfiguration_initial] using
    hbridge

/-- Legal event law induced by a legal FDist-valued behavioral profile. -/
noncomputable def behavioralEventLaw
    (σ : FeasibleProgramBehavioralProfile g)
    (hctx : WFCtx g.Γ) :
    (graphMachine g hctx).LegalEventLaw :=
  pmfBehavioralEventLaw (FeasibleProgramBehavioralProfile.toPMFProfile σ) hctx

/-- Legal event law induced by a legal pure profile. -/
noncomputable def pureEventLaw
    (σ : FeasibleProgramPureProfile g)
    (hctx : WFCtx g.Γ) :
    (graphMachine g hctx).LegalEventLaw :=
  pmfBehavioralEventLaw (FeasibleProgramPureProfile.toBehavioralPMF σ) hctx

@[simp] theorem lawValOfPure_apply
    (σ : FeasibleProgramPureProfile g)
    (hctx : WFCtx g.Γ)
    (cfg : (graphMachine g hctx).State) :
    (pureEventLaw σ hctx).val cfg =
      let w := cursorWorldOfGraphConfiguration g hctx cfg
      match w.1.prog with
      | .commit _ who _ _ =>
          PMF.pure
            (eventOfProgramMove g hctx who
              (movePureAtCursorWorld g hctx σ who w))
      | _ =>
          PMF.pure (.internal ()) := by
  change
    pmfBehavioralEventKernel (FeasibleProgramPureProfile.toBehavioralPMF σ) hctx cfg =
      (let w := cursorWorldOfGraphConfiguration g hctx cfg
       match w.1.prog with
       | .commit _ who _ _ =>
           PMF.pure
             (eventOfProgramMove g hctx who
               (movePureAtCursorWorld g hctx σ who w))
       | _ =>
           PMF.pure (.internal ()))
  unfold pmfBehavioralEventKernel
  let w := cursorWorldOfGraphConfiguration g hctx cfg
  cases hhead : w.1.prog with
  | ret payoffs =>
      simp [w, hhead]
  | letExpr x e k =>
      simp [w, hhead]
  | sample x D k =>
      simp [w, hhead]
  | commit x who R k =>
      simp [w, hhead, moveAtCursorWorldPMF_toBehavioralPMF_eq_pure,
        PMF.pure_map]
  | reveal y who x hx k =>
      simp [w, hhead]

/-- One graph-machine step under a pure profile's event law projects to the
checked-world profile step for the deterministic behavioral lift. -/
theorem pureEventLaw_bind_step_map_checkedWorld_eq_checkedProfileStepPMF
    (σ : FeasibleProgramPureProfile g)
    (hctx : WFCtx g.Γ)
    (state : (graphMachine g hctx).State)
    (hterminal : ¬ (graphMachine g hctx).terminal state)
    (hcursor :
      ¬ terminal (cursorWorldOfGraphConfiguration g hctx state).toWorld) :
    ((pureEventLaw σ hctx).val state).bind
        (fun event =>
          PMF.map
            (fun next : (graphMachine g hctx).State =>
              CheckedWorld.ofCursorChecked (hctx := hctx)
                (cursorWorldOfGraphConfiguration g hctx next))
            ((graphMachine g hctx).step event state)) =
      checkedProfileStepPMF g hctx
        (FeasibleProgramPureProfile.toBehavioralPMF σ)
        (CheckedWorld.ofCursorChecked (hctx := hctx)
          (cursorWorldOfGraphConfiguration g hctx state)) := by
  change
    (pmfBehavioralEventKernel (FeasibleProgramPureProfile.toBehavioralPMF σ)
        hctx state).bind
        (fun event =>
          PMF.map
            (fun next : (graphMachine g hctx).State =>
              CheckedWorld.ofCursorChecked (hctx := hctx)
                (cursorWorldOfGraphConfiguration g hctx next))
            ((graphMachine g hctx).step event state)) =
      checkedProfileStepPMF g hctx
        (FeasibleProgramPureProfile.toBehavioralPMF σ)
        (CheckedWorld.ofCursorChecked (hctx := hctx)
          (cursorWorldOfGraphConfiguration g hctx state))
  exact
    pmfBehavioralEventKernel_bind_step_map_checkedWorld_eq_checkedProfileStepPMF
      (g := g) (σ := FeasibleProgramPureProfile.toBehavioralPMF σ)
      hctx state hterminal hcursor

/-- The legacy cursor outcome kernel is preserved by one graph-machine step
under a pure profile's event law. -/
theorem pureEventLaw_bind_step_cursorVegasOutcomeKernelPMF
    (σ : FeasibleProgramPureProfile g)
    (hctx : WFCtx g.Γ)
    (state : (graphMachine g hctx).State)
    (hterminal : ¬ (graphMachine g hctx).terminal state)
    (hcursor :
      ¬ terminal (cursorWorldOfGraphConfiguration g hctx state).toWorld) :
    ((pureEventLaw σ hctx).val state).bind
        (fun event =>
          ((graphMachine g hctx).step event state).bind
            (fun next =>
              cursorVegasOutcomeKernelPMF
                (FeasibleProgramPureProfile.toBehavioralPMF σ)
                (cursorWorldOfGraphConfiguration g hctx next))) =
      cursorVegasOutcomeKernelPMF
        (FeasibleProgramPureProfile.toBehavioralPMF σ)
        (cursorWorldOfGraphConfiguration g hctx state) := by
  change
    (pmfBehavioralEventKernel (FeasibleProgramPureProfile.toBehavioralPMF σ)
        hctx state).bind
        (fun event =>
          ((graphMachine g hctx).step event state).bind
            (fun next =>
              cursorVegasOutcomeKernelPMF
                (FeasibleProgramPureProfile.toBehavioralPMF σ)
                (cursorWorldOfGraphConfiguration g hctx next))) =
      cursorVegasOutcomeKernelPMF
        (FeasibleProgramPureProfile.toBehavioralPMF σ)
        (cursorWorldOfGraphConfiguration g hctx state)
  exact
    pmfBehavioralEventKernel_bind_step_cursorVegasOutcomeKernelPMF
      (g := g) (σ := FeasibleProgramPureProfile.toBehavioralPMF σ)
      hctx state hterminal hcursor

end GraphEventLaw

export GraphEventLaw
  (pmfBehavioralEventKernel pmfBehavioralEventLaw behavioralEventLaw pureEventLaw)

end Vegas
