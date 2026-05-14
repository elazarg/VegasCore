import Vegas.EventGraph.Round
import Vegas.GameBridge.FOSG.Basic

/-!
# FOSG bridge for event graphs

This module exposes stable event-graph frontiers as bounded FOSG rounds and
connects those rounds back to primitive machine traces.
-/

namespace Vegas

namespace EventGraph

open GameTheory

variable {Player : Type} [DecidableEq Player] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- FOSG presentation of a protocol-graph machine by stable frontier rounds. -/
noncomputable def toFOSGView
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) :
    (G.toMachine iface).FOSGView where
  Act := PlayerRoundAction G
  active := roundActive G
  availableActions := roundAvailable G
  transition := fun cfg action => roundTransition G cfg action.1
  reward := fun _ _ dst who => iface.utility (iface.outcome dst) who
  terminal_active_eq_empty := by
    intro cfg hterminal
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro who hmem
    rcases (mem_roundActive_iff G cfg who).mp hmem with
      ⟨node, hfrontier, _hactor⟩
    exact (cfg.not_terminal_of_mem_frontier hfrontier) hterminal
  nonterminal_exists_legal := by
    intro cfg hterminal
    classical
    let mkSlice (who : Player) (node : G.Node) : G.WriteSlice :=
      if h : node ∈ cfg.frontier ∧ (G.sem node).actor = some who then
        Classical.choose (hsound.availablePlayerActions cfg h.1 h.2)
      else
        fun _ => none
    let joint : JointAction (PlayerRoundAction G) := fun who =>
      if who ∈ roundActive G cfg then
        some { slice := mkSlice who }
      else
        none
    refine ⟨joint, hterminal, ?_⟩
    intro who
    by_cases hactive : who ∈ roundActive G cfg
    · have hjoint : joint who = some { slice := mkSlice who } := by
        simp [joint, hactive]
      rw [hjoint]
      refine ⟨hactive, ?_⟩
      intro node hfrontier hactor
      have hnode : node ∈ cfg.frontier ∧ (G.sem node).actor = some who :=
        ⟨hfrontier, hactor⟩
      change
        G.sliceLegal node (mkSlice who node) ∧
          G.actionLegal cfg.result node (mkSlice who node)
      unfold mkSlice
      split
      · rename_i h
        exact Classical.choose_spec
          (hsound.availablePlayerActions cfg h.1 h.2)
      · rename_i h
        exact False.elim (h hnode)
    · have hjoint : joint who = none := by
        simp [joint, hactive]
      rw [hjoint]
      exact hactive

/-- The optional-move set of the FOSG induced by an event graph is the
graph-level `roundMenu`.  Bridges the strategic FOSG carrier (which pairs
each player's optional round move with a `none` for inactive rounds) and the
direct configuration-level menu. -/
@[simp] theorem toFOSGView_toFOSG_availableMovesAtState_eq_roundMenu
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds)
    (cfg : G.Configuration) (who : Player) :
    (G.toFOSGView iface hsound).toFOSG.availableMovesAtState cfg who =
      G.roundMenu cfg who := by
  ext move
  cases move <;> rfl

/-- The bounded-FOSG version: before the horizon cutoff, optional round moves
agree with the player-facing graph menu. -/
theorem toFOSGView_toBoundedFOSG_availableMovesAtState_eq_roundMenu
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat) (who : Player)
    (state : (G.toMachine iface).BoundedState horizon)
    (hcut : ¬ horizon ≤ state.depth) :
    ((G.toFOSGView iface hsound).toBoundedFOSG horizon).availableMovesAtState
        state who =
      G.roundMenu state.state who := by
  ext move
  rw [GameTheory.FOSG.mem_availableMovesAtState_iff]
  cases move with
  | none =>
      change ¬ who ∈ Machine.FOSGView.boundedActive _ horizon state ↔ _
      simp [Machine.FOSGView.boundedActive, hcut]
      rfl
  | some action =>
      change who ∈ Machine.FOSGView.boundedActive _ horizon state ∧
          action ∈ Machine.FOSGView.boundedAvailableActions _ horizon state who ↔ _
      simp [Machine.FOSGView.boundedActive,
        Machine.FOSGView.boundedAvailableActions, hcut]
      rfl

/-- One bounded graph-FOSG transition, projected back to graph configurations,
is the primitive machine run of the round's canonical frontier event list. -/
theorem toFOSGView_toBoundedFOSG_transition_map_state_eq_runEventsFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds)
    (horizon : Nat)
    (state : (G.toMachine iface).BoundedState horizon)
    (action :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).LegalAction
        state)) :
    PMF.map (fun bounded => bounded.state)
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          state action) =
      (G.toMachine iface).runEventsFrom
        (roundPrimitiveEvents G iface state.state action.1)
        state.state := by
  rw [Machine.FOSGView.toBoundedFOSG_transition_map_state]
  change
    roundTransition G state.state action.1 =
      (G.toMachine iface).runEventsFrom
        (roundPrimitiveEvents G iface state.state action.1)
        state.state
  exact roundTransition_eq_runEventsFrom_roundPrimitiveEvents
    G iface state.state action.1

/-- One bounded graph-FOSG transition, projected back to graph configurations,
is one blocked primitive machine run.  This is the one-step form used by
trace-level simulations: FOSG histories compose blocks; primitive machine
traces flatten them. -/
theorem toFOSGView_toBoundedFOSG_transition_map_state_eq_runEventBlocksFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds)
    (horizon : Nat)
    (state : (G.toMachine iface).BoundedState horizon)
    (action :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).LegalAction
        state)) :
    PMF.map (fun bounded => bounded.state)
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          state action) =
      (G.toMachine iface).runEventBlocksFrom
        [roundPrimitiveEvents G iface state.state action.1]
        state.state := by
  rw [toFOSGView_toBoundedFOSG_transition_map_state_eq_runEventsFrom]
  simp

/-- Primitive event blocks extracted from a bounded graph-FOSG step list.

Each bounded FOSG step is one frontier round.  This projection forgets the
sampled checkpoint destination and keeps the primitive machine event block
selected by the round action at the step source. -/
noncomputable def boundedFOSGStepEventBlocks
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    (steps :
      List (((G.toFOSGView iface hsound).toBoundedFOSG horizon).Step)) :
    List (List (G.toMachine iface).Event) :=
  steps.map fun step =>
    roundPrimitiveEvents G iface step.src.state step.act.1

/-- Primitive event blocks extracted from a bounded graph-FOSG history. -/
noncomputable def boundedFOSGHistoryEventBlocks
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History)) :
    List (List (G.toMachine iface).Event) :=
  boundedFOSGStepEventBlocks G iface hsound horizon h.steps

/-- Every realized bounded graph-FOSG step chain is backed by a primitive
machine blocked run whose support contains the same checkpoint endpoint. -/
theorem boundedFOSGStepEventBlocks_lastState_mem_runEventBlocksFrom_support
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat) :
    ∀ {start : (G.toMachine iface).BoundedState horizon}
      {steps :
        List (((G.toFOSGView iface hsound).toBoundedFOSG horizon).Step)},
      ((G.toFOSGView iface hsound).toBoundedFOSG horizon).StepChainFrom
          start steps →
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).lastStateFrom
            start steps).state ∈
          ((G.toMachine iface).runEventBlocksFrom
            (boundedFOSGStepEventBlocks G iface hsound horizon steps)
            start.state).support
  | start, [], _hchain => by
      simp [boundedFOSGStepEventBlocks, GameTheory.FOSG.lastStateFrom]
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      cases hsrc
      let block : List (G.toMachine iface).Event :=
        roundPrimitiveEvents G iface step.src.state step.act.1
      have hblock :
          step.dst.state ∈
            ((G.toMachine iface).runEventBlocksFrom [block]
              step.src.state).support := by
        have hmap :
            step.dst.state ∈
              (PMF.map (fun bounded => bounded.state)
                (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
                  step.src step.act)).support := by
          exact (PMF.mem_support_map_iff _ _ _).2
            ⟨step.dst, (PMF.mem_support_iff _ _).2 step.support, rfl⟩
        rw [toFOSGView_toBoundedFOSG_transition_map_state_eq_runEventBlocksFrom
          (G := G) (iface := iface) (hsound := hsound)
          (horizon := horizon) (state := step.src) (action := step.act)] at hmap
        simpa [block] using hmap
      have htailSupport :
          (((G.toFOSGView iface hsound).toBoundedFOSG horizon).lastStateFrom
              step.dst steps).state ∈
            ((G.toMachine iface).runEventBlocksFrom
              (boundedFOSGStepEventBlocks G iface hsound horizon steps)
              step.dst.state).support :=
        boundedFOSGStepEventBlocks_lastState_mem_runEventBlocksFrom_support
          G iface hsound horizon htail
      change
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).lastStateFrom
            step.dst steps).state ∈
          ((G.toMachine iface).runEventBlocksFrom
            ([block] ++
              boundedFOSGStepEventBlocks G iface hsound horizon steps)
            step.src.state).support
      rw [Machine.runEventBlocksFrom_append]
      rw [PMF.mem_support_bind_iff]
      exact ⟨step.dst.state, hblock, htailSupport⟩

/-- Every realized bounded graph-FOSG history extracts a primitive machine
blocked trace whose endpoint support contains the history's checkpoint state. -/
theorem boundedFOSGHistory_state_mem_runEventBlocksFrom_support
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History)) :
    h.lastState.state ∈
      ((G.toMachine iface).runEventBlocksFrom
        (boundedFOSGHistoryEventBlocks G iface hsound horizon h)
        (G.toMachine iface).init).support := by
  simpa [boundedFOSGHistoryEventBlocks,
    boundedFOSGStepEventBlocks, GameTheory.FOSG.History.lastState,
    EventGraph.toMachine_init] using
    (boundedFOSGStepEventBlocks_lastState_mem_runEventBlocksFrom_support
      G iface hsound horizon h.chain)

/-- One bounded graph-FOSG transition, projected to the history's extracted
event-block prefix and the successor checkpoint state, is exactly the
corresponding primitive machine blocked run. -/
theorem boundedFOSG_transition_map_eventBlocks_state_eq_runEventBlocksFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History))
    (action :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).LegalAction
        h.lastState)) :
    PMF.map
        (fun dst =>
          (boundedFOSGHistoryEventBlocks G iface hsound horizon h ++
              [roundPrimitiveEvents G iface h.lastState.state action.1],
            dst.state))
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          h.lastState action) =
      PMF.map
        (fun next =>
          (boundedFOSGHistoryEventBlocks G iface hsound horizon h ++
              [roundPrimitiveEvents G iface h.lastState.state action.1],
            next))
        ((G.toMachine iface).runEventBlocksFrom
          [roundPrimitiveEvents G iface h.lastState.state action.1]
          h.lastState.state) := by
  let attach : (G.toMachine iface).State →
      List (List (G.toMachine iface).Event) × (G.toMachine iface).State :=
    fun next =>
      (boundedFOSGHistoryEventBlocks G iface hsound horizon h ++
          [roundPrimitiveEvents G iface h.lastState.state action.1],
        next)
  have hstate :=
    toFOSGView_toBoundedFOSG_transition_map_state_eq_runEventBlocksFrom
      (G := G) (iface := iface) (hsound := hsound)
      (horizon := horizon) (state := h.lastState) (action := action)
  change
    PMF.map (fun dst => attach dst.state)
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          h.lastState action) =
      PMF.map attach
        ((G.toMachine iface).runEventBlocksFrom
          [roundPrimitiveEvents G iface h.lastState.state action.1]
          h.lastState.state)
  rw [← hstate]
  rw [PMF.map_comp]
  rfl

/-- Binding a continuation over one bounded graph-FOSG transition is the same
as binding that continuation over the corresponding primitive machine blocked
run, with the bounded presentation depth reattached to the checkpoint state. -/
theorem boundedFOSG_transition_bind_eq_runEventBlocksFrom_bind
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History))
    (action :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).LegalAction
        h.lastState))
    {α : Type}
    (K : (G.toMachine iface).BoundedState horizon → PMF α) :
    ((((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          h.lastState action).bind K) =
      ((G.toMachine iface).runEventBlocksFrom
          [roundPrimitiveEvents G iface h.lastState.state action.1]
          h.lastState.state).bind
        (fun next =>
          K (h.lastState.succ
            (Nat.lt_of_not_ge
              (fun hle => action.2.1 (Or.inr hle)))
            next)) := by
  rw [Machine.FOSGView.toBoundedFOSG_transition]
  change
    (PMF.map
        (fun next =>
          h.lastState.succ
            (Nat.lt_of_not_ge
              (fun hle => action.2.1 (Or.inr hle)))
            next)
        (roundTransition G h.lastState.state action.1)).bind K =
      ((G.toMachine iface).runEventBlocksFrom
          [roundPrimitiveEvents G iface h.lastState.state action.1]
          h.lastState.state).bind
        (fun next =>
          K (h.lastState.succ
            (Nat.lt_of_not_ge
              (fun hle => action.2.1 (Or.inr hle)))
            next))
  rw [PMF.bind_map]
  rw [roundTransition_eq_runEventsFrom_roundPrimitiveEvents
    (G := G) (iface := iface) (cfg := h.lastState.state)
    (joint := action.1)]
  rw [Machine.runEventBlocksFrom_singleton]
  rfl

/-- History-dependent blocked primitive trace distribution induced by a
bounded graph-FOSG behavioral profile.

The state of this process is still the FOSG history: strategies are allowed to
depend on information-state history.  The machine contribution at each
nonterminal FOSG round is the primitive event block selected by that round. -/
noncomputable def boundedFOSGBlockTraceDistFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon)) :
    Nat →
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History) →
        PMF (List (List (G.toMachine iface).Event) × (G.toMachine iface).State)
  | 0, h =>
      PMF.pure
        (boundedFOSGHistoryEventBlocks G iface hsound horizon h,
          h.lastState.state)
  | n + 1, h => by
      classical
      exact
        if hterm :
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon).terminal
              h.lastState then
          PMF.pure
            (boundedFOSGHistoryEventBlocks G iface hsound horizon h,
              h.lastState.state)
        else
          (GameTheory.FOSG.legalActionLaw
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon)
            σ h hterm).bind fun action =>
            ((G.toMachine iface).runEventBlocksFrom
              [roundPrimitiveEvents G iface h.lastState.state action.1]
              h.lastState.state).bind fun next =>
                boundedFOSGBlockTraceDistFrom
                  G iface hsound horizon σ n
                  (h.extendByOutcome action
                    (h.lastState.succ
                      (Nat.lt_of_not_ge
                        (fun hle => action.2.1 (Or.inr hle)))
                      next))

@[simp] theorem boundedFOSGBlockTraceDistFrom_zero
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon))
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History)) :
    boundedFOSGBlockTraceDistFrom G iface hsound horizon σ 0 h =
      PMF.pure
        (boundedFOSGHistoryEventBlocks G iface hsound horizon h,
          h.lastState.state) := rfl

theorem boundedFOSGBlockTraceDistFrom_succ_terminal
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon))
    (n : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History))
    (hterm :
      ((G.toFOSGView iface hsound).toBoundedFOSG horizon).terminal
        h.lastState) :
    boundedFOSGBlockTraceDistFrom G iface hsound horizon σ (n + 1) h =
      PMF.pure
        (boundedFOSGHistoryEventBlocks G iface hsound horizon h,
          h.lastState.state) := by
  have hterm' :
      (G.toFOSGView iface hsound).boundedTerminal horizon h.lastState := by
    simpa [Machine.FOSGView.toBoundedFOSG_terminal] using hterm
  simp [boundedFOSGBlockTraceDistFrom, hterm']

theorem boundedFOSGBlockTraceDistFrom_succ_nonterminal
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon))
    (n : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History))
    (hterm :
      ¬ ((G.toFOSGView iface hsound).toBoundedFOSG horizon).terminal
        h.lastState) :
    boundedFOSGBlockTraceDistFrom G iface hsound horizon σ (n + 1) h =
      (GameTheory.FOSG.legalActionLaw
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon)
        σ h hterm).bind fun action =>
        ((G.toMachine iface).runEventBlocksFrom
          [roundPrimitiveEvents G iface h.lastState.state action.1]
          h.lastState.state).bind fun next =>
            boundedFOSGBlockTraceDistFrom
              G iface hsound horizon σ n
              (h.extendByOutcome action
                (h.lastState.succ
                  (Nat.lt_of_not_ge
                    (fun hle => action.2.1 (Or.inr hle)))
                  next)) := by
  have hterm' :
      ¬ (G.toFOSGView iface hsound).boundedTerminal horizon h.lastState := by
    simpa [Machine.FOSGView.toBoundedFOSG_terminal] using hterm
  simp [boundedFOSGBlockTraceDistFrom, hterm']

/-- Bounded graph-FOSG execution, projected to extracted primitive event blocks
and checkpoint state, equals the history-dependent blocked machine trace
distribution induced by the same behavioral profile. -/
theorem boundedFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
    [DecidablePred
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).terminal)]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon)) :
    ∀ (n : Nat)
      (h :
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History)),
      PMF.map
          (fun h' =>
            (boundedFOSGHistoryEventBlocks G iface hsound horizon h',
              h'.lastState.state))
          (GameTheory.FOSG.History.runDistFrom
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon) σ n h) =
        boundedFOSGBlockTraceDistFrom G iface hsound horizon σ n h
  | 0, h => by
      rw [GameTheory.FOSG.History.runDistFrom_zero]
      rw [boundedFOSGBlockTraceDistFrom_zero]
      rw [PMF.pure_map]
  | n + 1, h => by
      let BFOSG := (G.toFOSGView iface hsound).toBoundedFOSG horizon
      by_cases hterm : BFOSG.terminal h.lastState
      · rw [GameTheory.FOSG.History.runDistFrom_succ_terminal
          (G := BFOSG) σ n h hterm]
        rw [boundedFOSGBlockTraceDistFrom_succ_terminal
          (G := G) (iface := iface) (hsound := hsound)
          (horizon := horizon) σ n h hterm]
        rw [PMF.pure_map]
      · rw [GameTheory.FOSG.History.runDistFrom_succ_nonterminal
          (G := BFOSG) σ n h hterm]
        rw [boundedFOSGBlockTraceDistFrom_succ_nonterminal
          (G := G) (iface := iface) (hsound := hsound)
          (horizon := horizon) σ n h hterm]
        rw [PMF.map_bind]
        congr
        funext action
        rw [PMF.map_bind]
        conv_lhs =>
          arg 2
          intro dst
          rw [boundedFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
            G iface hsound horizon σ n (h.extendByOutcome action dst)]
        exact
          boundedFOSG_transition_bind_eq_runEventBlocksFrom_bind
            G iface hsound horizon h action
            (fun dst =>
              boundedFOSGBlockTraceDistFrom
                G iface hsound horizon σ n
                (h.extendByOutcome action dst))

/-- Outcome projection of bounded graph-FOSG execution equals outcome
projection of the corresponding history-dependent blocked machine trace
distribution. -/
theorem boundedFOSG_runDistFrom_map_outcome_eq_blockTraceDistFrom_map_outcome
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
    [DecidablePred
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).terminal)]
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon))
    (n : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History)) :
    PMF.map
        (fun h' => (G.toMachine iface).outcome h'.lastState.state)
        (GameTheory.FOSG.History.runDistFrom
          ((G.toFOSGView iface hsound).toBoundedFOSG horizon) σ n h) =
      PMF.map
        (fun trace => (G.toMachine iface).outcome trace.2)
        (boundedFOSGBlockTraceDistFrom G iface hsound horizon σ n h) := by
  let project :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History) →
        List (List (G.toMachine iface).Event) × (G.toMachine iface).State :=
    fun h' =>
      (boundedFOSGHistoryEventBlocks G iface hsound horizon h',
        h'.lastState.state)
  let observe :
      List (List (G.toMachine iface).Event) × (G.toMachine iface).State →
        (G.toMachine iface).Outcome :=
    fun trace => (G.toMachine iface).outcome trace.2
  calc
    PMF.map
        (fun h' => (G.toMachine iface).outcome h'.lastState.state)
        (GameTheory.FOSG.History.runDistFrom
          ((G.toFOSGView iface hsound).toBoundedFOSG horizon) σ n h)
        =
      PMF.map observe
        (PMF.map project
          (GameTheory.FOSG.History.runDistFrom
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon) σ n h)) := by
          rw [PMF.map_comp]
          rfl
    _ =
      PMF.map observe
        (boundedFOSGBlockTraceDistFrom G iface hsound horizon σ n h) := by
          rw [boundedFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
            (G := G) (iface := iface) (hsound := hsound)
            (horizon := horizon) σ n h]

/-- Public bounded behavioral outcome kernel of a graph-FOSG view, computed as
the machine outcome map of the induced blocked primitive trace distribution. -/
theorem boundedFOSG_outcomeFromBehavioral_eq_blockTraceDist
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
    [Fintype ((G.toMachine iface).BoundedState horizon)]
    [DecidablePred
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).terminal)]
    (β :
      ((G.toFOSGView iface hsound).BoundedBehavioralProfile horizon))
    (steps : Nat) :
    ((G.toFOSGView iface hsound).boundedOutcomeFromBehavioral
        horizon β steps) =
      PMF.map
        (fun trace => (G.toMachine iface).outcome trace.2)
        (boundedFOSGBlockTraceDistFrom G iface hsound horizon β.extend steps
          (GameTheory.FOSG.History.nil
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon))) := by
  simpa [Machine.FOSGView.boundedOutcomeFromBehavioral,
    Machine.FOSGView.boundedHistoryOutcome, GameTheory.FOSG.runDist] using
    (boundedFOSG_runDistFrom_map_outcome_eq_blockTraceDistFrom_map_outcome
      (G := G) (iface := iface) (hsound := hsound)
      (horizon := horizon) β.extend steps
      (GameTheory.FOSG.History.nil
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon)))

/-- Public bounded pure outcome kernel of a graph-FOSG view, computed as the
machine outcome map of the blocked primitive trace distribution induced by the
pure profile's behavioral embedding. -/
theorem boundedFOSG_outcomeFromPure_eq_blockTraceDist
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    [Fintype Player]
    [∀ player, Fintype (Option ((G.toFOSGView iface hsound).Act player))]
    [Fintype ((G.toMachine iface).BoundedState horizon)]
    [DecidablePred
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).terminal)]
    (π :
      ((G.toFOSGView iface hsound).BoundedPureProfile horizon))
    (steps : Nat) :
    ((G.toFOSGView iface hsound).boundedOutcomeFromPure
        horizon π steps) =
      PMF.map
        (fun trace => (G.toMachine iface).outcome trace.2)
        (boundedFOSGBlockTraceDistFrom G iface hsound horizon
          (GameTheory.FOSG.legalPureToBehavioral
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon) π.extend)
          steps
          (GameTheory.FOSG.History.nil
            ((G.toFOSGView iface hsound).toBoundedFOSG horizon))) := by
  simpa [Machine.FOSGView.boundedOutcomeFromPure,
    Machine.FOSGView.boundedHistoryOutcome, GameTheory.FOSG.runDist] using
    (boundedFOSG_runDistFrom_map_outcome_eq_blockTraceDistFrom_map_outcome
      (G := G) (iface := iface) (hsound := hsound)
      (horizon := horizon)
      (GameTheory.FOSG.legalPureToBehavioral
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon) π.extend)
      steps
      (GameTheory.FOSG.History.nil
        ((G.toFOSGView iface hsound).toBoundedFOSG horizon)))

/-- One-step form matching `FOSG.History.runDistFrom`: if the sampled bounded
destination extends the FOSG history, then the extracted block prefix and
checkpoint state have the same distribution as the primitive machine blocked
run for the selected frontier round. -/
theorem boundedFOSG_transition_map_extend_eventBlocks_state_eq_runEventBlocksFrom
    (G : Vegas.EventGraph Player L) (iface : MachineInterface G)
    (hsound : G.HasStableFrontierRounds) (horizon : Nat)
    (h :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).History))
    (action :
      (((G.toFOSGView iface hsound).toBoundedFOSG horizon).LegalAction
        h.lastState)) :
    PMF.map
        (fun dst =>
          let h' := h.extendByOutcome action dst
          (boundedFOSGHistoryEventBlocks G iface hsound horizon h',
            h'.lastState.state))
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          h.lastState action) =
      PMF.map
        (fun next =>
          (boundedFOSGHistoryEventBlocks G iface hsound horizon h ++
              [roundPrimitiveEvents G iface h.lastState.state action.1],
            next))
        ((G.toMachine iface).runEventBlocksFrom
          [roundPrimitiveEvents G iface h.lastState.state action.1]
          h.lastState.state) := by
  let transition :=
    (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
      h.lastState action)
  have hproject :
      PMF.map
          (fun dst =>
            let h' := h.extendByOutcome action dst
            (boundedFOSGHistoryEventBlocks G iface hsound horizon h',
              h'.lastState.state))
          transition =
        PMF.map
          (fun dst =>
            (boundedFOSGHistoryEventBlocks G iface hsound horizon h ++
                [roundPrimitiveEvents G iface h.lastState.state action.1],
              dst.state))
          transition := by
    change
      transition.bind
          (fun dst =>
            PMF.pure
              (let h' := h.extendByOutcome action dst
              (boundedFOSGHistoryEventBlocks G iface hsound horizon h',
                h'.lastState.state))) =
        transition.bind
          (fun dst =>
            PMF.pure
              (boundedFOSGHistoryEventBlocks G iface hsound horizon h ++
                  [roundPrimitiveEvents G iface h.lastState.state action.1],
                dst.state))
    refine Math.ProbabilityMassFunction.bind_congr_on_support
      transition _ _ ?_
    intro dst hdst
    have hsuppLocal : transition dst ≠ 0 :=
      (PMF.mem_support_iff _ _).1 hdst
    have hsupp :
        (((G.toFOSGView iface hsound).toBoundedFOSG horizon).transition
          h.lastState action) dst ≠ 0 := by
      simpa [transition] using hsuppLocal
    rw [GameTheory.FOSG.History.extendByOutcome_of_support
      (h := h) (a := action) (dst := dst) hsupp]
    simp [boundedFOSGHistoryEventBlocks, boundedFOSGStepEventBlocks]
  rw [hproject]
  exact
    boundedFOSG_transition_map_eventBlocks_state_eq_runEventBlocksFrom
      G iface hsound horizon h action

end EventGraph

end Vegas
