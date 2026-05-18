import Vegas.Core.ToEventGraph
import Vegas.GameBridge.FOSG.FromEventGraph
import Vegas.Core.Finite

/-!
# FOSG bridge for checked Vegas programs

This module packages checked-program event graphs as FOSG views and relates
bounded FOSG histories to primitive event-graph machine traces.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- FOSG view of the program event-graph machine. -/
noncomputable def eventGraphFOSGView
    (g : WFProgram P L) :
    (eventGraphMachine g).FOSGView :=
  (programEventGraph g).toFOSGView (eventGraphMachineInterface g)
    (programEventGraph_hasLocalFrontierRounds g)

private theorem eventGraph_done_subset_nodes
    {G : EventGraph P L} (cfg : G.Configuration) :
    cfg.done ⊆ G.nodes := by
  intro node hdone
  exact (G.mem_done_iff cfg.result node).mp hdone |>.1

private theorem eventGraph_extendFrontier_done_card_succ_le
    {G : EventGraph P L} (cfg : G.Configuration)
    {realization : EventGraph.FrontierRealization G cfg}
    (hlegal : realization.Legal)
    {node : G.Node}
    (hfrontier : node ∈ cfg.frontier) :
    cfg.done.card + 1 ≤
      (cfg.extendFrontier realization hlegal).done.card := by
  classical
  have hsubset :
      insert node cfg.done ⊆
        (cfg.extendFrontier realization hlegal).done := by
    intro candidate hcandidate
    rcases Finset.mem_insert.mp hcandidate with hcandidate | hdone
    · subst candidate
      refine (G.mem_done_iff
        (cfg.extendFrontier realization hlegal).result node).mpr ?_
      exact ⟨cfg.mem_nodes_of_mem_frontier hfrontier, by
        simp [EventGraph.Configuration.extendFrontier_result_of_mem
          cfg realization hlegal hfrontier]⟩
    · have hdoneData := (G.mem_done_iff cfg.result candidate).mp hdone
      have hnotFrontier : candidate ∉ cfg.frontier := by
        intro hcandidateFrontier
        have hsome := hdoneData.2
        have hnone := cfg.not_done_of_mem_frontier hcandidateFrontier
        cases hresult : cfg.result candidate <;>
          simp [hresult] at hsome hnone
      refine (G.mem_done_iff
        (cfg.extendFrontier realization hlegal).result candidate).mpr ?_
      exact ⟨hdoneData.1, by
        simpa [EventGraph.Configuration.extendFrontier_result_of_not_mem
          cfg realization hlegal hnotFrontier] using hdoneData.2⟩
  have hnotDone : node ∉ cfg.done := by
    intro hdone
    have hdoneSome := (G.mem_done_iff cfg.result node).mp hdone |>.2
    have hnone := cfg.not_done_of_mem_frontier hfrontier
    cases hresult : cfg.result node <;> simp [hresult] at hdoneSome hnone
  have hcard := Finset.card_le_card hsubset
  simpa [Finset.card_insert_of_notMem hnotDone] using hcard

private theorem eventGraph_boundedFOSG_step_done_card_succ_le
    (g : WFProgram P L) (horizon : Nat)
    {src dst : (eventGraphMachine g).BoundedState horizon}
    {action :
      (((eventGraphFOSGView g).toBoundedFOSG horizon).LegalAction src)}
    (hsupp :
      ((eventGraphFOSGView g).toBoundedFOSG horizon).transition
        src action dst ≠ 0) :
    src.state.done.card + 1 ≤ dst.state.done.card := by
  classical
  let rawAction :=
    (eventGraphFOSGView g).boundedActionToAction horizon src action
  have hnotGraph : ¬ (eventGraphMachine g).terminal src.state := by
    intro hgraph
    exact action.2.1 (by
      rw [Machine.FOSGView.toBoundedFOSG_terminal]
      exact Or.inl hgraph)
  have hboundedMem :
      dst ∈
        (((eventGraphFOSGView g).toBoundedFOSG horizon).transition
          src action).support :=
    (PMF.mem_support_iff _ _).2 hsupp
  have hstateMem :
      dst.state ∈
        (PMF.map (fun bounded => bounded.state)
          (((eventGraphFOSGView g).toBoundedFOSG horizon).transition
            src action)).support :=
    (PMF.mem_support_map_iff _ _ _).2
      ⟨dst, hboundedMem, rfl⟩
  rw [Machine.FOSGView.toBoundedFOSG_transition_map_state] at hstateMem
  have hroundLegal :
      GameTheory.JointActionLegal
        (EventGraph.PlayerRoundAction (programEventGraph g))
        (EventGraph.roundActive (programEventGraph g))
        EventGraph.Configuration.terminal
        (EventGraph.roundAvailable (programEventGraph g))
        src.state rawAction.1 := by
    simpa [rawAction, eventGraphFOSGView, eventGraphMachine,
      EventGraph.toFOSGView] using rawAction.2
  have hfrontierMem :
      dst.state ∈
        (EventGraph.frontierRealizationTransition (programEventGraph g)
          src.state ⟨rawAction.1, hroundLegal⟩).support := by
    simpa [rawAction, eventGraphFOSGView, eventGraphMachine,
      EventGraph.toFOSGView] using hstateMem
  rcases EventGraph.frontierRealizationTransition_support_extend
      (programEventGraph g) src.state ⟨rawAction.1, hroundLegal⟩
      hfrontierMem with
    ⟨realization, _hrealizationSupport, hrealizationLegal, hdst⟩
  rcases src.state.frontier_nonempty_of_not_terminal hnotGraph with
    ⟨node, hnodeFrontier⟩
  rw [hdst]
  exact eventGraph_extendFrontier_done_card_succ_le
    src.state hrealizationLegal hnodeFrontier

private theorem eventGraph_boundedFOSG_stepChain_done_card_ge_length
    (g : WFProgram P L) (horizon : Nat) :
    ∀ {start : (eventGraphMachine g).BoundedState horizon}
      {steps : List (((eventGraphFOSGView g).toBoundedFOSG horizon).Step)},
      ((eventGraphFOSGView g).toBoundedFOSG horizon).StepChainFrom
          start steps →
        start.state.done.card + steps.length ≤
          (((eventGraphFOSGView g).toBoundedFOSG horizon).lastStateFrom
            start steps).state.done.card
  | start, [], _hchain => by
      simp [GameTheory.FOSG.lastStateFrom]
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      have hstartDone :
          start.state.done.card = step.src.state.done.card := by
        rw [← hsrc]
      have hstep :
          step.src.state.done.card + 1 ≤ step.dst.state.done.card :=
        eventGraph_boundedFOSG_step_done_card_succ_le
          g horizon step.support
      have htailDone :
          step.dst.state.done.card + steps.length ≤
            (((eventGraphFOSGView g).toBoundedFOSG horizon).lastStateFrom
              step.dst steps).state.done.card :=
        eventGraph_boundedFOSG_stepChain_done_card_ge_length
          (g := g) (horizon := horizon) htail
      simp [GameTheory.FOSG.lastStateFrom, hstartDone]
      omega

private theorem eventGraph_boundedFOSG_history_done_card_ge_depth
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    h.lastState.depth ≤ h.lastState.state.done.card := by
  have hchainDone :
      ((Machine.BoundedState.init (eventGraphMachine g) horizon).state.done.card) +
          h.steps.length ≤ h.lastState.state.done.card := by
    simpa [GameTheory.FOSG.History.lastState,
      Machine.FOSGView.toBoundedFOSG_init] using
      (eventGraph_boundedFOSG_stepChain_done_card_ge_length
        (g := g) (horizon := horizon) h.chain)
  have hinitDone :
      ((Machine.BoundedState.init (eventGraphMachine g) horizon).state.done.card) =
        0 := by
    simp [eventGraphMachine, EventGraph.toMachine,
      EventGraph.Configuration.initial, EventGraph.Configuration.done,
      EventGraph.done]
  have hstepsDone : h.steps.length ≤ h.lastState.state.done.card := by
    omega
  have hdepth :
      h.lastState.depth = h.steps.length :=
    (eventGraphFOSGView g).toBoundedFOSG_history_depth horizon h
  omega

private theorem eventGraph_terminal_of_done_card_ge_syntaxSteps
    (g : WFProgram P L)
    (cfg : (programEventGraph g).Configuration)
    (hcard : syntaxSteps g.prog ≤ cfg.done.card) :
    cfg.terminal := by
  have hnodesCard :
      (programEventGraph g).nodes.card ≤ syntaxSteps g.prog := by
    change (ProgramNode.finset g.prog).card ≤ syntaxSteps g.prog
    exact ProgramNode.finset_card_le_syntaxSteps g.prog
  have hnodes_le_done :
      (programEventGraph g).nodes.card ≤ cfg.done.card :=
    Nat.le_trans hnodesCard hcard
  have hdone_subset :
      cfg.done ⊆ (programEventGraph g).nodes :=
    eventGraph_done_subset_nodes cfg
  have hdone_eq_nodes :
      cfg.done = (programEventGraph g).nodes :=
    Finset.eq_of_subset_of_card_le hdone_subset hnodes_le_done
  intro node hnode
  rw [hdone_eq_nodes]
  exact hnode

/-- A checked game that is played legally to completion reaches its declared
payoff rule. The internal bound is the number of source steps in the checked
program. -/
theorem eventGraph_wholeGame_reaches_declared_payoff_rule
    (g : WFProgram P L)
    (h :
      (((eventGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).History))
    (hcomplete :
      ((eventGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).terminal h.lastState) :
    ∃ env : VEnv L (ProgramField.finalVCtx g.prog),
      ProgramField.finalEnv? g.prog
          (eventGraphConfigValue? g h.lastState.state) = some env ∧
        eventGraphOutcome g h.lastState.state =
          evalPayoffs (ProgramField.finalPayoffs g.prog) env := by
  have hgraphTerminal :
      (eventGraphMachine g).terminal h.lastState.state := by
    rw [Machine.FOSGView.toBoundedFOSG_terminal] at hcomplete
    rcases hcomplete with hterminal | hcut
    · exact hterminal
    · have hdoneDepth :=
        eventGraph_boundedFOSG_history_done_card_ge_depth
          g (syntaxSteps g.prog) h
      have hdoneSteps : syntaxSteps g.prog ≤ h.lastState.state.done.card := by
        omega
      exact eventGraph_terminal_of_done_card_ge_syntaxSteps
        g h.lastState.state hdoneSteps
  exact eventGraphOutcome_eq_evalPayoffs_of_terminal g hgraphTerminal

/-- Primitive machine event batches extracted from a bounded event-graph FOSG
history. Each event batch is one frontier round of the public FOSG view. -/
noncomputable def eventGraphFOSGHistoryEventBatches
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    List (List (eventGraphMachine g).Event) :=
  EventGraph.boundedFOSGHistoryEventBatches
    (programEventGraph g) (eventGraphMachineInterface g)
    (programEventGraph_hasLocalFrontierRounds g) horizon h

/-- Program-specialized availability witness for the primitive batches
extracted from a bounded event-graph FOSG history. -/
theorem eventGraphFOSGHistory_availableRunBatchesFrom
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    (eventGraphMachine g).AvailableRunBatchesFrom (eventGraphMachine g).init
      (eventGraphFOSGHistoryEventBatches g horizon h)
      h.lastState.state := by
  simpa [eventGraphFOSGHistoryEventBatches, eventGraphMachine,
    eventGraphFOSGView] using
    (EventGraph.boundedFOSGHistory_availableRunBatchesFrom
      (programEventGraph g) (eventGraphMachineInterface g)
      (programEventGraph_hasLocalFrontierRounds g) horizon h)

/-- Program-specialized support theorem for primitive batches extracted from a
bounded event-graph FOSG history. -/
theorem eventGraphFOSGHistory_state_mem_runEventBatchesFrom_support
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    h.lastState.state ∈
      ((eventGraphMachine g).runEventBatchesFrom
        (eventGraphFOSGHistoryEventBatches g horizon h)
        (eventGraphMachine g).init).support :=
  Machine.AvailableRunBatchesFrom.mem_runEventBatchesFrom_support
    (eventGraphFOSGHistory_availableRunBatchesFrom g horizon h)

/-- Realized primitive machine events represented by one event-graph FOSG
frontier round. Internal events carry the patch found in the realized
destination. -/
noncomputable def eventGraphRealizedEventBatch
    (g : WFProgram P L)
    (cfg : (eventGraphMachine g).State)
    (joint : GameTheory.JointAction (eventGraphFOSGView g).Act)
    (dst : (eventGraphMachine g).State) :
    List (eventGraphMachine g).Event := by
  simpa [eventGraphMachine, eventGraphFOSGView] using
    (EventGraph.realizedEventBatch (programEventGraph g)
      (eventGraphMachineInterface g) cfg joint dst)

/-- Player round-action availability in the event graph is determined by the
public transcript together with the acting player's private observation. -/
theorem eventGraph_roundAvailable_eq_of_observation_eq
    (g : WFProgram P L) (who : P)
    {left right : (programEventGraph g).Configuration}
    (hpriv : eventGraphObserve g who left = eventGraphObserve g who right)
    (hpub : eventGraphPublicView g left = eventGraphPublicView g right) :
    EventGraph.roundAvailable (programEventGraph g) left who =
      EventGraph.roundAvailable (programEventGraph g) right who := by
  classical
  have hfrontierEq := eventGraphPublicView_frontier_eq_of_eq g hpub
  ext action
  constructor
  · intro haction node hfrontier hactor
    have hfrontierLeft : node ∈ left.frontier := by
      simpa [hfrontierEq] using hfrontier
    rcases haction hfrontierLeft hactor with ⟨hpatch, hlegal⟩
    exact ⟨hpatch,
      eventGraph_actionLegal_of_observe_eq g who hfrontier
        hactor hpriv hlegal⟩
  · intro haction node hfrontier hactor
    have hfrontierRight : node ∈ right.frontier := by
      simpa [hfrontierEq] using hfrontier
    rcases haction hfrontierRight hactor with ⟨hpatch, hlegal⟩
    exact ⟨hpatch,
      eventGraph_actionLegal_of_observe_eq g who hfrontier
        hactor hpriv.symm hlegal⟩

/-- The active-player set of an event-graph frontier round is determined by
the public transcript. -/
theorem eventGraph_roundActive_eq_of_publicView_eq
    (g : WFProgram P L)
    {left right : (programEventGraph g).Configuration}
    (hpub : eventGraphPublicView g left = eventGraphPublicView g right) :
    EventGraph.roundActive (programEventGraph g) left =
      EventGraph.roundActive (programEventGraph g) right := by
  classical
  have hfrontier := eventGraphPublicView_frontier_eq_of_eq g hpub
  unfold EventGraph.roundActive
  rw [hfrontier]

/-- Player-facing frontier-round menus in the event graph are determined by
the public transcript together with the player's private observation.

This is the protocol-level "the player knows what they can do" invariant:
two configurations indistinguishable to `who` offer the same optional menu to
`who`, including whether `who` is called at all. -/
theorem eventGraph_roundMenu_eq_of_observation_eq
    (g : WFProgram P L) (who : P)
    {left right : (programEventGraph g).Configuration}
    (hpriv : eventGraphObserve g who left = eventGraphObserve g who right)
    (hpub : eventGraphPublicView g left = eventGraphPublicView g right) :
    EventGraph.roundMenu (programEventGraph g) left who =
      EventGraph.roundMenu (programEventGraph g) right who := by
  have hactive :=
    eventGraph_roundActive_eq_of_publicView_eq g hpub
  have havailable :=
    eventGraph_roundAvailable_eq_of_observation_eq g who hpriv hpub
  simp [EventGraph.roundMenu, hactive, havailable]

/-- At a bounded event-graph FOSG state before the cutoff, legal optional
moves are determined by the player's latest private observation and the public
transcript. -/
theorem eventGraph_boundedAvailableMovesAtState_eq_of_observation_eq
    (g : WFProgram P L) (horizon : Nat) (who : P)
    {left right : (eventGraphMachine g).BoundedState horizon}
    (hcut : ¬ horizon ≤ left.depth)
    (hcut' : ¬ horizon ≤ right.depth)
    (hpriv :
      eventGraphObserve g who left.state =
        eventGraphObserve g who right.state)
    (hpub :
      eventGraphPublicView g left.state =
        eventGraphPublicView g right.state) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMovesAtState
        left who =
      ((eventGraphFOSGView g).toBoundedFOSG horizon).availableMovesAtState
        right who := by
  classical
  have hroundActive :
      EventGraph.roundActive (programEventGraph g) left.state =
        EventGraph.roundActive (programEventGraph g) right.state :=
    eventGraph_roundActive_eq_of_publicView_eq g hpub
  have hroundAvailable :
      EventGraph.roundAvailable (programEventGraph g) left.state who =
        EventGraph.roundAvailable (programEventGraph g) right.state who :=
    eventGraph_roundAvailable_eq_of_observation_eq g who hpriv hpub
  have hactive :
      ((eventGraphFOSGView g).toBoundedFOSG horizon).active left =
        ((eventGraphFOSGView g).toBoundedFOSG horizon).active right := by
    ext player
    simp [Machine.FOSGView.boundedActive, hcut, hcut',
      eventGraphFOSGView, EventGraph.toFOSGView, hroundActive]
  have hactions :
      ((eventGraphFOSGView g).toBoundedFOSG horizon).availableActions
          left who =
        ((eventGraphFOSGView g).toBoundedFOSG horizon).availableActions
          right who := by
    ext action
    simp [Machine.FOSGView.boundedAvailableActions, hcut, hcut',
      eventGraphFOSGView, EventGraph.toFOSGView, hroundAvailable]
  ext move
  cases move with
  | none =>
      change
        who ∉ ((eventGraphFOSGView g).toBoundedFOSG horizon).active left ↔
          who ∉ ((eventGraphFOSGView g).toBoundedFOSG horizon).active right
      rw [hactive]
  | some action =>
      change
        who ∈ ((eventGraphFOSGView g).toBoundedFOSG horizon).active left ∧
            action ∈
              ((eventGraphFOSGView g).toBoundedFOSG horizon).availableActions
                left who ↔
          who ∈ ((eventGraphFOSGView g).toBoundedFOSG horizon).active right ∧
            action ∈
              ((eventGraphFOSGView g).toBoundedFOSG horizon).availableActions
                right who
      rw [hactive, hactions]

/-- Bounded event-graph FOSGs satisfy the legal-observability
condition required by Kuhn's theorem. -/
theorem eventGraphFOSGView_toBoundedFOSG_legalObservable
    (g : WFProgram P L) (horizon : Nat) :
    ((eventGraphFOSGView g).toBoundedFOSG horizon).LegalObservable := by
  intro who h h' hInfo
  let G := (eventGraphFOSGView g).toBoundedFOSG horizon
  have hobsLen :
      (GameTheory.FOSG.InfoState.observationEvents
        (G := G) (i := who) (h.playerView who)).length =
        h.steps.length := by
    simpa [G] using
      (eventGraphFOSGView g)
        |>.toBoundedFOSG_history_playerView_observationEvents_length
          horizon h who
  have hobsLen' :
      (GameTheory.FOSG.InfoState.observationEvents
        (G := G) (i := who) (h'.playerView who)).length =
        h'.steps.length := by
    simpa [G] using
      (eventGraphFOSGView g)
        |>.toBoundedFOSG_history_playerView_observationEvents_length
          horizon h' who
  have hlenEq : h.steps.length = h'.steps.length := by
    have hlen :=
      congrArg
        (fun s =>
          (GameTheory.FOSG.InfoState.observationEvents
            (G := G) (i := who) s).length)
        hInfo
    change
      (GameTheory.FOSG.InfoState.observationEvents
        (G := G) (i := who) (h.playerView who)).length =
        (GameTheory.FOSG.InfoState.observationEvents
          (G := G) (i := who) (h'.playerView who)).length at hlen
    rw [hobsLen, hobsLen'] at hlen
    exact hlen
  by_cases hnil : h.steps = []
  · have hnil' : h'.steps = [] := by
      have hlen0 : h'.steps.length = 0 := by
        rw [← hlenEq, hnil]
        rfl
      exact List.eq_nil_of_length_eq_zero hlen0
    have hh : h = GameTheory.FOSG.History.nil G := by
      cases h with
      | mk steps chain =>
          cases hnil
          rfl
    have hh' : h' = GameTheory.FOSG.History.nil G := by
      cases h' with
      | mk steps chain =>
          cases hnil'
          rfl
    subst hh
    subst hh'
    rfl
  · have hnil' : h'.steps ≠ [] := by
      intro hnil'
      have hlen0 : h.steps.length = 0 := by
        rw [hlenEq, hnil']
        rfl
      exact hnil (List.eq_nil_of_length_eq_zero hlen0)
    have hdepthLen :=
      (eventGraphFOSGView g)
        |>.toBoundedFOSG_history_depth horizon h
    have hdepthLen' :=
      (eventGraphFOSGView g)
        |>.toBoundedFOSG_history_depth horizon h'
    have hcutEq :
        (horizon ≤ h.lastState.depth) ↔
          (horizon ≤ h'.lastState.depth) := by
      have heqDepth :
          h.lastState.depth = h'.lastState.depth := by
        calc
          h.lastState.depth = h.steps.length := hdepthLen
          _ = h'.steps.length := hlenEq
          _ = h'.lastState.depth := hdepthLen'.symm
      constructor
      · intro hle
        exact heqDepth ▸ hle
      · intro hle
        exact heqDepth.symm ▸ hle
    by_cases hcut : horizon ≤ h.lastState.depth
    · have hcut' : horizon ≤ h'.lastState.depth :=
        hcutEq.mp hcut
      have hInactive : who ∉ G.active h.lastState := by
        simp [G, Machine.FOSGView.boundedActive, hcut]
      have hInactive' : who ∉ G.active h'.lastState := by
        simp [G, Machine.FOSGView.boundedActive, hcut']
      rw [G.availableMoves_eq_singleton_none_of_not_mem_active h hInactive,
        G.availableMoves_eq_singleton_none_of_not_mem_active h' hInactive']
    · have hcut' :
          ¬ horizon ≤ h'.lastState.depth := by
        intro hle
        exact hcut (hcutEq.mpr hle)
      have hlatest :=
        congrArg
          (GameTheory.FOSG.InfoState.latestObservation?
            (G := G) (i := who))
          hInfo
      have hlatest₁ :
          GameTheory.FOSG.InfoState.latestObservation?
              (G := G) (i := who) (h.playerView who) =
            some
              (eventGraphObserve g who h.lastState.state,
                eventGraphPublicView g h.lastState.state) := by
        simpa [G, eventGraphMachine, EventGraph.toMachine,
          eventGraphMachineInterface] using
          (eventGraphFOSGView g)
            |>.toBoundedFOSG_latestObservation?_history_of_ne_nil
              horizon who h hnil
      have hlatest₂ :
          GameTheory.FOSG.InfoState.latestObservation?
              (G := G) (i := who) (h'.playerView who) =
            some
              (eventGraphObserve g who h'.lastState.state,
                eventGraphPublicView g h'.lastState.state) := by
        simpa [G, eventGraphMachine, EventGraph.toMachine,
          eventGraphMachineInterface] using
          (eventGraphFOSGView g)
            |>.toBoundedFOSG_latestObservation?_history_of_ne_nil
              horizon who h' hnil'
      rw [hlatest₁, hlatest₂] at hlatest
      injection hlatest with hobs
      have hpriv :
          eventGraphObserve g who h.lastState.state =
            eventGraphObserve g who h'.lastState.state :=
        congrArg Prod.fst hobs
      have hpub :
          eventGraphPublicView g h.lastState.state =
            eventGraphPublicView g h'.lastState.state :=
        congrArg Prod.snd hobs
      simpa [GameTheory.FOSG.availableMoves] using
        eventGraph_boundedAvailableMovesAtState_eq_of_observation_eq
          g horizon who hcut hcut' hpriv hpub

/-- Finite state helper for the program event-graph machine. -/
@[reducible] noncomputable instance eventGraphMachine.instFintypeState
    (g : WFProgram P L) [FiniteDomains g] :
    Fintype (eventGraphMachine g).State := by
  classical
  letI : Fintype (ProgramNode g.prog) :=
    ProgramNode.instFintype g.prog
  letI : Fintype (ProgramField g.prog) :=
    ProgramField.instFintype g.prog
  letI :
      ∀ field : ProgramField g.prog, Fintype (L.Val field.ty) :=
    fun field => ProgramField.instFintypeValue g field
  dsimp [eventGraphMachine, EventGraph.toMachine,
    programEventGraph, EventGraph.Configuration,
    EventGraph.ResultAssignment, EventGraph.FieldPatch]
  infer_instance

/-- Finite action helper for the program event-graph machine. -/
@[reducible] noncomputable instance eventGraphMachine.instFintypeAction
    (g : WFProgram P L) [FiniteDomains g] (who : P) :
    Fintype ((eventGraphMachine g).Action who) := by
  classical
  letI : Fintype (ProgramNode g.prog) :=
    ProgramNode.instFintype g.prog
  letI : Fintype (ProgramField g.prog) :=
    ProgramField.instFintype g.prog
  letI :
      ∀ field : ProgramField g.prog, Fintype (L.Val field.ty) :=
    fun field => ProgramField.instFintypeValue g field
  dsimp [eventGraphMachine, EventGraph.toMachine,
    EventGraph.PlayerAction, programEventGraph,
    EventGraph.FieldPatch]
  infer_instance

/-- Finite optional-action helper for the program event-graph machine. -/
@[reducible] noncomputable instance eventGraphMachine.instFintypeOptionAction
    (g : WFProgram P L) [FiniteDomains g] (who : P) :
    Fintype (Option ((eventGraphMachine g).Action who)) := by
  classical
  letI : Fintype ((eventGraphMachine g).Action who) :=
    eventGraphMachine.instFintypeAction g who
  infer_instance

/-- Finite FOSG round-action helper for the event-graph FOSG view. -/
@[reducible] noncomputable instance eventGraphFOSGView.instFintypeAct
    (g : WFProgram P L) [FiniteDomains g] (who : P) :
    Fintype ((eventGraphFOSGView g).Act who) := by
  classical
  letI : Fintype (ProgramNode g.prog) :=
    ProgramNode.instFintype g.prog
  letI : Fintype (ProgramField g.prog) :=
    ProgramField.instFintype g.prog
  letI :
      ∀ field : ProgramField g.prog, Fintype (L.Val field.ty) :=
    fun field => ProgramField.instFintypeValue g field
  haveI : Fintype (programEventGraph g).Node := by
    change Fintype (ProgramNode g.prog)
    exact ProgramNode.instFintype g.prog
  haveI : Fintype (programEventGraph g).Field := by
    change Fintype (ProgramField g.prog)
    exact ProgramField.instFintype g.prog
  haveI :
      ∀ field : (programEventGraph g).Field,
        Fintype (L.Val ((programEventGraph g).fieldTy field)) := by
    intro field
    change Fintype (L.Val field.ty)
    exact ProgramField.instFintypeValue g field
  change Fintype (EventGraph.PlayerRoundAction (programEventGraph g) who)
  exact EventGraph.PlayerRoundAction.instFintype (programEventGraph g) who

/-- Finite optional FOSG round-action helper for event-graph views. -/
@[reducible] noncomputable instance eventGraphFOSGView.instFintypeOptionAct
    (g : WFProgram P L) [FiniteDomains g] (who : P) :
    Fintype (Option ((eventGraphFOSGView g).Act who)) := by
  classical
  letI : Fintype ((eventGraphFOSGView g).Act who) :=
    eventGraphFOSGView.instFintypeAct g who
  infer_instance

/-- Finite internal-event helper for the program event-graph machine. -/
@[reducible] noncomputable instance eventGraphMachine.instFintypeInternal
    (g : WFProgram P L) [FiniteDomains g] :
    Fintype (eventGraphMachine g).Internal := by
  classical
  letI : Fintype (ProgramNode g.prog) :=
    ProgramNode.instFintype g.prog
  letI : Fintype (ProgramField g.prog) :=
    ProgramField.instFintype g.prog
  letI :
      ∀ field : ProgramField g.prog, Fintype (L.Val field.ty) :=
    fun field => ProgramField.instFintypeValue g field
  dsimp [eventGraphMachine, EventGraph.toMachine,
    EventGraph.InternalEvent, programEventGraph]
  infer_instance

/-- Finite primitive-event helper for the program event-graph machine. -/
@[reducible] noncomputable instance eventGraphMachine.instFintypeEvent
    (g : WFProgram P L) [FiniteDomains g] [Fintype P] :
    Fintype (eventGraphMachine g).Event := by
  classical
  letI : ∀ who : P, Fintype ((eventGraphMachine g).Action who) :=
    fun who => eventGraphMachine.instFintypeAction g who
  letI : Fintype (eventGraphMachine g).Internal :=
    eventGraphMachine.instFintypeInternal g
  let playEvents : Finset (eventGraphMachine g).Event :=
    (Finset.univ :
      Finset (Sigma fun who : P => (eventGraphMachine g).Action who)).image
        (fun x => Machine.Event.play x.1 x.2)
  let internalEvents : Finset (eventGraphMachine g).Event :=
    (Finset.univ : Finset (eventGraphMachine g).Internal).image
      (fun event => Machine.Event.internal event)
  refine Fintype.mk (playEvents ∪ internalEvents) ?_
  intro event
  cases event with
  | play who action =>
      exact Finset.mem_union.mpr
        (Or.inl
          (Finset.mem_image.mpr
            ⟨⟨who, action⟩, Finset.mem_univ _, rfl⟩))
  | internal event =>
      exact Finset.mem_union.mpr
        (Or.inr
          (Finset.mem_image.mpr
            ⟨event, Finset.mem_univ _, rfl⟩))

/-- Finite-history helper for bounded event-graph FOSG views. -/
@[reducible] noncomputable instance eventGraphFOSGView.instFintypeBoundedHistory
    (g : WFProgram P L) (horizon : Nat)
    [Fintype P] [FiniteDomains g] :
    Fintype (((eventGraphFOSGView g).toBoundedFOSG horizon).History) := by
  classical
  haveI :
      Fintype ((eventGraphMachine g).BoundedState horizon) :=
    Machine.BoundedState.instFintype
  haveI :
      ∀ who : P, Fintype (Option ((eventGraphFOSGView g).Act who)) :=
    fun who => eventGraphFOSGView.instFintypeOptionAct g who
  exact GameTheory.FOSG.historyFintypeOfBoundedHorizon
    (G := (eventGraphFOSGView g).toBoundedFOSG horizon)
    ((eventGraphFOSGView g).toBoundedFOSG_boundedHorizon horizon)

/-- Terminal decidability for bounded event-graph FOSG views. -/
noncomputable instance eventGraphFOSGView.instDecidablePredBoundedTerminal
    (g : WFProgram P L) (horizon : Nat) :
    DecidablePred (((eventGraphFOSGView g).toBoundedFOSG horizon).terminal) :=
  Classical.decPred _

/-- History-dependent event-batched primitive trace distribution induced by a
bounded event-graph FOSG behavioral profile. -/
noncomputable def eventGraphFOSGEventBatchTraceDistFrom
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((eventGraphFOSGView g).toBoundedFOSG horizon)) :
    Nat →
      (((eventGraphFOSGView g).toBoundedFOSG horizon).History) →
        PMF (List (List (eventGraphMachine g).Event) ×
          (eventGraphMachine g).State) := by
  letI :
      ∀ player,
        Fintype
          (Option
            (((programEventGraph g).toFOSGView
              (eventGraphMachineInterface g)
              (programEventGraph_hasLocalFrontierRounds g)).Act
                player)) := by
    intro player
    simpa [eventGraphFOSGView] using
      (eventGraphFOSGView.instFintypeOptionAct g player)
  simpa [eventGraphMachine, eventGraphFOSGView] using
    (EventGraph.boundedFOSGEventBatchTraceDistFrom
      (programEventGraph g) (eventGraphMachineInterface g)
      (programEventGraph_hasLocalFrontierRounds g) horizon σ)

/-- Bounded event-graph FOSG execution, projected to extracted primitive
event batches and checkpoint state, equals the history-dependent event-batch
machine trace distribution induced by the same behavioral profile. -/
theorem eventGraphFOSG_runDistFrom_map_eventBatches_state_eq_eventBatchTraceDistFrom
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((eventGraphFOSGView g).toBoundedFOSG horizon))
    (n : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    PMF.map
        (fun h' =>
          (eventGraphFOSGHistoryEventBatches g horizon h',
            h'.lastState.state))
        (GameTheory.FOSG.History.runDistFrom
          ((eventGraphFOSGView g).toBoundedFOSG horizon) σ n h) =
      eventGraphFOSGEventBatchTraceDistFrom g horizon σ n h := by
  letI :
      ∀ player,
        Fintype
          (Option
            (((programEventGraph g).toFOSGView
              (eventGraphMachineInterface g)
              (programEventGraph_hasLocalFrontierRounds g)).Act
                player)) := by
    intro player
    simpa [eventGraphFOSGView] using
      (eventGraphFOSGView.instFintypeOptionAct g player)
  letI :
      Fintype
        (((programEventGraph g).toMachine
          (eventGraphMachineInterface g)).BoundedState horizon) := by
    simpa [eventGraphMachine] using
      (inferInstance : Fintype ((eventGraphMachine g).BoundedState horizon))
  letI :
      DecidablePred
        ((((programEventGraph g).toFOSGView
          (eventGraphMachineInterface g)
          (programEventGraph_hasLocalFrontierRounds g)).toBoundedFOSG
            horizon).terminal) :=
    Classical.decPred _
  simpa [eventGraphFOSGHistoryEventBatches, eventGraphMachine,
    eventGraphFOSGView, eventGraphFOSGEventBatchTraceDistFrom] using
      (EventGraph.boundedFOSG_runDistFrom_map_eventBatches_state_eq_eventBatchTraceDistFrom
        (programEventGraph g) (eventGraphMachineInterface g)
        (programEventGraph_hasLocalFrontierRounds g) horizon σ n h)

/-- Initial history of the bounded event-graph FOSG presentation. -/
noncomputable def eventGraphInitialHistory
    (g : WFProgram P L) (horizon : Nat) :
    (((eventGraphFOSGView g).toBoundedFOSG horizon).History) :=
  GameTheory.FOSG.History.nil
    ((eventGraphFOSGView g).toBoundedFOSG horizon)

/-- Project a bounded event-graph FOSG history to primitive event batches and
the checkpoint machine state. -/
noncomputable def eventGraphHistoryTrace
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    List (List (eventGraphMachine g).Event) × (eventGraphMachine g).State :=
  (eventGraphFOSGHistoryEventBatches g horizon h, h.lastState.state)

/-- Outcome extracted from an event-batch event-graph trace. -/
noncomputable def eventGraphTraceOutcome
    (g : WFProgram P L)
    (trace :
      List (List (eventGraphMachine g).Event) ×
        (eventGraphMachine g).State) :
    (eventGraphMachine g).Outcome :=
  (eventGraphMachine g).outcome trace.2

/-- Bounded behavioral outcome kernel of the event-graph FOSG view, computed
as the machine outcome projection of the induced event-batched primitive trace
distribution. -/
theorem eventGraphFOSG_boundedOutcomeFromBehavioral_eq_eventBatchTraceDist
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (β : (eventGraphFOSGView g).BoundedBehavioralProfile horizon)
    (steps : Nat) :
    (eventGraphFOSGView g).boundedOutcomeFromBehavioral
        horizon β steps =
      PMF.map
        (eventGraphTraceOutcome g)
        (eventGraphFOSGEventBatchTraceDistFrom g horizon β.extend steps
          (eventGraphInitialHistory g horizon)) := by
  let run :=
    GameTheory.FOSG.History.runDistFrom
      ((eventGraphFOSGView g).toBoundedFOSG horizon) β.extend steps
      (eventGraphInitialHistory g horizon)
  calc
    (eventGraphFOSGView g).boundedOutcomeFromBehavioral horizon β steps =
      PMF.map
        (fun h' => (eventGraphMachine g).outcome h'.lastState.state)
        run := by
          rfl
    _ = PMF.map (eventGraphTraceOutcome g)
          (PMF.map (eventGraphHistoryTrace g horizon) run) := by
          rw [PMF.map_comp]
          rfl
    _ =
      PMF.map (eventGraphTraceOutcome g)
        (eventGraphFOSGEventBatchTraceDistFrom g horizon β.extend steps
          (eventGraphInitialHistory g horizon)) := by
          have htrace :
              PMF.map (eventGraphHistoryTrace g horizon) run =
                eventGraphFOSGEventBatchTraceDistFrom g horizon β.extend steps
                  (eventGraphInitialHistory g horizon) := by
            simpa [eventGraphHistoryTrace, run] using
              (eventGraphFOSG_runDistFrom_map_eventBatches_state_eq_eventBatchTraceDistFrom
                (g := g) (horizon := horizon) (σ := β.extend)
                (n := steps)
                (h := eventGraphInitialHistory g horizon))
          rw [htrace]

/-- Bounded pure outcome kernel of the event-graph FOSG view, computed as
the machine outcome projection of the event-batched primitive trace distribution
induced by the pure profile's behavioral embedding. -/
theorem eventGraphFOSG_boundedOutcomeFromPure_eq_eventBatchTraceDist
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (π : (eventGraphFOSGView g).BoundedPureProfile horizon)
    (steps : Nat) :
    (eventGraphFOSGView g).boundedOutcomeFromPure
        horizon π steps =
      PMF.map
        (eventGraphTraceOutcome g)
        (eventGraphFOSGEventBatchTraceDistFrom g horizon
          (GameTheory.FOSG.legalPureToBehavioral
            ((eventGraphFOSGView g).toBoundedFOSG horizon) π.extend)
          steps
          (eventGraphInitialHistory g horizon)) := by
  let σ :=
    GameTheory.FOSG.legalPureToBehavioral
      ((eventGraphFOSGView g).toBoundedFOSG horizon) π.extend
  let run :=
    GameTheory.FOSG.History.runDistFrom
      ((eventGraphFOSGView g).toBoundedFOSG horizon) σ steps
      (eventGraphInitialHistory g horizon)
  calc
    (eventGraphFOSGView g).boundedOutcomeFromPure horizon π steps =
      PMF.map
        (fun h' => (eventGraphMachine g).outcome h'.lastState.state)
        run := by
          rfl
    _ = PMF.map (eventGraphTraceOutcome g)
          (PMF.map (eventGraphHistoryTrace g horizon) run) := by
          rw [PMF.map_comp]
          rfl
    _ =
      PMF.map (eventGraphTraceOutcome g)
        (eventGraphFOSGEventBatchTraceDistFrom g horizon σ steps
          (eventGraphInitialHistory g horizon)) := by
          have htrace :
              PMF.map (eventGraphHistoryTrace g horizon) run =
                eventGraphFOSGEventBatchTraceDistFrom g horizon σ steps
                  (eventGraphInitialHistory g horizon) := by
            simpa [eventGraphHistoryTrace, run] using
              (eventGraphFOSG_runDistFrom_map_eventBatches_state_eq_eventBatchTraceDistFrom
                (g := g) (horizon := horizon) (σ := σ)
                (n := steps)
                (h := eventGraphInitialHistory g horizon))
          rw [htrace]


end Vegas
