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
    (programEventGraph_hasStableFrontierRounds g)

private theorem eventGraph_done_subset_nodes
    {G : EventGraph P L} (cfg : G.Configuration) :
    cfg.done ⊆ G.nodes := by
  intro node hdone
  exact (G.mem_done_iff cfg.result node).mp hdone |>.1

private theorem eventGraph_withResult_done_subset
    {G : EventGraph P L} (cfg : G.Configuration)
    {node : G.Node} {slice : G.WriteSlice}
    (hfrontier : node ∈ cfg.frontier)
    (hlegal : G.sliceLegal node slice) :
    cfg.done ⊆ (cfg.withResult slice hfrontier hlegal).done := by
  intro candidate hdone
  have hdoneData := (G.mem_done_iff cfg.result candidate).mp hdone
  refine (G.mem_done_iff
    (cfg.withResult slice hfrontier hlegal).result candidate).mpr ?_
  refine ⟨hdoneData.1, ?_⟩
  by_cases hcandidate : candidate = node
  · subst candidate
    simp [EventGraph.Configuration.withResult,
      EventGraph.Configuration.updateResult]
  · simpa [EventGraph.Configuration.withResult,
      EventGraph.Configuration.updateResult, hcandidate] using hdoneData.2

private theorem eventGraph_withResult_done_card_succ_le
    {G : EventGraph P L} (cfg : G.Configuration)
    {node : G.Node} {slice : G.WriteSlice}
    (hfrontier : node ∈ cfg.frontier)
    (hlegal : G.sliceLegal node slice) :
    cfg.done.card + 1 ≤
      (cfg.withResult slice hfrontier hlegal).done.card := by
  classical
  have hsubset :
      insert node cfg.done ⊆
        (cfg.withResult slice hfrontier hlegal).done := by
    intro candidate hcandidate
    rcases Finset.mem_insert.mp hcandidate with hnode | hdone
    · subst candidate
      refine (G.mem_done_iff
        (cfg.withResult slice hfrontier hlegal).result node).mpr ?_
      exact ⟨cfg.mem_nodes_of_mem_frontier hfrontier, by simp
        [EventGraph.Configuration.withResult,
          EventGraph.Configuration.updateResult]⟩
    · exact eventGraph_withResult_done_subset cfg hfrontier hlegal hdone
  have hnotDone : node ∉ cfg.done := by
    intro hdone
    have hdoneSome := (G.mem_done_iff cfg.result node).mp hdone |>.2
    have hnone := cfg.not_done_of_mem_frontier hfrontier
    cases hresult : cfg.result node <;> simp [hresult] at hdoneSome hnone
  have hcard := Finset.card_le_card hsubset
  simpa [Finset.card_insert_of_notMem hnotDone] using hcard

private theorem eventGraph_roundStepNode_done_subset
    {G : EventGraph P L}
    (joint : GameTheory.JointAction (EventGraph.PlayerRoundAction G))
    (node : G.Node)
    {cfg dst : G.Configuration}
    (hsupp :
      dst ∈ (EventGraph.roundStepNode G joint node cfg).support) :
    cfg.done ⊆ dst.done := by
  classical
  unfold EventGraph.roundStepNode at hsupp
  cases hactor : (G.sem node).actor with
  | some who =>
      cases hmove : joint who with
      | none =>
          have hdst : dst = cfg := by
            simpa [hactor, hmove] using hsupp
          subst dst
          intro candidate hdone
          exact hdone
      | some action =>
          by_cases havailable :
              ({ node := node, slice := action.slice node } :
                EventGraph.PlayerAction G who) ∈
                EventGraph.available G cfg who
          · have hdst :
                dst =
                  cfg.withResult (action.slice node)
                    havailable.1 havailable.2.2.1 := by
              simpa [EventGraph.roundStepNode, EventGraph.stepPlay,
                hactor, hmove, havailable] using hsupp
            subst dst
            exact eventGraph_withResult_done_subset cfg
              havailable.1 havailable.2.2.1
          · have hdst : dst = cfg := by
              simpa [EventGraph.roundStepNode, EventGraph.stepPlay,
                hactor, hmove, havailable] using hsupp
            subst dst
            intro candidate hdone
            exact hdone
  | none =>
      by_cases havailable :
          (EventGraph.InternalEvent.node node : EventGraph.InternalEvent G) ∈
            EventGraph.availableInternal G cfg
      · have hsuppBind :
            dst ∈
              ((G.internalKernel node cfg.result).bind fun slice =>
                if hlegal : G.sliceLegal node slice then
                  PMF.pure (cfg.withResult slice
                    (by simpa [EventGraph.availableInternal, hactor] using havailable)
                    hlegal)
                else
                  PMF.pure cfg).support := by
          simpa [EventGraph.roundStepNode, EventGraph.stepInternal,
            hactor, havailable] using hsupp
        rw [PMF.mem_support_bind_iff] at hsuppBind
        rcases hsuppBind with ⟨slice, _hslice, hdst⟩
        split at hdst
        · rename_i hlegal
          have hdstEq :
              dst =
                cfg.withResult slice
                  (by simpa [EventGraph.availableInternal, hactor] using havailable)
                  hlegal := by
            simpa using hdst
          subst dst
          exact eventGraph_withResult_done_subset cfg
            (by simpa [EventGraph.availableInternal, hactor] using havailable)
            hlegal
        · have hdstEq : dst = cfg := by
            simpa using hdst
          subst dst
          intro candidate hdone
          exact hdone
      · have hdst : dst = cfg := by
          simpa [EventGraph.roundStepNode, EventGraph.stepInternal,
            hactor, havailable] using hsupp
        subst dst
        intro candidate hdone
        exact hdone

private theorem eventGraph_internalKernel_sliceLegal_of_mem_support
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {node : ProgramNode g.prog}
    (hfrontier : node ∈ cfg.frontier)
    (hactor : ((programEventGraph g).sem node).actor = none)
    {slice : ProgramField.WriteSlice g.prog}
    (hsupp :
      slice ∈
        ((programEventGraph g).internalKernel node cfg.result).support) :
    (programEventGraph g).sliceLegal node slice := by
  classical
  change
    slice ∈
      (ProgramNode.internalKernel g.env g.obligations node cfg.result).support at hsupp
  unfold ProgramNode.internalKernel at hsupp
  change (ProgramNode.sem g.obligations node).actor = none at hactor
  change ProgramNode.sliceLegal g.obligations node slice
  cases hsem : ProgramNode.sem g.obligations node with
  | assign target expr =>
      rw [hsem] at hsupp
      have havailable :
          ∀ read, read ∈ expr.reads →
            (ProgramField.value? g.env cfg.result read).isSome := by
        intro read hread
        exact programReadsAvailableAtFrontier_of_wfProgram g cfg hfrontier read
          (by simpa [EventGraph.NodeSem.reads, hsem] using hread)
      change
        slice ∈
          (if available :
              ∀ read, read ∈ expr.reads →
                (ProgramField.value? g.env cfg.result read).isSome then
            PMF.pure
              (ProgramField.singleSlice target
                (.clear
                  (expr.eval
                    (ProgramField.readEnvOfResult g.env cfg.result
                      expr.reads available))))
          else
            PMF.pure (ProgramField.emptySlice g.prog)).support at hsupp
      rw [dif_pos havailable] at hsupp
      have hslice :
          slice =
            ProgramField.singleSlice target
              (.clear
                (expr.eval
                  (ProgramField.readEnvOfResult g.env cfg.result
                    expr.reads havailable))) := by
        simpa using hsupp
      subst slice
      rw [ProgramNode.sliceLegal, hsem]
      exact ⟨_, rfl⟩
  | sample target dist =>
      rw [hsem] at hsupp
      have havailable :
          ∀ read, read ∈ dist.reads →
            (ProgramField.value? g.env cfg.result read).isSome := by
        intro read hread
        exact programReadsAvailableAtFrontier_of_wfProgram g cfg hfrontier read
          (by simpa [EventGraph.NodeSem.reads, hsem] using hread)
      change
        slice ∈
          (if available :
              ∀ read, read ∈ dist.reads →
                (ProgramField.value? g.env cfg.result read).isSome then
            PMF.map
              (fun value => ProgramField.singleSlice target (.clear value))
              (dist.eval
                (ProgramField.readEnvOfResult g.env cfg.result
                  dist.reads available))
          else
            PMF.pure (ProgramField.emptySlice g.prog)).support at hsupp
      rw [dif_pos havailable] at hsupp
      rcases (PMF.mem_support_map_iff _ _ _).mp hsupp with
        ⟨value, _hvalue, hslice⟩
      rw [← hslice]
      rw [ProgramNode.sliceLegal, hsem]
      exact ⟨value, rfl⟩
  | commit owner target guard =>
      simp [EventGraph.NodeSem.actor, hsem] at hactor
  | reveal source target hty =>
      rw [hsem] at hsupp
      have havailable :
          ∀ read, read ∈ ({source} : Finset (ProgramField g.prog)) →
            (ProgramField.value? g.env cfg.result read).isSome := by
        intro read hread
        exact programReadsAvailableAtFrontier_of_wfProgram g cfg hfrontier read
          (by simpa [EventGraph.NodeSem.reads, hsem] using hread)
      change
        slice ∈
          (if available :
              ∀ read, read ∈ ({source} : Finset (ProgramField g.prog)) →
                (ProgramField.value? g.env cfg.result read).isSome then
            (let ρ :=
              ProgramField.readEnvOfResult g.env cfg.result
                ({source} : Finset (ProgramField g.prog)) available
            PMF.pure
              (ProgramField.singleSlice target
                (.clear (cast (by rw [hty])
                  (ρ.value source (by simp))))))
          else
            PMF.pure (ProgramField.emptySlice g.prog)).support at hsupp
      rw [dif_pos havailable] at hsupp
      let ρ :=
        ProgramField.readEnvOfResult g.env cfg.result
          ({source} : Finset (ProgramField g.prog)) havailable
      have hslice :
          slice =
            ProgramField.singleSlice target
              (.clear (cast (by rw [hty]) (ρ.value source (by simp)))) := by
        simpa using hsupp
      subst slice
      rw [ProgramNode.sliceLegal, hsem]
      exact ⟨_, rfl⟩

private theorem eventGraph_roundStepNode_done_card_succ_le_of_legal
    (g : WFProgram P L)
    {cfg dst : (programEventGraph g).Configuration}
    {joint : GameTheory.JointAction
      (EventGraph.PlayerRoundAction (programEventGraph g))}
    (hjoint :
      GameTheory.JointActionLegal
        (EventGraph.PlayerRoundAction (programEventGraph g))
        (EventGraph.roundActive (programEventGraph g))
        EventGraph.Configuration.terminal
        (EventGraph.roundAvailable (programEventGraph g))
        cfg joint)
    {node : ProgramNode g.prog}
    (hfrontier : node ∈ cfg.frontier)
    (hsupp :
      dst ∈
        (EventGraph.roundStepNode (programEventGraph g) joint node cfg).support) :
    cfg.done.card + 1 ≤ dst.done.card := by
  classical
  cases hactor : ((programEventGraph g).sem node).actor with
  | some who =>
      have hactive :
          who ∈ EventGraph.roundActive (programEventGraph g) cfg :=
        (EventGraph.mem_roundActive_iff (programEventGraph g) cfg who).mpr
          ⟨node, hfrontier, hactor⟩
      have hcoord := hjoint.2 who
      cases hmove : joint who with
      | none =>
          have hnot : who ∉ EventGraph.roundActive (programEventGraph g) cfg := by
            simpa [hmove] using hcoord
          exact False.elim (hnot hactive)
      | some action =>
          have hpair :
              who ∈ EventGraph.roundActive (programEventGraph g) cfg ∧
                action ∈ EventGraph.roundAvailable
                  (programEventGraph g) cfg who := by
            simpa [hmove] using hcoord
          have hnodeLegal :
              (programEventGraph g).sliceLegal node (action.slice node) ∧
                (programEventGraph g).actionLegal cfg.result node
                  (action.slice node) :=
            hpair.2 hfrontier hactor
          have havailable :
              ({ node := node, slice := action.slice node } :
                EventGraph.PlayerAction (programEventGraph g) who) ∈
                EventGraph.available (programEventGraph g) cfg who :=
            ⟨hfrontier, hactor, hnodeLegal.1, hnodeLegal.2⟩
          have hdst :
              dst = cfg.withResult (action.slice node)
                hfrontier hnodeLegal.1 := by
            simpa [EventGraph.roundStepNode, EventGraph.stepPlay,
              hactor, hmove, havailable] using hsupp
          subst dst
          exact eventGraph_withResult_done_card_succ_le cfg
            hfrontier hnodeLegal.1
  | none =>
      have havailable :
          (EventGraph.InternalEvent.node node :
            EventGraph.InternalEvent (programEventGraph g)) ∈
            EventGraph.availableInternal (programEventGraph g) cfg := by
        exact ⟨hfrontier, hactor⟩
      let hfrontier' : node ∈ cfg.frontier := hfrontier
      have hsuppBind :
          dst ∈
            (((programEventGraph g).internalKernel node cfg.result).bind
              fun slice =>
                if hlegal : (programEventGraph g).sliceLegal node slice then
                  PMF.pure (cfg.withResult slice hfrontier' hlegal)
                else
                  PMF.pure cfg).support := by
        simpa [EventGraph.roundStepNode, EventGraph.stepInternal,
          hactor, havailable, hfrontier'] using hsupp
      rw [PMF.mem_support_bind_iff] at hsuppBind
      rcases hsuppBind with ⟨slice, hslice, hdstSupport⟩
      have hlegal :
          (programEventGraph g).sliceLegal node slice :=
        eventGraph_internalKernel_sliceLegal_of_mem_support g
          hfrontier hactor hslice
      rw [dif_pos hlegal] at hdstSupport
      have hdst : dst = cfg.withResult slice hfrontier' hlegal := by
        simpa using hdstSupport
      subst dst
      exact eventGraph_withResult_done_card_succ_le cfg hfrontier' hlegal

private theorem eventGraph_roundTransition_go_done_card_lower_bound
    {G : EventGraph P L}
    (joint : GameTheory.JointAction (EventGraph.PlayerRoundAction G))
    (nodes : List G.Node)
    {acc : PMF G.Configuration} {lower : Nat}
    (hacc :
      ∀ cfg : G.Configuration, cfg ∈ acc.support → lower ≤ cfg.done.card)
    {dst : G.Configuration}
    (hsupp :
      dst ∈
        (nodes.foldl
          (fun acc node =>
            acc.bind fun state => EventGraph.roundStepNode G joint node state)
          acc).support) :
    lower ≤ dst.done.card := by
  induction nodes generalizing acc with
  | nil =>
      simpa using hacc dst hsupp
  | cons node nodes ih =>
      apply ih
      · intro mid hmid
        rw [PMF.mem_support_bind_iff] at hmid
        rcases hmid with ⟨src : G.Configuration, hsrc, hstep⟩
        have hsrcLower : lower ≤ src.done.card := hacc src hsrc
        have hsubset : src.done ⊆ mid.done :=
          eventGraph_roundStepNode_done_subset joint node hstep
        exact Nat.le_trans hsrcLower (Finset.card_le_card hsubset)
      · simpa [List.foldl_cons] using hsupp

private theorem eventGraph_roundTransition_done_card_succ_le_of_legal
    (g : WFProgram P L)
    {cfg dst : (programEventGraph g).Configuration}
    {joint : GameTheory.JointAction
      (EventGraph.PlayerRoundAction (programEventGraph g))}
    (hjoint :
      GameTheory.JointActionLegal
        (EventGraph.PlayerRoundAction (programEventGraph g))
        (EventGraph.roundActive (programEventGraph g))
        EventGraph.Configuration.terminal
        (EventGraph.roundAvailable (programEventGraph g))
        cfg joint)
    (hnotTerminal : ¬ cfg.terminal)
    (hsupp :
      dst ∈
        (EventGraph.roundTransition (programEventGraph g) cfg joint).support) :
    cfg.done.card + 1 ≤ dst.done.card := by
  classical
  rcases cfg.frontier_nonempty_of_not_terminal hnotTerminal with
    ⟨first, hfirstFrontier⟩
  rw [EventGraph.roundTransition] at hsupp
  cases hlist : cfg.frontier.toList with
  | nil =>
      have hfirstList : first ∈ cfg.frontier.toList := by
        simpa using hfirstFrontier
      simp [hlist] at hfirstList
  | cons head rest =>
      have hheadFrontier : head ∈ cfg.frontier := by
        have hheadList : head ∈ cfg.frontier.toList := by
          simp [hlist]
        simpa using hheadList
      have hsuppRest :
          dst ∈
            (rest.foldl
              (fun acc node =>
                acc.bind fun state =>
                  EventGraph.roundStepNode
                    (programEventGraph g) joint node state)
              (EventGraph.roundStepNode
                (programEventGraph g) joint head cfg)).support := by
        simpa [hlist, List.foldl_cons] using hsupp
      exact
        eventGraph_roundTransition_go_done_card_lower_bound
          (G := programEventGraph g) joint rest
          (acc := EventGraph.roundStepNode
            (programEventGraph g) joint head cfg)
          (lower := cfg.done.card + 1)
          (fun mid hmid =>
            eventGraph_roundStepNode_done_card_succ_le_of_legal
              g hjoint hheadFrontier hmid)
          hsuppRest

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
  have hroundMem :
      dst.state ∈
        (EventGraph.roundTransition (programEventGraph g)
          src.state rawAction.1).support := by
    simpa [rawAction, eventGraphFOSGView, eventGraphMachine,
      EventGraph.toFOSGView] using hstateMem
  have hroundLegal :
      GameTheory.JointActionLegal
        (EventGraph.PlayerRoundAction (programEventGraph g))
        (EventGraph.roundActive (programEventGraph g))
        EventGraph.Configuration.terminal
        (EventGraph.roundAvailable (programEventGraph g))
        src.state rawAction.1 := by
    simpa [rawAction, eventGraphFOSGView, eventGraphMachine,
      EventGraph.toFOSGView] using rawAction.2
  exact eventGraph_roundTransition_done_card_succ_le_of_legal
    g hroundLegal hnotGraph hroundMem

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

/-- Primitive machine event blocks extracted from a bounded event-graph FOSG
history. Each block is one frontier round of the public FOSG view. -/
noncomputable def eventGraphFOSGHistoryEventBlocks
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    List (List (eventGraphMachine g).Event) :=
  EventGraph.boundedFOSGHistoryEventBlocks
    (programEventGraph g) (eventGraphMachineInterface g)
    (programEventGraph_hasStableFrontierRounds g) horizon h

/-- Primitive machine events represented by one event-graph FOSG frontier
round. -/
noncomputable def eventGraphRoundPrimitiveEvents
    (g : WFProgram P L)
    (cfg : (eventGraphMachine g).State)
    (joint : GameTheory.JointAction (eventGraphFOSGView g).Act) :
    List (eventGraphMachine g).Event := by
  simpa [eventGraphMachine, eventGraphFOSGView] using
    (EventGraph.roundPrimitiveEvents (programEventGraph g)
      (eventGraphMachineInterface g) cfg joint)

/-- Every bounded event-graph FOSG history is backed by a primitive machine
blocked run whose support contains the same checkpoint state. -/
theorem eventGraphFOSGHistory_state_mem_runEventBlocksFrom_support
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    h.lastState.state ∈
      ((eventGraphMachine g).runEventBlocksFrom
        (eventGraphFOSGHistoryEventBlocks g horizon h)
        (eventGraphMachine g).init).support := by
  simpa [eventGraphFOSGHistoryEventBlocks, eventGraphMachine,
    eventGraphFOSGView] using
    (EventGraph.boundedFOSGHistory_state_mem_runEventBlocksFrom_support
      (programEventGraph g) (eventGraphMachineInterface g)
      (programEventGraph_hasStableFrontierRounds g) horizon h)

/-- One bounded event-graph FOSG transition, projected to the history's
extracted event-block prefix and successor checkpoint state, is exactly the
corresponding primitive machine blocked run. -/
theorem eventGraphFOSG_transition_map_eventBlocks_state_eq_runEventBlocksFrom
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History))
    (action :
      (((eventGraphFOSGView g).toBoundedFOSG horizon).LegalAction
        h.lastState)) :
    PMF.map
        (fun dst =>
          (eventGraphFOSGHistoryEventBlocks g horizon h ++
              [eventGraphRoundPrimitiveEvents g h.lastState.state action.1],
            dst.state))
        (((eventGraphFOSGView g).toBoundedFOSG horizon).transition
          h.lastState action) =
      PMF.map
        (fun next =>
          (eventGraphFOSGHistoryEventBlocks g horizon h ++
              [eventGraphRoundPrimitiveEvents g h.lastState.state action.1],
            next))
        ((eventGraphMachine g).runEventBlocksFrom
          [eventGraphRoundPrimitiveEvents g h.lastState.state action.1]
          h.lastState.state) := by
  simpa [eventGraphFOSGHistoryEventBlocks, eventGraphMachine,
    eventGraphFOSGView, eventGraphRoundPrimitiveEvents] using
    (EventGraph.boundedFOSG_transition_map_eventBlocks_state_eq_runEventBlocksFrom
      (programEventGraph g) (eventGraphMachineInterface g)
      (programEventGraph_hasStableFrontierRounds g) horizon h action)

/-- Continuation form of one event-graph FOSG transition: binding over the
bounded FOSG transition is the same as binding over the primitive blocked
machine run and reattaching the bounded presentation depth. -/
theorem eventGraphFOSG_transition_bind_eq_runEventBlocksFrom_bind
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History))
    (action :
      (((eventGraphFOSGView g).toBoundedFOSG horizon).LegalAction
        h.lastState))
    {α : Type}
    (K : (eventGraphMachine g).BoundedState horizon → PMF α) :
    ((((eventGraphFOSGView g).toBoundedFOSG horizon).transition
          h.lastState action).bind K) =
      ((eventGraphMachine g).runEventBlocksFrom
          [eventGraphRoundPrimitiveEvents g h.lastState.state action.1]
          h.lastState.state).bind
        (fun next =>
          K (h.lastState.succ
            (Nat.lt_of_not_ge
              (fun hle => action.2.1 (Or.inr hle)))
            next)) := by
  simpa [eventGraphMachine, eventGraphFOSGView,
    eventGraphRoundPrimitiveEvents] using
    (EventGraph.boundedFOSG_transition_bind_eq_runEventBlocksFrom_bind
      (programEventGraph g) (eventGraphMachineInterface g)
      (programEventGraph_hasStableFrontierRounds g) horizon h action K)

/-- One-step form matching `FOSG.History.runDistFrom` for event graphs:
extend the FOSG history by the sampled bounded destination, then project to
the extracted primitive event blocks and checkpoint state. -/
theorem eventGraphFOSG_transition_map_extend_eventBlocks_state_eq_runEventBlocksFrom
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History))
    (action :
      (((eventGraphFOSGView g).toBoundedFOSG horizon).LegalAction
        h.lastState)) :
    PMF.map
        (fun dst =>
          let h' := h.extendByOutcome action dst
          (eventGraphFOSGHistoryEventBlocks g horizon h',
            h'.lastState.state))
        (((eventGraphFOSGView g).toBoundedFOSG horizon).transition
          h.lastState action) =
      PMF.map
        (fun next =>
          (eventGraphFOSGHistoryEventBlocks g horizon h ++
              [eventGraphRoundPrimitiveEvents g h.lastState.state action.1],
            next))
        ((eventGraphMachine g).runEventBlocksFrom
          [eventGraphRoundPrimitiveEvents g h.lastState.state action.1]
          h.lastState.state) := by
  simpa [eventGraphFOSGHistoryEventBlocks, eventGraphMachine,
    eventGraphFOSGView, eventGraphRoundPrimitiveEvents] using
    (EventGraph.boundedFOSG_transition_map_extend_eventBlocks_state_eq_runEventBlocksFrom
      (programEventGraph g) (eventGraphMachineInterface g)
      (programEventGraph_hasStableFrontierRounds g) horizon h action)

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
    rcases haction hfrontierLeft hactor with ⟨hslice, hlegal⟩
    exact ⟨hslice,
      eventGraph_actionLegal_of_observe_eq g who hfrontier
        hactor hpriv hlegal⟩
  · intro haction node hfrontier hactor
    have hfrontierRight : node ∈ right.frontier := by
      simpa [hfrontierEq] using hfrontier
    rcases haction hfrontierRight hactor with ⟨hslice, hlegal⟩
    exact ⟨hslice,
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
    EventGraph.ResultAssignment, EventGraph.WriteSlice]
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
    EventGraph.WriteSlice]
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
    (g : WFProgram P L) :
    Fintype (eventGraphMachine g).Internal := by
  classical
  letI : Fintype (ProgramNode g.prog) :=
    ProgramNode.instFintype g.prog
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

/-- History-dependent blocked primitive trace distribution induced by a
bounded event-graph FOSG behavioral profile. -/
noncomputable def eventGraphFOSGBlockTraceDistFrom
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
              (programEventGraph_hasStableFrontierRounds g)).Act
                player)) := by
    intro player
    simpa [eventGraphFOSGView] using
      (eventGraphFOSGView.instFintypeOptionAct g player)
  simpa [eventGraphMachine, eventGraphFOSGView] using
    (EventGraph.boundedFOSGBlockTraceDistFrom
      (programEventGraph g) (eventGraphMachineInterface g)
      (programEventGraph_hasStableFrontierRounds g) horizon σ)

/-- Bounded event-graph FOSG execution, projected to extracted primitive
event blocks and checkpoint state, equals the history-dependent blocked
machine trace distribution induced by the same behavioral profile. -/
theorem eventGraphFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (σ :
      GameTheory.FOSG.LegalBehavioralProfile
        ((eventGraphFOSGView g).toBoundedFOSG horizon))
    (n : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    PMF.map
        (fun h' =>
          (eventGraphFOSGHistoryEventBlocks g horizon h',
            h'.lastState.state))
        (GameTheory.FOSG.History.runDistFrom
          ((eventGraphFOSGView g).toBoundedFOSG horizon) σ n h) =
      eventGraphFOSGBlockTraceDistFrom g horizon σ n h := by
  letI :
      ∀ player,
        Fintype
          (Option
            (((programEventGraph g).toFOSGView
              (eventGraphMachineInterface g)
              (programEventGraph_hasStableFrontierRounds g)).Act
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
          (programEventGraph_hasStableFrontierRounds g)).toBoundedFOSG
            horizon).terminal) :=
    Classical.decPred _
  simpa [eventGraphFOSGHistoryEventBlocks, eventGraphMachine,
    eventGraphFOSGView, eventGraphFOSGBlockTraceDistFrom] using
      (EventGraph.boundedFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
        (programEventGraph g) (eventGraphMachineInterface g)
        (programEventGraph_hasStableFrontierRounds g) horizon σ n h)

/-- Initial history of the bounded event-graph FOSG presentation. -/
noncomputable def eventGraphInitialHistory
    (g : WFProgram P L) (horizon : Nat) :
    (((eventGraphFOSGView g).toBoundedFOSG horizon).History) :=
  GameTheory.FOSG.History.nil
    ((eventGraphFOSGView g).toBoundedFOSG horizon)

/-- Project a bounded event-graph FOSG history to primitive event blocks and
the checkpoint machine state. -/
noncomputable def eventGraphHistoryTrace
    (g : WFProgram P L) (horizon : Nat)
    (h : (((eventGraphFOSGView g).toBoundedFOSG horizon).History)) :
    List (List (eventGraphMachine g).Event) × (eventGraphMachine g).State :=
  (eventGraphFOSGHistoryEventBlocks g horizon h, h.lastState.state)

/-- Outcome extracted from a blocked event-graph trace. -/
noncomputable def eventGraphTraceOutcome
    (g : WFProgram P L)
    (trace :
      List (List (eventGraphMachine g).Event) ×
        (eventGraphMachine g).State) :
    (eventGraphMachine g).Outcome :=
  (eventGraphMachine g).outcome trace.2

/-- Bounded behavioral outcome kernel of the event-graph FOSG view, computed
as the machine outcome projection of the induced blocked primitive trace
distribution. -/
theorem eventGraphFOSG_boundedOutcomeFromBehavioral_eq_blockTraceDist
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (β : (eventGraphFOSGView g).BoundedBehavioralProfile horizon)
    (steps : Nat) :
    (eventGraphFOSGView g).boundedOutcomeFromBehavioral
        horizon β steps =
      PMF.map
        (eventGraphTraceOutcome g)
        (eventGraphFOSGBlockTraceDistFrom g horizon β.extend steps
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
        (eventGraphFOSGBlockTraceDistFrom g horizon β.extend steps
          (eventGraphInitialHistory g horizon)) := by
          have htrace :
              PMF.map (eventGraphHistoryTrace g horizon) run =
                eventGraphFOSGBlockTraceDistFrom g horizon β.extend steps
                  (eventGraphInitialHistory g horizon) := by
            simpa [eventGraphHistoryTrace, run] using
              (eventGraphFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
                (g := g) (horizon := horizon) (σ := β.extend)
                (n := steps)
                (h := eventGraphInitialHistory g horizon))
          rw [htrace]

/-- Bounded pure outcome kernel of the event-graph FOSG view, computed as
the machine outcome projection of the blocked primitive trace distribution
induced by the pure profile's behavioral embedding. -/
theorem eventGraphFOSG_boundedOutcomeFromPure_eq_blockTraceDist
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (horizon : Nat)
    (π : (eventGraphFOSGView g).BoundedPureProfile horizon)
    (steps : Nat) :
    (eventGraphFOSGView g).boundedOutcomeFromPure
        horizon π steps =
      PMF.map
        (eventGraphTraceOutcome g)
        (eventGraphFOSGBlockTraceDistFrom g horizon
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
        (eventGraphFOSGBlockTraceDistFrom g horizon σ steps
          (eventGraphInitialHistory g horizon)) := by
          have htrace :
              PMF.map (eventGraphHistoryTrace g horizon) run =
                eventGraphFOSGBlockTraceDistFrom g horizon σ steps
                  (eventGraphInitialHistory g horizon) := by
            simpa [eventGraphHistoryTrace, run] using
              (eventGraphFOSG_runDistFrom_map_eventBlocks_state_eq_blockTraceDistFrom
                (g := g) (horizon := horizon) (σ := σ)
                (n := steps)
                (h := eventGraphInitialHistory g horizon))
          rw [htrace]


end Vegas
