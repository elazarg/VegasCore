import Vegas.Core.ToEventGraph.Checkpoint
import Vegas.EventGraph.RoundView
import Vegas.Machine.KernelGame

/-!
# EventGraph frontier round views

This file connects compiled event graphs to the native `Machine.RoundView`
carrier.  The strategic surface is canonical at the local-action level:
active players are those with ready commit nodes once currently-ready internal
graph work has closed, and player actions assign values to their ready commit
frontier.

The stochastic transition from a legal frontier action profile to the next
checkpoint is intentionally supplied as explicit semantics, but it is tied to a
checkpoint presentation: every supported transition must be an allowed
checkpoint transition.  The default primitive-downset semantics executes
chosen commits together with operational/chance closure and records a primitive
event-batch certificate for each supported checkpoint transition.
-/

namespace Vegas

namespace ToEventGraph

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- EventGraph-native primitive-machine spec produced by compilation. -/
noncomputable def primitiveMachineSpec
    (compiled : CompiledProgram P L) :
    EventGraph.ToMachine.GraphMachineSpec compiled.graph where
  graphWF := compiled.graphWF
  payoffs := compiled.payoffs
  payoffsWF := compiled.payoffsWF

/-- The primitive machine associated with a compiled event graph. -/
noncomputable abbrev PrimitiveMachine
    (compiled : CompiledProgram P L) : Machine P :=
  EventGraph.PrimitiveMachineOf (primitiveMachineSpec compiled)

/-- Canonical player action alphabet for graph-frontier rounds. -/
abbrev FrontierAct (compiled : CompiledProgram P L) (who : P) : Type :=
  EventGraph.FrontierAct compiled.graph who

/-- Active players at a checkpoint: ready commit owners after currently-ready
internal graph work has closed. -/
noncomputable def frontierActive (compiled : CompiledProgram P L) :
    (PrimitiveMachine compiled).State → Finset P :=
  EventGraph.frontierActive compiled.graph

/-- Locally available frontier actions for one player. -/
noncomputable def frontierAvailableActions
    (compiled : CompiledProgram P L) :
    (PrimitiveMachine compiled).State → (who : P) →
      Set (FrontierAct compiled who) :=
  EventGraph.frontierAvailableActions compiled.graph

theorem frontierCommitAvailable_of_legal_value
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    {joint : JointAction (FrontierAct compiled)}
    (hlegal :
      JointActionLegal (FrontierAct compiled)
        (frontierActive compiled)
        (PrimitiveMachine compiled).terminal
        (frontierAvailableActions compiled) state joint)
    {who : P} {frontierAction : FrontierAct compiled who}
    {node : Fin compiled.graph.nodeCount}
    {value : L.Val (compiled.graph.nodeRow node).ty}
    (haction : joint who = some frontierAction)
    (hvalue : frontierAction.value? node = some value) :
    EventGraph.CommitAvailable compiled.graph state.1 who
      { node := node, value := compiled.graph.nodeTypedValue node value } := by
  exact
    EventGraph.frontierCommitAvailable_of_legal_value
      compiled.graph hlegal haction hvalue

/-- A primitive machine event is compatible with a joint frontier action if
player events are exactly values selected by the corresponding player's
frontier action. Internal events are operational/chance work and are not
strategic choices. -/
abbrev FrontierEventSelected (compiled : CompiledProgram P L)
    (action : JointAction (FrontierAct compiled)) :
    (PrimitiveMachine compiled).Event → Prop :=
  EventGraph.FrontierEventSelected (primitiveMachineSpec compiled) action

/-- A primitive event batch realizes a joint frontier action when every
strategic primitive event in the batch is selected by the joint action, and
every selected commit value appears as a primitive play event. Availability and
ordering are proved separately by `AvailableRunFrom`. -/
abbrev FrontierBatchRealizesAction (compiled : CompiledProgram P L)
    (action : JointAction (FrontierAct compiled))
    (batch : List (PrimitiveMachine compiled).Event) : Prop :=
  EventGraph.FrontierBatchRealizesAction
    (primitiveMachineSpec compiled) action batch

omit [Fintype P] in
/-- Primitive commit events selected by a joint frontier action, enumerated
over graph nodes. This is the canonical strategic prefix shape: each graph
node is visited at most once, so selected commit serialization follows graph
identity rather than player-order bookkeeping. -/
noncomputable abbrev selectedCommitEventsFromNodes
    (compiled : CompiledProgram P L)
    (nodes : List (Fin compiled.graph.nodeCount))
    (action : JointAction (FrontierAct compiled)) :
    List (PrimitiveMachine compiled).Event :=
  EventGraph.selectedCommitEventsFromNodes
    (primitiveMachineSpec compiled) nodes action

omit [Fintype P] in
/-- A selected strategic commit event at one graph node. -/
abbrev SelectedCommitAtNode
    (compiled : CompiledProgram P L)
    (action : JointAction (FrontierAct compiled))
    (node : Fin compiled.graph.nodeCount)
    (event : (PrimitiveMachine compiled).Event) : Prop :=
  EventGraph.SelectedCommitAtNode
    (primitiveMachineSpec compiled) action node event

omit [Fintype P] in
theorem mem_selectedCommitEventsFromNodes_iff
    (compiled : CompiledProgram P L)
    (nodes : List (Fin compiled.graph.nodeCount))
    (action : JointAction (FrontierAct compiled))
    {event : (PrimitiveMachine compiled).Event} :
    event ∈ selectedCommitEventsFromNodes compiled nodes action ↔
      ∃ node, node ∈ nodes ∧
        SelectedCommitAtNode compiled action node event := by
  exact EventGraph.mem_selectedCommitEventsFromNodes_iff
    (primitiveMachineSpec compiled) nodes action

theorem selectedCommitAtNode_available_of_legal
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    {action : JointAction (FrontierAct compiled)}
    (hlegal :
      JointActionLegal (FrontierAct compiled)
        (frontierActive compiled)
        (PrimitiveMachine compiled).terminal
        (frontierAvailableActions compiled) state action)
    {node : Fin compiled.graph.nodeCount}
    {event : (PrimitiveMachine compiled).Event}
    (hselected : SelectedCommitAtNode compiled action node event) :
    (PrimitiveMachine compiled).EventAvailable state event := by
  exact
    EventGraph.selectedCommitAtNode_available_of_legal
      (primitiveMachineSpec compiled) hlegal hselected

omit [Fintype P] in
theorem selectedCommitAtNode_step_support
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    {action : JointAction (FrontierAct compiled)}
    {node : Fin compiled.graph.nodeCount}
    {event : (PrimitiveMachine compiled).Event}
    (hselected : SelectedCommitAtNode compiled action node event)
    (havailable :
      (PrimitiveMachine compiled).EventAvailable state event) :
    ∃ written : EventGraph.TypedValue L,
      ∃ next : (PrimitiveMachine compiled).State,
        next ∈ ((PrimitiveMachine compiled).step event state).support ∧
        next.1 = state.1.completeNode node written := by
  rcases hselected with
    ⟨who, _guard, _frontierAction, value,
      _hnode, _haction, _hvalue, hevent⟩
  rw [hevent] at havailable
  rcases
      EventGraph.ToMachine.primitiveMachine_step_play_available_support
        (primitiveMachineSpec compiled) havailable with
    ⟨written, next, hnext, hcfg⟩
  exact ⟨written, next, by simpa [hevent] using hnext, hcfg⟩

omit [Fintype P] in
theorem selectedCommitAtNode_available_persist_after_other_write
    (compiled : CompiledProgram P L)
    {action : JointAction (FrontierAct compiled)}
    {current next : (PrimitiveMachine compiled).State}
    {node₁ node₂ : Fin compiled.graph.nodeCount}
    {event₁ event₂ : (PrimitiveMachine compiled).Event}
    {written : EventGraph.TypedValue L}
    (hselected₁ : SelectedCommitAtNode compiled action node₁ event₁)
    (hselected₂ : SelectedCommitAtNode compiled action node₂ event₂)
    (havailable₁ :
      (PrimitiveMachine compiled).EventAvailable current event₁)
    (havailable₂ :
      (PrimitiveMachine compiled).EventAvailable current event₂)
    (hne : node₂ ≠ node₁)
    (hnext : next.1 = current.1.completeNode node₁ written) :
    (PrimitiveMachine compiled).EventAvailable next event₂ := by
  rcases hselected₁ with
    ⟨who₁, _guard₁, _frontierAction₁, value₁,
      _hnode₁, _haction₁, _hvalue₁, hevent₁⟩
  rcases hselected₂ with
    ⟨who₂, _guard₂, _frontierAction₂, value₂,
      _hnode₂, _haction₂, _hvalue₂, hevent₂⟩
  rw [hevent₁] at havailable₁
  rw [hevent₂] at havailable₂ ⊢
  change
    EventGraph.CommitAvailable compiled.graph next.1 who₂
      { node := node₂,
        value := compiled.graph.nodeTypedValue node₂ value₂ }
  rw [hnext]
  exact
    havailable₂.persist_after_other_commit_write
      compiled.graphWF havailable₁ written hne

omit [Fintype P] in
theorem selectedCommitEventsFromNodes_availableRunFrom_of_available
    (compiled : CompiledProgram P L)
    {action : JointAction (FrontierAct compiled)} :
    ∀ {state : (PrimitiveMachine compiled).State}
      {nodes : List (Fin compiled.graph.nodeCount)},
      nodes.Nodup →
      (∀ {node event},
        node ∈ nodes →
          SelectedCommitAtNode compiled action node event →
            (PrimitiveMachine compiled).EventAvailable state event) →
      ∃ dst,
        (PrimitiveMachine compiled).AvailableRunFrom state
          (selectedCommitEventsFromNodes compiled nodes action) dst
  | state, [], _hnodup, _havailable => ⟨state, .nil state⟩
  | state, node :: tail, hnodup, havailable => by
      classical
      have hnodupParts := List.nodup_cons.mp hnodup
      have hnodeNotTail : node ∉ tail := hnodupParts.1
      have htailNodup : tail.Nodup := hnodupParts.2
      let tailAvailable :
          ∀ {tailNode event},
            tailNode ∈ tail →
              SelectedCommitAtNode compiled action tailNode event →
                (PrimitiveMachine compiled).EventAvailable state event := by
        intro tailNode event hmem hselected
        exact havailable (by simp [hmem]) hselected
      cases hnode : (compiled.graph.nodeRow node).sem with
      | sample dist =>
          rcases
              selectedCommitEventsFromNodes_availableRunFrom_of_available
                compiled htailNodup tailAvailable with
            ⟨dst, hrun⟩
          refine ⟨dst, ?_⟩
          simpa [selectedCommitEventsFromNodes,
            EventGraph.selectedCommitEventsFromNodes, hnode] using hrun
      | reveal source =>
          rcases
              selectedCommitEventsFromNodes_availableRunFrom_of_available
                compiled htailNodup tailAvailable with
            ⟨dst, hrun⟩
          refine ⟨dst, ?_⟩
          simpa [selectedCommitEventsFromNodes,
            EventGraph.selectedCommitEventsFromNodes, hnode] using hrun
      | commit who guard =>
              cases haction : action who with
              | none =>
                  rcases
                      selectedCommitEventsFromNodes_availableRunFrom_of_available
                        compiled htailNodup tailAvailable with
                    ⟨dst, hrun⟩
                  refine ⟨dst, ?_⟩
                  simpa [selectedCommitEventsFromNodes,
                    EventGraph.selectedCommitEventsFromNodes, hnode, haction] using
                    hrun
              | some frontierAction =>
                  cases hvalue : frontierAction.value? node with
                  | none =>
                      rcases
                          selectedCommitEventsFromNodes_availableRunFrom_of_available
                            compiled htailNodup tailAvailable with
                        ⟨dst, hrun⟩
                      refine ⟨dst, ?_⟩
                      simpa [selectedCommitEventsFromNodes,
                        EventGraph.selectedCommitEventsFromNodes, hnode,
                        haction, hvalue] using hrun
                  | some value =>
                      let event : (PrimitiveMachine compiled).Event :=
                        Machine.Event.play (M := PrimitiveMachine compiled)
                          who
                          ({ node := node, value := compiled.graph.nodeTypedValue node value } :
                            (PrimitiveMachine compiled).Action who)
                      have hselectedHead :
                          SelectedCommitAtNode compiled action node event :=
                        ⟨who, guard, frontierAction, value, hnode, haction,
                          hvalue, rfl⟩
                      have hheadAvailable :
                          (PrimitiveMachine compiled).EventAvailable
                            state event :=
                        havailable (by simp) hselectedHead
                      rcases
                          selectedCommitAtNode_step_support
                            compiled hselectedHead hheadAvailable with
                        ⟨written, next, hnextSupport, hnextCfg⟩
                      let nextAvailable :
                          ∀ {tailNode event₂},
                            tailNode ∈ tail →
                              SelectedCommitAtNode compiled action
                                tailNode event₂ →
                                (PrimitiveMachine compiled).EventAvailable
                                  next event₂ := by
                        intro tailNode event₂ hmem hselectedTail
                        have htailCurrent :
                            (PrimitiveMachine compiled).EventAvailable
                              state event₂ :=
                          havailable (by simp [hmem]) hselectedTail
                        have hne : tailNode ≠ node := by
                          intro heq
                          exact hnodeNotTail (by simpa [heq] using hmem)
                        exact
                          selectedCommitAtNode_available_persist_after_other_write
                            compiled hselectedHead hselectedTail
                            hheadAvailable htailCurrent hne hnextCfg
                      rcases
                          selectedCommitEventsFromNodes_availableRunFrom_of_available
                            compiled htailNodup nextAvailable with
                        ⟨dst, htailRun⟩
                      have hrun :
                          (PrimitiveMachine compiled).AvailableRunFrom state
                            (event ::
                              selectedCommitEventsFromNodes compiled tail
                                action)
                            dst :=
                        .cons hheadAvailable hnextSupport htailRun
                      refine ⟨dst, ?_⟩
                      simpa [selectedCommitEventsFromNodes,
                        EventGraph.selectedCommitEventsFromNodes, hnode,
                        haction, hvalue, event] using hrun

theorem selectedCommitEventsFromNodes_available
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    {action : JointAction (FrontierAct compiled)}
    (hlegal :
      JointActionLegal (FrontierAct compiled)
        (frontierActive compiled)
        (PrimitiveMachine compiled).terminal
        (frontierAvailableActions compiled) state action)
    (nodes : List (Fin compiled.graph.nodeCount))
    {event : (PrimitiveMachine compiled).Event}
    (hmem :
      event ∈ selectedCommitEventsFromNodes compiled nodes action) :
    (PrimitiveMachine compiled).EventAvailable state event := by
  rcases
      (mem_selectedCommitEventsFromNodes_iff
        compiled nodes action).mp hmem with
    ⟨node, _hnode, hselected⟩
  exact selectedCommitAtNode_available_of_legal compiled hlegal hselected

theorem selectedCommitEventsFromNodes_availableRunFrom_exists
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    {action : JointAction (FrontierAct compiled)}
    (hlegal :
      JointActionLegal (FrontierAct compiled)
        (frontierActive compiled)
        (PrimitiveMachine compiled).terminal
        (frontierAvailableActions compiled) state action)
    {nodes : List (Fin compiled.graph.nodeCount)}
    (hnodup : nodes.Nodup) :
    ∃ dst,
      (PrimitiveMachine compiled).AvailableRunFrom state
        (selectedCommitEventsFromNodes compiled nodes action) dst :=
  selectedCommitEventsFromNodes_availableRunFrom_of_available
    compiled hnodup
    (fun _hmem hselected =>
      selectedCommitAtNode_available_of_legal compiled hlegal hselected)

theorem selectedCommitEventsFromNodes_realizesAction
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    {action : JointAction (FrontierAct compiled)}
    (hlegal :
      JointActionLegal (FrontierAct compiled)
        (frontierActive compiled)
        (PrimitiveMachine compiled).terminal
        (frontierAvailableActions compiled) state action)
    (nodes : List (Fin compiled.graph.nodeCount))
    (hnodes : ∀ node, node ∈ nodes) :
    FrontierBatchRealizesAction compiled action
      (selectedCommitEventsFromNodes compiled nodes action) := by
  classical
  constructor
  · intro event hmem
    rcases
        (mem_selectedCommitEventsFromNodes_iff
          compiled nodes action).mp hmem with
      ⟨_node, _hnode, who, _guard, frontierAction, value,
        _hsem, haction, hvalue, hevent⟩
    rw [hevent]
    exact
      ⟨frontierAction, haction, value, hvalue, rfl⟩
  · intro who frontierAction node value haction hvalue
    have hlocal := hlegal.2 who
    rw [haction] at hlocal
    rcases
        EventGraph.FrontierAction.Available.readyCommitNode_of_value
          hlocal.2 hvalue with
      ⟨row, guard, hrow, hsem, _hready⟩
    have hnode :
        (compiled.graph.nodeRow node).sem =
          EventGraph.NodeSem.commit who guard := by
      have hrowEq : compiled.graph.nodeRow node = row := by
        have hcanonical := compiled.graph.nodes_get?_nodeRow node
        change compiled.graph.nodes[(node : Nat)]? = some row at hrow
        rw [hrow] at hcanonical
        exact (Option.some.inj hcanonical).symm
      rw [hrowEq]
      exact hsem
    unfold selectedCommitEventsFromNodes EventGraph.selectedCommitEventsFromNodes
    rw [List.mem_filterMap]
    refine ⟨node, hnodes node, ?_⟩
    simp [hnode, haction, hvalue]

/-- Canonical primitive commit events selected by a joint frontier action. -/
noncomputable def selectedCommitEvents
    (compiled : CompiledProgram P L)
    (action : JointAction (FrontierAct compiled)) :
    List (PrimitiveMachine compiled).Event :=
  selectedCommitEventsFromNodes compiled compiled.graph.nodeOrder action

theorem selectedCommitEvents_realizesAction
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    (action : JointAction (FrontierAct compiled))
    (hlegal :
      JointActionLegal (FrontierAct compiled)
        (frontierActive compiled)
        (PrimitiveMachine compiled).terminal
        (frontierAvailableActions compiled) state action) :
    FrontierBatchRealizesAction compiled action
      (selectedCommitEvents compiled action) := by
  simpa [selectedCommitEvents] using
    selectedCommitEventsFromNodes_realizesAction
      compiled hlegal compiled.graph.nodeOrder
      (by intro node; simp)

theorem selectedCommitEvents_available
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    {action : JointAction (FrontierAct compiled)}
    (hlegal :
      JointActionLegal (FrontierAct compiled)
        (frontierActive compiled)
        (PrimitiveMachine compiled).terminal
        (frontierAvailableActions compiled) state action)
    {event : (PrimitiveMachine compiled).Event}
    (hmem : event ∈ selectedCommitEvents compiled action) :
    (PrimitiveMachine compiled).EventAvailable state event := by
  exact
    selectedCommitEventsFromNodes_available
      compiled hlegal compiled.graph.nodeOrder hmem

theorem selectedCommitEvents_availableRunFrom_exists
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    {action : JointAction (FrontierAct compiled)}
    (hlegal :
      JointActionLegal (FrontierAct compiled)
        (frontierActive compiled)
        (PrimitiveMachine compiled).terminal
        (frontierAvailableActions compiled) state action) :
    ∃ dst,
      (PrimitiveMachine compiled).AvailableRunFrom state
        (selectedCommitEvents compiled action) dst := by
  simpa [selectedCommitEvents] using
    selectedCommitEventsFromNodes_availableRunFrom_exists
      compiled hlegal compiled.graph.nodeOrder_nodup

theorem selectedCommitEvents_ne_nil_of_active
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    {action : JointAction (FrontierAct compiled)}
    (hlegal :
      JointActionLegal (FrontierAct compiled)
        (frontierActive compiled)
        (PrimitiveMachine compiled).terminal
        (frontierAvailableActions compiled) state action)
    (hactive : (frontierActive compiled state).Nonempty) :
    selectedCommitEvents compiled action ≠ [] := by
  classical
  rcases hactive with ⟨who, hwho⟩
  have hwhoActive :
      who ∈ EventGraph.activePlayers compiled.graph state.1 := by
    unfold frontierActive EventGraph.frontierActive at hwho
    by_cases hinternal :
        (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty
    · simp [hinternal] at hwho
    · simpa [hinternal] using hwho
  have hreadyNodes :
      (EventGraph.readyCommitNodes compiled.graph state.1 who).Nonempty := by
    exact (Finset.mem_filter.mp hwhoActive).2
  rcases hreadyNodes with ⟨node, hnodeMem⟩
  have hready :
      EventGraph.ReadyCommitNode compiled.graph state.1 who node :=
    (Finset.mem_filter.mp hnodeMem).2
  have hlocal := hlegal.2 who
  cases haction : action who with
  | none =>
      have hnotActive : who ∉ frontierActive compiled state := by
        simpa [haction] using hlocal
      exact False.elim (hnotActive hwho)
  | some frontierAction =>
      have havailable :
          EventGraph.FrontierAction.Available
            compiled.graph state.1 who frontierAction := by
        have hpair :
            who ∈ frontierActive compiled state ∧
              frontierAction ∈ frontierAvailableActions compiled state who := by
          simpa [haction] using hlocal
        exact hpair.2
      have hnodeAction := havailable node
      rw [dif_pos hready] at hnodeAction
      rcases hnodeAction with ⟨value, hvalue, _hcommit⟩
      have hrealizes :
          FrontierBatchRealizesAction compiled action
            (selectedCommitEvents compiled action) :=
        selectedCommitEvents_realizesAction compiled action hlegal
      let event : (PrimitiveMachine compiled).Event :=
        Machine.Event.play (M := PrimitiveMachine compiled) who
          ({ node := node,
             value := compiled.graph.nodeTypedValue node value } :
            (PrimitiveMachine compiled).Action who)
      have hmem :
          event ∈ selectedCommitEvents compiled action :=
        hrealizes.2 who frontierAction node value haction hvalue
      intro hnil
      rw [hnil] at hmem
      cases hmem

theorem selectedCommitEvents_primitiveDownset_allowed_of_active
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    {action : JointAction (FrontierAct compiled)}
    (hlegal :
      JointActionLegal (FrontierAct compiled)
        (frontierActive compiled)
        (PrimitiveMachine compiled).terminal
        (frontierAvailableActions compiled) state action)
    (hactive : (frontierActive compiled state).Nonempty) :
    ∃ dst,
      (PrimitiveMachine compiled).AvailableRunFrom state
        (selectedCommitEvents compiled action) dst ∧
      (EventGraph.primitiveDownsetCheckpointPolicy compiled.graph).allowed
        state dst := by
  classical
  rcases selectedCommitEvents_availableRunFrom_exists
      compiled hlegal with
    ⟨dst, hrun⟩
  have hne :
      selectedCommitEvents compiled action ≠ [] :=
    selectedCommitEvents_ne_nil_of_active compiled hlegal hactive
  refine ⟨dst, hrun, ?_, ?_⟩
  · exact
      EventGraph.ToMachine.primitiveMachine_availableRunFrom_done_ssubset_of_ne_nil
        (primitiveMachineSpec compiled) hrun hne
  · exact
      EventGraph.ToMachine.checkpointStep_of_availableRunFrom
        (primitiveMachineSpec compiled) hrun

theorem selectedCommitEvent_step_support
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    {action : JointAction (FrontierAct compiled)}
    (hlegal :
      JointActionLegal (FrontierAct compiled)
        (frontierActive compiled)
        (PrimitiveMachine compiled).terminal
        (frontierAvailableActions compiled) state action)
    {event : (PrimitiveMachine compiled).Event}
    (hmem : event ∈ selectedCommitEvents compiled action) :
    ∃ next : (PrimitiveMachine compiled).State,
      next ∈ ((PrimitiveMachine compiled).step event state).support := by
  exact
    EventGraph.ToMachine.primitiveMachine_step_available_support
      (primitiveMachineSpec compiled)
      (selectedCommitEvents_available compiled hlegal hmem)

omit [Fintype P] in
/-- Ready internal primitive events, enumerated over graph nodes. -/
noncomputable abbrev readyInternalEventsFromNodes
    (compiled : CompiledProgram P L)
    (state : (PrimitiveMachine compiled).State)
    (nodes : List (Fin compiled.graph.nodeCount)) :
    List (PrimitiveMachine compiled).Event :=
  EventGraph.readyInternalEventsFromNodes
    (primitiveMachineSpec compiled) state nodes

omit [Fintype P] in
theorem mem_readyInternalEventsFromNodes_iff
    (compiled : CompiledProgram P L)
    (state : (PrimitiveMachine compiled).State)
    (nodes : List (Fin compiled.graph.nodeCount))
    {event : (PrimitiveMachine compiled).Event} :
    event ∈ readyInternalEventsFromNodes compiled state nodes ↔
      ∃ node, node ∈ nodes ∧
        EventGraph.ReadyInternalNode compiled.graph state.1 node ∧
        event =
          Machine.Event.internal (M := PrimitiveMachine compiled)
            ({ node := node } : (PrimitiveMachine compiled).Internal) := by
  exact
    EventGraph.mem_readyInternalEventsFromNodes_iff
      (primitiveMachineSpec compiled) state nodes

omit [Fintype P] in
theorem readyInternalEventsFromNodes_available
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    {nodes : List (Fin compiled.graph.nodeCount)}
    {event : (PrimitiveMachine compiled).Event}
    (hmem : event ∈ readyInternalEventsFromNodes compiled state nodes) :
    (PrimitiveMachine compiled).EventAvailable state event := by
  exact
    EventGraph.readyInternalEventsFromNodes_available
      (primitiveMachineSpec compiled) hmem

/-- Canonical ready-internal primitive events at a compiled checkpoint,
enumerated by graph node id. -/
noncomputable def readyInternalEvents
    (compiled : CompiledProgram P L)
    (state : (PrimitiveMachine compiled).State) :
    List (PrimitiveMachine compiled).Event :=
  readyInternalEventsFromNodes compiled state compiled.graph.nodeOrder

omit [Fintype P] in
theorem readyInternalEvents_available
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    {event : (PrimitiveMachine compiled).Event}
    (hmem : event ∈ readyInternalEvents compiled state) :
    (PrimitiveMachine compiled).EventAvailable state event :=
  readyInternalEventsFromNodes_available compiled hmem

omit [Fintype P] in
theorem readyInternalAtNode_step_support
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    {node : Fin compiled.graph.nodeCount}
    {event : (PrimitiveMachine compiled).Event}
    (hevent :
      event =
        Machine.Event.internal (M := PrimitiveMachine compiled)
          ({ node := node } : (PrimitiveMachine compiled).Internal))
    (havailable :
      (PrimitiveMachine compiled).EventAvailable state event) :
    ∃ written : EventGraph.TypedValue L,
      ∃ next : (PrimitiveMachine compiled).State,
        next ∈ ((PrimitiveMachine compiled).step event state).support ∧
        next.1 = state.1.completeNode node written := by
  rw [hevent] at havailable
  rcases
      EventGraph.ToMachine.primitiveMachine_step_internal_available_support
        (primitiveMachineSpec compiled) havailable with
    ⟨written, next, hnext, hcfg⟩
  exact ⟨written, next, by simpa [hevent] using hnext, hcfg⟩

omit [Fintype P] in
theorem readyInternalAtNode_step_support_completeNode
    (compiled : CompiledProgram P L)
    {state next : (PrimitiveMachine compiled).State}
    {node : Fin compiled.graph.nodeCount}
    {event : (PrimitiveMachine compiled).Event}
    (hevent :
      event =
        Machine.Event.internal (M := PrimitiveMachine compiled)
          ({ node := node } : (PrimitiveMachine compiled).Internal))
    (havailable :
      (PrimitiveMachine compiled).EventAvailable state event)
    (hstep : next ∈ ((PrimitiveMachine compiled).step event state).support) :
    ∃ written : EventGraph.TypedValue L,
      next.1 = state.1.completeNode node written := by
  rw [hevent] at havailable hstep
  exact
    EventGraph.ToMachine.primitiveMachine_step_internal_support_completeNode
      (primitiveMachineSpec compiled) havailable hstep

omit [Fintype P] in
theorem readyInternalAtNode_available_persist_after_other_write
    (compiled : CompiledProgram P L)
    {current next : (PrimitiveMachine compiled).State}
    {node₁ node₂ : Fin compiled.graph.nodeCount}
    {event₁ event₂ : (PrimitiveMachine compiled).Event}
    {written : EventGraph.TypedValue L}
    (hevent₁ :
      event₁ =
        Machine.Event.internal (M := PrimitiveMachine compiled)
          ({ node := node₁ } : (PrimitiveMachine compiled).Internal))
    (hevent₂ :
      event₂ =
        Machine.Event.internal (M := PrimitiveMachine compiled)
          ({ node := node₂ } : (PrimitiveMachine compiled).Internal))
    (havailable₁ :
      (PrimitiveMachine compiled).EventAvailable current event₁)
    (havailable₂ :
      (PrimitiveMachine compiled).EventAvailable current event₂)
    (hne : node₂ ≠ node₁)
    (hnext : next.1 = current.1.completeNode node₁ written) :
    (PrimitiveMachine compiled).EventAvailable next event₂ := by
  rw [hevent₁] at havailable₁
  rw [hevent₂] at havailable₂ ⊢
  change
    EventGraph.InternalAvailable compiled.graph next.1
      { node := node₂ }
  change
    EventGraph.InternalAvailable compiled.graph current.1
      { node := node₁ } at havailable₁
  change
    EventGraph.InternalAvailable compiled.graph current.1
      { node := node₂ } at havailable₂
  rcases havailable₁.ready with ⟨row₁, hrow₁, hready₁⟩
  rw [hnext]
  exact
    havailable₂.persist_after_other_ready_write
      compiled.graphWF hrow₁ hready₁ written hne

omit [Fintype P] in
theorem readyInternalEventsFromNodes_availableRunFrom_of_available
    (compiled : CompiledProgram P L)
    {source : (PrimitiveMachine compiled).State} :
    ∀ {current : (PrimitiveMachine compiled).State}
      {nodes : List (Fin compiled.graph.nodeCount)},
      nodes.Nodup →
      (∀ {node event},
        node ∈ nodes →
          EventGraph.ReadyInternalNode compiled.graph source.1 node →
            event =
              Machine.Event.internal (M := PrimitiveMachine compiled)
                ({ node := node } : (PrimitiveMachine compiled).Internal) →
              (PrimitiveMachine compiled).EventAvailable current event) →
      ∃ dst,
        (PrimitiveMachine compiled).AvailableRunFrom current
          (readyInternalEventsFromNodes compiled source nodes) dst
  | current, [], _hnodup, _havailable => ⟨current, .nil current⟩
  | current, node :: tail, hnodup, havailable => by
      classical
      have hnodupParts := List.nodup_cons.mp hnodup
      have hnodeNotTail : node ∉ tail := hnodupParts.1
      have htailNodup : tail.Nodup := hnodupParts.2
      let tailAvailable :
          ∀ {tailNode event},
            tailNode ∈ tail →
              EventGraph.ReadyInternalNode compiled.graph source.1
                tailNode →
                event =
                  Machine.Event.internal (M := PrimitiveMachine compiled)
                    ({ node := tailNode } :
                      (PrimitiveMachine compiled).Internal) →
                (PrimitiveMachine compiled).EventAvailable current event := by
        intro tailNode event hmem hready hevent
        exact havailable (by simp [hmem]) hready hevent
      by_cases hready :
          EventGraph.ReadyInternalNode compiled.graph source.1 node
      · let event : (PrimitiveMachine compiled).Event :=
          Machine.Event.internal (M := PrimitiveMachine compiled)
            ({ node := node } : (PrimitiveMachine compiled).Internal)
        have hheadAvailable :
            (PrimitiveMachine compiled).EventAvailable current event :=
          havailable (by simp) hready rfl
        rcases
            readyInternalAtNode_step_support
              compiled (node := node) (event := event) rfl
              hheadAvailable with
          ⟨written, next, hnextSupport, hnextCfg⟩
        let nextAvailable :
            ∀ {tailNode event₂},
              tailNode ∈ tail →
                EventGraph.ReadyInternalNode compiled.graph source.1
                  tailNode →
                  event₂ =
                    Machine.Event.internal (M := PrimitiveMachine compiled)
                      ({ node := tailNode } :
                        (PrimitiveMachine compiled).Internal) →
                  (PrimitiveMachine compiled).EventAvailable next event₂ := by
          intro tailNode event₂ hmem hreadyTail hevent₂
          have htailCurrent :
              (PrimitiveMachine compiled).EventAvailable current event₂ :=
            havailable (by simp [hmem]) hreadyTail hevent₂
          have hne : tailNode ≠ node := by
            intro heq
            exact hnodeNotTail (by simpa [heq] using hmem)
          exact
            readyInternalAtNode_available_persist_after_other_write
              compiled rfl hevent₂ hheadAvailable htailCurrent
              hne hnextCfg
        rcases
            readyInternalEventsFromNodes_availableRunFrom_of_available
              compiled htailNodup nextAvailable with
          ⟨dst, htailRun⟩
        have hrun :
            (PrimitiveMachine compiled).AvailableRunFrom current
              (event :: readyInternalEventsFromNodes compiled source tail)
              dst :=
          .cons hheadAvailable hnextSupport htailRun
        refine ⟨dst, ?_⟩
        simpa [readyInternalEventsFromNodes,
          EventGraph.readyInternalEventsFromNodes, hready, event] using hrun
      · rcases
            readyInternalEventsFromNodes_availableRunFrom_of_available
              compiled htailNodup tailAvailable with
          ⟨dst, hrun⟩
        refine ⟨dst, ?_⟩
        simpa [readyInternalEventsFromNodes,
          EventGraph.readyInternalEventsFromNodes, hready] using hrun

omit [Fintype P] in
theorem readyInternalEventsFromNodes_availableRunFrom_exists
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    {nodes : List (Fin compiled.graph.nodeCount)}
    (hnodup : nodes.Nodup) :
    ∃ dst,
      (PrimitiveMachine compiled).AvailableRunFrom state
        (readyInternalEventsFromNodes compiled state nodes) dst :=
  readyInternalEventsFromNodes_availableRunFrom_of_available
    compiled hnodup
    (fun _hmem hready hevent => by
      rw [hevent]
      change
        EventGraph.InternalAvailable compiled.graph state.1
          { node := _ }
      exact
        EventGraph.InternalAvailable.of_readyInternalNode
          compiled.graphWF
          (EventGraph.reachable_storeCoherent compiled.graphWF state.2)
          hready)

omit [Fintype P] in
theorem readyInternalEventsFromNodes_availableRunFrom_of_support
    (compiled : CompiledProgram P L)
    {source : (PrimitiveMachine compiled).State} :
    ∀ {current dst : (PrimitiveMachine compiled).State}
      {nodes : List (Fin compiled.graph.nodeCount)},
      nodes.Nodup →
      (∀ {node event},
        node ∈ nodes →
          EventGraph.ReadyInternalNode compiled.graph source.1 node →
            event =
              Machine.Event.internal (M := PrimitiveMachine compiled)
                ({ node := node } : (PrimitiveMachine compiled).Internal) →
              (PrimitiveMachine compiled).EventAvailable current event) →
      dst ∈
        ((PrimitiveMachine compiled).runEventsFrom
          (readyInternalEventsFromNodes compiled source nodes)
          current).support →
      (PrimitiveMachine compiled).AvailableRunFrom current
        (readyInternalEventsFromNodes compiled source nodes) dst
  | current, dst, [], _hnodup, _havailable, hsupport => by
      have hdst : dst = current := by
        simpa [readyInternalEventsFromNodes,
          EventGraph.readyInternalEventsFromNodes, PMF.support_pure,
          Set.mem_singleton_iff] using hsupport
      subst dst
      exact .nil current
  | current, dst, node :: tail, hnodup, havailable, hsupport => by
      classical
      have hnodupParts := List.nodup_cons.mp hnodup
      have hnodeNotTail : node ∉ tail := hnodupParts.1
      have htailNodup : tail.Nodup := hnodupParts.2
      let tailAvailable :
          ∀ {tailNode event},
            tailNode ∈ tail →
              EventGraph.ReadyInternalNode compiled.graph source.1
                tailNode →
                event =
                  Machine.Event.internal (M := PrimitiveMachine compiled)
                    ({ node := tailNode } :
                      (PrimitiveMachine compiled).Internal) →
                (PrimitiveMachine compiled).EventAvailable current event := by
        intro tailNode event hmem hready hevent
        exact havailable (by simp [hmem]) hready hevent
      by_cases hready :
          EventGraph.ReadyInternalNode compiled.graph source.1 node
      · let event : (PrimitiveMachine compiled).Event :=
          Machine.Event.internal (M := PrimitiveMachine compiled)
            ({ node := node } : (PrimitiveMachine compiled).Internal)
        have hheadAvailable :
            (PrimitiveMachine compiled).EventAvailable current event :=
          havailable (by simp) hready rfl
        have hsupport' :
            dst ∈
              ((PrimitiveMachine compiled).runEventsFrom
                (event ::
                  readyInternalEventsFromNodes compiled source tail)
                current).support := by
          simpa [readyInternalEventsFromNodes,
            EventGraph.readyInternalEventsFromNodes, hready, event] using
            hsupport
        rw [Machine.runEventsFrom_cons_bind] at hsupport'
        rw [PMF.mem_support_bind_iff] at hsupport'
        rcases hsupport' with ⟨mid, hmid, htailSupport⟩
        rcases
            readyInternalAtNode_step_support_completeNode
              compiled (node := node) (event := event) rfl
              hheadAvailable hmid with
          ⟨written, hmidCfg⟩
        let nextAvailable :
            ∀ {tailNode event₂},
              tailNode ∈ tail →
                EventGraph.ReadyInternalNode compiled.graph source.1
                  tailNode →
                  event₂ =
                    Machine.Event.internal (M := PrimitiveMachine compiled)
                      ({ node := tailNode } :
                        (PrimitiveMachine compiled).Internal) →
                  (PrimitiveMachine compiled).EventAvailable mid event₂ := by
          intro tailNode event₂ hmem hreadyTail hevent₂
          have htailCurrent :
              (PrimitiveMachine compiled).EventAvailable current event₂ :=
            havailable (by simp [hmem]) hreadyTail hevent₂
          have hne : tailNode ≠ node := by
            intro heq
            exact hnodeNotTail (by simpa [heq] using hmem)
          exact
            readyInternalAtNode_available_persist_after_other_write
              compiled rfl hevent₂ hheadAvailable htailCurrent
              hne hmidCfg
        have htailRun :
            (PrimitiveMachine compiled).AvailableRunFrom mid
              (readyInternalEventsFromNodes compiled source tail) dst :=
          readyInternalEventsFromNodes_availableRunFrom_of_support
            (compiled := compiled) (source := source) (current := mid)
            (dst := dst) (nodes := tail)
            htailNodup nextAvailable htailSupport
        simpa [readyInternalEventsFromNodes,
          EventGraph.readyInternalEventsFromNodes, hready, event] using
          (Machine.AvailableRunFrom.cons hheadAvailable hmid htailRun)
      · have htailSupport :
            dst ∈
              ((PrimitiveMachine compiled).runEventsFrom
                (readyInternalEventsFromNodes compiled source tail)
                current).support := by
          simpa [readyInternalEventsFromNodes,
            EventGraph.readyInternalEventsFromNodes, hready] using hsupport
        simpa [readyInternalEventsFromNodes,
          EventGraph.readyInternalEventsFromNodes, hready] using
          readyInternalEventsFromNodes_availableRunFrom_of_support
            (compiled := compiled) (source := source) (current := current)
            (dst := dst) (nodes := tail)
            htailNodup tailAvailable htailSupport

omit [Fintype P] in
theorem readyInternalEvents_availableRunFrom_of_support
    (compiled : CompiledProgram P L)
    {state dst : (PrimitiveMachine compiled).State}
    (hsupport :
      dst ∈
        ((PrimitiveMachine compiled).runEventsFrom
          (readyInternalEvents compiled state) state).support) :
    (PrimitiveMachine compiled).AvailableRunFrom state
      (readyInternalEvents compiled state) dst := by
  simpa [readyInternalEvents] using
    readyInternalEventsFromNodes_availableRunFrom_of_support
      compiled compiled.graph.nodeOrder_nodup
      (fun _hmem hready hevent => by
        rw [hevent]
        change
          EventGraph.InternalAvailable compiled.graph state.1
            { node := _ }
        exact
          EventGraph.InternalAvailable.of_readyInternalNode
            compiled.graphWF
            (EventGraph.reachable_storeCoherent compiled.graphWF state.2)
            hready)
      hsupport

omit [Fintype P] in
theorem readyInternalEvents_availableRunFrom_exists
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State} :
    ∃ dst,
      (PrimitiveMachine compiled).AvailableRunFrom state
        (readyInternalEvents compiled state) dst := by
  simpa [readyInternalEvents] using
    readyInternalEventsFromNodes_availableRunFrom_exists
      compiled compiled.graph.nodeOrder_nodup

omit [Fintype P] in
theorem readyInternalEvents_ne_nil_of_nonempty
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    (hinternal : (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty) :
    readyInternalEvents compiled state ≠ [] := by
  classical
  rcases hinternal with ⟨node, hnode⟩
  have hready :
      EventGraph.ReadyInternalNode compiled.graph state.1 node :=
    (Finset.mem_filter.mp hnode).2
  have hmem :
      Machine.Event.internal (M := PrimitiveMachine compiled)
        ({ node := node } : (PrimitiveMachine compiled).Internal) ∈
        readyInternalEvents compiled state := by
    unfold readyInternalEvents
    rw [mem_readyInternalEventsFromNodes_iff]
    exact ⟨node, compiled.graph.mem_nodeOrder node, hready, rfl⟩
  intro hnil
  rw [hnil] at hmem
  cases hmem

omit [Fintype P] in
/-- A primitive batch containing only internal graph events. -/
def InternalOnlyBatch
    (compiled : CompiledProgram P L)
    (batch : List (PrimitiveMachine compiled).Event) : Prop :=
  ∀ event, event ∈ batch →
    ∃ internalEvent : (PrimitiveMachine compiled).Internal,
      event = Machine.Event.internal (M := PrimitiveMachine compiled)
        internalEvent

omit [Fintype P] in
theorem internalOnlyBatch_nil
    (compiled : CompiledProgram P L) :
    InternalOnlyBatch compiled [] := by
  intro event hmem
  cases hmem

omit [Fintype P] in
theorem internalOnlyBatch_append
    (compiled : CompiledProgram P L)
    {left right : List (PrimitiveMachine compiled).Event}
    (hleft : InternalOnlyBatch compiled left)
    (hright : InternalOnlyBatch compiled right) :
    InternalOnlyBatch compiled (left ++ right) := by
  intro event hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft event hmem
  · exact hright event hmem

omit [Fintype P] in
theorem readyInternalEvents_internalOnly
    (compiled : CompiledProgram P L)
    (state : (PrimitiveMachine compiled).State) :
    InternalOnlyBatch compiled (readyInternalEvents compiled state) := by
  intro event hmem
  rcases
      (mem_readyInternalEventsFromNodes_iff
        compiled state compiled.graph.nodeOrder).mp
        (by simpa [readyInternalEvents] using hmem) with
    ⟨node, _hnode, _hready, hevent⟩
  exact ⟨{ node := node }, hevent⟩

omit [Fintype P] in
/-- Fixed-fuel closure of ready internal graph work.

Each pass executes every internal node ready at the current checkpoint in graph
order.  Graph node-count fuel is enough for compiler-generated default games;
the certificate theorem below is stated for arbitrary fuel because the frontier
round only needs the supported primitive run it induces. -/
noncomputable def internalClosureTransition
    (compiled : CompiledProgram P L) :
    Nat → (PrimitiveMachine compiled).State →
      PMF (PrimitiveMachine compiled).State
  | 0, state => PMF.pure state
  | fuel + 1, state => by
      classical
      if (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty then
        exact
          ((PrimitiveMachine compiled).runEventsFrom
            (readyInternalEvents compiled state) state).bind
            (internalClosureTransition compiled fuel)
      else
        exact PMF.pure state

omit [Fintype P] in
theorem internalClosureTransition_support_cert
    (compiled : CompiledProgram P L) :
    ∀ fuel {state dst : (PrimitiveMachine compiled).State},
      dst ∈ (internalClosureTransition compiled fuel state).support →
        ∃ batch : List (PrimitiveMachine compiled).Event,
          InternalOnlyBatch compiled batch ∧
            (PrimitiveMachine compiled).AvailableRunFrom state batch dst
  | 0, state, dst, hsupport => by
      have hdst : dst = state := by
        simpa [internalClosureTransition, PMF.support_pure,
          Set.mem_singleton_iff] using hsupport
      subst dst
      exact ⟨[], internalOnlyBatch_nil compiled, .nil state⟩
  | fuel + 1, state, dst, hsupport => by
      classical
      by_cases hinternal :
          (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty
      · have hsupport' :
            dst ∈
              (((PrimitiveMachine compiled).runEventsFrom
                (readyInternalEvents compiled state) state).bind
                (internalClosureTransition compiled fuel)).support := by
          simpa [internalClosureTransition, hinternal] using hsupport
        rw [PMF.mem_support_bind_iff] at hsupport'
        rcases hsupport' with ⟨mid, hmid, htail⟩
        have hheadRun :
            (PrimitiveMachine compiled).AvailableRunFrom state
              (readyInternalEvents compiled state) mid :=
          readyInternalEvents_availableRunFrom_of_support
            compiled hmid
        rcases internalClosureTransition_support_cert
            compiled fuel htail with
          ⟨tail, htailInternal, htailRun⟩
        exact
          ⟨readyInternalEvents compiled state ++ tail,
            internalOnlyBatch_append compiled
              (readyInternalEvents_internalOnly compiled state)
              htailInternal,
            hheadRun.append htailRun⟩
      · have hdst : dst = state := by
          simpa [internalClosureTransition, hinternal, PMF.support_pure,
            Set.mem_singleton_iff] using hsupport
        subst dst
        exact ⟨[], internalOnlyBatch_nil compiled, .nil state⟩

omit [Fintype P] in
theorem readyInternalNodes_empty_of_not_nonempty
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    (hinternal :
      ¬ (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty) :
    EventGraph.readyInternalNodes compiled.graph state.1 = ∅ := by
  ext node
  constructor
  · intro hnode
    exact False.elim (hinternal ⟨node, hnode⟩)
  · intro hnode
    cases hnode

omit [Fintype P] in
theorem no_readyInternal_or_card_growth_of_internalClosureTransition_support
    (compiled : CompiledProgram P L) :
    ∀ fuel {state dst : (PrimitiveMachine compiled).State},
      dst ∈ (internalClosureTransition compiled fuel state).support →
        EventGraph.readyInternalNodes compiled.graph dst.1 = ∅ ∨
          state.1.done.card + fuel ≤ dst.1.done.card
  | 0, state, dst, hsupport => by
      have hdst : dst = state := by
        simpa [internalClosureTransition, PMF.support_pure,
          Set.mem_singleton_iff] using hsupport
      subst dst
      exact Or.inr (by simp)
  | fuel + 1, state, dst, hsupport => by
      classical
      by_cases hinternal :
          (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty
      · have hsupport' :
            dst ∈
              (((PrimitiveMachine compiled).runEventsFrom
                (readyInternalEvents compiled state) state).bind
                (internalClosureTransition compiled fuel)).support := by
          simpa [internalClosureTransition, hinternal] using hsupport
        rw [PMF.mem_support_bind_iff] at hsupport'
        rcases hsupport' with ⟨mid, hmid, htail⟩
        have hheadRun :
            (PrimitiveMachine compiled).AvailableRunFrom state
              (readyInternalEvents compiled state) mid :=
          readyInternalEvents_availableRunFrom_of_support
            compiled hmid
        have hheadNe :
            readyInternalEvents compiled state ≠ [] :=
          readyInternalEvents_ne_nil_of_nonempty compiled hinternal
        have hheadCard :
            state.1.done.card + 1 ≤ mid.1.done.card :=
          Nat.succ_le_of_lt
            (Finset.card_lt_card
              (EventGraph.ToMachine.primitiveMachine_availableRunFrom_done_ssubset_of_ne_nil
                (primitiveMachineSpec compiled) hheadRun hheadNe))
        rcases
            no_readyInternal_or_card_growth_of_internalClosureTransition_support
              compiled fuel htail with
          hclosed | htailCard
        · exact Or.inl hclosed
        · exact Or.inr (by omega)
      · have hdst : dst = state := by
          simpa [internalClosureTransition, hinternal, PMF.support_pure,
            Set.mem_singleton_iff] using hsupport
        subst dst
        exact Or.inl
          (readyInternalNodes_empty_of_not_nonempty compiled hinternal)

omit [Fintype P] in
theorem internalClosureTransition_support_closed
    (compiled : CompiledProgram P L)
    {state dst : (PrimitiveMachine compiled).State}
    (hsupport :
      dst ∈
        (internalClosureTransition compiled compiled.graph.nodeCount
          state).support) :
    EventGraph.readyInternalNodes compiled.graph dst.1 = ∅ := by
  classical
  rcases
      no_readyInternal_or_card_growth_of_internalClosureTransition_support
        compiled compiled.graph.nodeCount hsupport with
    hclosed | hcardGrowth
  · exact hclosed
  · by_contra hnotClosed
    have hnonempty :
        (EventGraph.readyInternalNodes compiled.graph dst.1).Nonempty := by
      by_cases h :
          (EventGraph.readyInternalNodes compiled.graph dst.1).Nonempty
      · exact h
      · exact False.elim (hnotClosed
          (readyInternalNodes_empty_of_not_nonempty compiled h))
    rcases hnonempty with ⟨node, hnodeMem⟩
    have hreadyInternal :
        EventGraph.ReadyInternalNode compiled.graph dst.1 node :=
      (Finset.mem_filter.mp hnodeMem).2
    rcases hreadyInternal with
      ⟨_row, _hrow, _hinternalNode, hready⟩
    have hcardLe :
        dst.1.done.card ≤ compiled.graph.nodeCount := by
      calc
        dst.1.done.card ≤
            (Finset.univ :
              Finset (Fin compiled.graph.nodeCount)).card :=
          Finset.card_le_card (by intro node _hnode; simp)
        _ = compiled.graph.nodeCount := by simp
    have hnodeCountLe :
        compiled.graph.nodeCount ≤ dst.1.done.card := by
      omega
    have hcard :
        dst.1.done.card =
          (Finset.univ : Finset (Fin compiled.graph.nodeCount)).card := by
      apply le_antisymm
      · simpa using hcardLe
      · simpa using hnodeCountLe
    have hdone :
        dst.1.done =
          (Finset.univ : Finset (Fin compiled.graph.nodeCount)) := by
      apply Finset.eq_univ_of_card
      exact hcard
    exact hready.1 (by rw [hdone]; exact Finset.mem_univ node)

omit [Fintype P] in
/-- Internal closure used by the default frontier semantics when the source
checkpoint already has ready internal work. -/
noncomputable def internalClosureAfterReady
    (compiled : CompiledProgram P L)
    (state : (PrimitiveMachine compiled).State) :
    PMF (PrimitiveMachine compiled).State :=
  ((PrimitiveMachine compiled).runEventsFrom
    (readyInternalEvents compiled state) state).bind
    (internalClosureTransition compiled compiled.graph.nodeCount)

omit [Fintype P] in
theorem internalClosureAfterReady_support_cert
    (compiled : CompiledProgram P L)
    {state dst : (PrimitiveMachine compiled).State}
    (hinternal :
      (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty)
    (hsupport :
      dst ∈ (internalClosureAfterReady compiled state).support) :
    ∃ batch : List (PrimitiveMachine compiled).Event,
      InternalOnlyBatch compiled batch ∧
        (PrimitiveMachine compiled).AvailableRunFrom state batch dst ∧
          batch ≠ [] := by
  rw [internalClosureAfterReady, PMF.mem_support_bind_iff] at hsupport
  rcases hsupport with ⟨mid, hmid, htail⟩
  have hheadRun :
      (PrimitiveMachine compiled).AvailableRunFrom state
        (readyInternalEvents compiled state) mid :=
    readyInternalEvents_availableRunFrom_of_support
      compiled hmid
  rcases internalClosureTransition_support_cert
      compiled compiled.graph.nodeCount htail with
    ⟨tail, htailInternal, htailRun⟩
  refine
    ⟨readyInternalEvents compiled state ++ tail,
      internalOnlyBatch_append compiled
        (readyInternalEvents_internalOnly compiled state)
        htailInternal,
      hheadRun.append htailRun,
      ?_⟩
  intro hnil
  have hheadNil : readyInternalEvents compiled state = [] :=
    List.eq_nil_of_append_eq_nil hnil |>.1
  exact readyInternalEvents_ne_nil_of_nonempty compiled hinternal hheadNil

omit [Fintype P] in
theorem internalClosureAfterReady_support_closed
    (compiled : CompiledProgram P L)
    {state dst : (PrimitiveMachine compiled).State}
    (hsupport :
      dst ∈ (internalClosureAfterReady compiled state).support) :
    EventGraph.readyInternalNodes compiled.graph dst.1 = ∅ := by
  rw [internalClosureAfterReady, PMF.mem_support_bind_iff] at hsupport
  rcases hsupport with ⟨_mid, _hmid, htail⟩
  exact internalClosureTransition_support_closed compiled htail

omit [Fintype P] in
def InternalClosureRunCert
    (compiled : CompiledProgram P L)
    (state dst : (PrimitiveMachine compiled).State) : Prop :=
  ∃ batch : List (PrimitiveMachine compiled).Event,
    InternalOnlyBatch compiled batch ∧
      (PrimitiveMachine compiled).AvailableRunFrom state batch dst

omit [Fintype P] in
noncomputable def internalClosureRunEventBatch
    (compiled : CompiledProgram P L)
    (state dst : (PrimitiveMachine compiled).State) :
    List (PrimitiveMachine compiled).Event := by
  classical
  if hcert : InternalClosureRunCert compiled state dst then
    exact Classical.choose hcert
  else
    exact []

omit [Fintype P] in
theorem internalClosureRunEventBatch_spec
    (compiled : CompiledProgram P L)
    {state dst : (PrimitiveMachine compiled).State}
    (hcert : InternalClosureRunCert compiled state dst) :
    InternalOnlyBatch compiled
        (internalClosureRunEventBatch compiled state dst) ∧
      (PrimitiveMachine compiled).AvailableRunFrom state
        (internalClosureRunEventBatch compiled state dst) dst := by
  classical
  unfold internalClosureRunEventBatch
  rw [dif_pos hcert]
  exact Classical.choose_spec hcert

omit [Fintype P] in
def InternalClosureBatchCert
    (compiled : CompiledProgram P L)
    (state dst : (PrimitiveMachine compiled).State) : Prop :=
  ∃ batch : List (PrimitiveMachine compiled).Event,
    InternalOnlyBatch compiled batch ∧
      (PrimitiveMachine compiled).AvailableRunFrom state batch dst ∧
        batch ≠ []

omit [Fintype P] in
noncomputable def internalClosureEventBatch
    (compiled : CompiledProgram P L)
    (state dst : (PrimitiveMachine compiled).State) :
    List (PrimitiveMachine compiled).Event := by
  classical
  if hcert : InternalClosureBatchCert compiled state dst then
    exact Classical.choose hcert
  else
    exact []

omit [Fintype P] in
theorem internalClosureEventBatch_spec
    (compiled : CompiledProgram P L)
    {state dst : (PrimitiveMachine compiled).State}
    (hcert : InternalClosureBatchCert compiled state dst) :
    InternalOnlyBatch compiled
        (internalClosureEventBatch compiled state dst) ∧
      (PrimitiveMachine compiled).AvailableRunFrom state
        (internalClosureEventBatch compiled state dst) dst ∧
      internalClosureEventBatch compiled state dst ≠ [] := by
  classical
  unfold internalClosureEventBatch
  rw [dif_pos hcert]
  exact Classical.choose_spec hcert

omit [Fintype P] in
theorem frontierBatchRealizesAction_append_internalOnly
    (compiled : CompiledProgram P L)
    {action : JointAction (FrontierAct compiled)}
    {strategic internal : List (PrimitiveMachine compiled).Event}
    (hstrategic :
      FrontierBatchRealizesAction compiled action strategic)
    (hinternal : InternalOnlyBatch compiled internal) :
    FrontierBatchRealizesAction compiled action (strategic ++ internal) := by
  constructor
  · intro event hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hstrategic.1 event hmem
    · rcases hinternal event hmem with ⟨internalEvent, hevent⟩
      rw [hevent]
      trivial
  · intro who frontierAction node value haction hvalue
    exact List.mem_append_left internal
      (hstrategic.2 who frontierAction node value haction hvalue)

/-- Certificate attached to one supported frontier-round transition. -/
abbrev FrontierRoundStepCertificate
    (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph)
    {state : (PrimitiveMachine compiled).State}
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a})
    (dst : (PrimitiveMachine compiled).State)
    (batch : List (PrimitiveMachine compiled).Event) : Prop :=
  EventGraph.FrontierRoundStepCertificate
    (primitiveMachineSpec compiled) presentation action dst batch

/-- Strategic semantics for one frontier round under a checkpoint
presentation. -/
abbrev FrontierRoundSemantics (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph) : Type :=
  EventGraph.FrontierRoundSemantics
    (primitiveMachineSpec compiled) presentation

/-- Native machine round view induced by canonical graph frontiers and an
explicit frontier-round operational semantics. -/
noncomputable def frontierRoundView
    (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph)
    (semantics : FrontierRoundSemantics compiled presentation) :
    (PrimitiveMachine compiled).RoundView :=
  EventGraph.frontierRoundView
    (primitiveMachineSpec compiled) presentation semantics

/-- Primitive downset checkpoint presentation induced by compiled graph
well-formedness and graph guard liveness. -/
noncomputable def primitiveDownsetPresentation
    (compiled : CompiledProgram P L)
    (guards : EventGraph.GuardLive compiled.graph) :
    EventGraph.CheckpointPresentation compiled.graph :=
  EventGraph.primitiveDownsetCheckpointPresentation compiled.graph
    (EventGraph.primitiveDownsetProgress_of_availableEventProgress
      (EventGraph.availableEventProgress_of_guardLive
        compiled.graphWF guards))

private noncomputable def selectedCommitDestination
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a})
    (hactive : (frontierActive compiled state).Nonempty) :
    (PrimitiveMachine compiled).State :=
  Classical.choose
    (selectedCommitEvents_primitiveDownset_allowed_of_active
      compiled action.2 hactive)

private theorem selectedCommitDestination_spec
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a})
    (hactive : (frontierActive compiled state).Nonempty) :
    (PrimitiveMachine compiled).AvailableRunFrom state
        (selectedCommitEvents compiled action.1)
        (selectedCommitDestination compiled action hactive) ∧
      (EventGraph.primitiveDownsetCheckpointPolicy compiled.graph).allowed
        state (selectedCommitDestination compiled action hactive) :=
  Classical.choose_spec
    (selectedCommitEvents_primitiveDownset_allowed_of_active
      compiled action.2 hactive)

private noncomputable def selectedCommitClosureTransition
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a})
    (hactive : (frontierActive compiled state).Nonempty) :
    PMF (PrimitiveMachine compiled).State :=
  internalClosureTransition compiled compiled.graph.nodeCount
    (selectedCommitDestination compiled action hactive)

private theorem selectedCommitClosure_support_cert
    (compiled : CompiledProgram P L)
    {state dst : (PrimitiveMachine compiled).State}
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a})
    (hactive : (frontierActive compiled state).Nonempty)
    (hsupport :
      dst ∈ (selectedCommitClosureTransition compiled action hactive).support) :
    InternalClosureRunCert compiled
      (selectedCommitDestination compiled action hactive) dst :=
  internalClosureTransition_support_cert
    compiled compiled.graph.nodeCount hsupport

private theorem selectedCommitClosure_support_closed
    (compiled : CompiledProgram P L)
    {state dst : (PrimitiveMachine compiled).State}
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a})
    (hactive : (frontierActive compiled state).Nonempty)
    (hsupport :
      dst ∈ (selectedCommitClosureTransition compiled action hactive).support) :
    EventGraph.readyInternalNodes compiled.graph dst.1 = ∅ :=
  internalClosureTransition_support_closed compiled hsupport

private theorem active_eq_empty_of_not_nonempty
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    (hactive : ¬ (frontierActive compiled state).Nonempty) :
    frontierActive compiled state = ∅ := by
  ext who
  constructor
  · intro hwho
    exact False.elim (hactive ⟨who, hwho⟩)
  · intro hwho
    cases hwho

private theorem activePlayers_eq_empty_of_frontier_empty_no_internal
    (compiled : CompiledProgram P L)
    {state : (PrimitiveMachine compiled).State}
    (hreadyInternal :
      ¬ (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty)
    (hfrontier : frontierActive compiled state = ∅) :
    EventGraph.activePlayers compiled.graph state.1 = ∅ := by
  simpa [frontierActive, EventGraph.frontierActive, hreadyInternal]
    using hfrontier

private theorem no_ready_internal_no_active_impossible
    (compiled : CompiledProgram P L)
    (guards : EventGraph.GuardLive compiled.graph)
    {state : (PrimitiveMachine compiled).State}
    (hterminal : ¬ (PrimitiveMachine compiled).terminal state)
    (hreadyInternal :
      ¬ (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty)
    (hfrontier : frontierActive compiled state = ∅) :
    False := by
  have hactivePlayersEmpty :
      EventGraph.activePlayers compiled.graph state.1 = ∅ :=
    activePlayers_eq_empty_of_frontier_empty_no_internal
      compiled hreadyInternal hfrontier
  rcases EventGraph.exists_internal_available_of_no_active
      compiled.graphWF guards hterminal hactivePlayersEmpty with
    ⟨event, havailable⟩
  have hreadyInternalNode :
      EventGraph.ReadyInternalNode compiled.graph state.1 event.node :=
    havailable.readyInternalNode
  have hmem :
      event.node ∈
        EventGraph.readyInternalNodes compiled.graph state.1 := by
    unfold EventGraph.readyInternalNodes
    simp [hreadyInternalNode]
  exact hreadyInternal ⟨event.node, hmem⟩

/-- Frontier-checkpoint transitions generated by the canonical strategic
frontier policy.

An allowed checkpoint either closes currently-ready internal work, or, when no
internal work is ready, executes one legal strategic commit frontier and then
closes newly-ready internal work. -/
inductive FrontierCheckpointAllowed
    (compiled : CompiledProgram P L) :
    (PrimitiveMachine compiled).State →
      (PrimitiveMachine compiled).State → Prop where
  | internal {src dst : (PrimitiveMachine compiled).State}
      (hinternal :
        (EventGraph.readyInternalNodes compiled.graph src.1).Nonempty)
      (hsupport :
        dst ∈ (internalClosureAfterReady compiled src).support) :
      FrontierCheckpointAllowed compiled src dst
  | strategic {src dst : (PrimitiveMachine compiled).State}
      (hnoInternal :
        ¬ (EventGraph.readyInternalNodes compiled.graph src.1).Nonempty)
      (hactive : (frontierActive compiled src).Nonempty)
      (action :
        {a : JointAction (FrontierAct compiled) //
          JointActionLegal (FrontierAct compiled)
            (frontierActive compiled)
            (PrimitiveMachine compiled).terminal
            (frontierAvailableActions compiled) src a})
      (hsupport :
        dst ∈ (selectedCommitClosureTransition
          compiled action hactive).support) :
      FrontierCheckpointAllowed compiled src dst

private theorem frontierCheckpointAllowed_run
    (compiled : CompiledProgram P L)
    {src dst : (PrimitiveMachine compiled).State}
    (hallowed : FrontierCheckpointAllowed compiled src dst) :
    ∃ batch : List (PrimitiveMachine compiled).Event,
      (PrimitiveMachine compiled).AvailableRunFrom src batch dst ∧
        batch ≠ [] := by
  cases hallowed with
  | internal hinternal hsupport =>
      rcases internalClosureAfterReady_support_cert
          compiled hinternal hsupport with
        ⟨batch, _hinternalOnly, hrun, hne⟩
      exact ⟨batch, hrun, hne⟩
  | strategic hnoInternal hactive action hsupport =>
      have hprefix := selectedCommitDestination_spec compiled action hactive
      have htailCert :=
        selectedCommitClosure_support_cert
          compiled action hactive hsupport
      have htailSpec :=
        internalClosureRunEventBatch_spec compiled htailCert
      let batch :=
        selectedCommitEvents compiled action.1 ++
          internalClosureRunEventBatch compiled
            (selectedCommitDestination compiled action hactive) dst
      have hrun :
          (PrimitiveMachine compiled).AvailableRunFrom src batch dst := by
        dsimp [batch]
        exact hprefix.1.append htailSpec.2
      have hne : batch ≠ [] := by
        intro hnil
        have hselectedNil :
            selectedCommitEvents compiled action.1 = [] :=
          (List.eq_nil_of_append_eq_nil hnil).1
        exact
          selectedCommitEvents_ne_nil_of_active
            compiled action.2 hactive hselectedNil
      exact ⟨batch, hrun, hne⟩

private theorem frontierCheckpointAllowed_realizable
    (compiled : CompiledProgram P L)
    {src dst : (PrimitiveMachine compiled).State}
    (hallowed : FrontierCheckpointAllowed compiled src dst) :
    EventGraph.CheckpointStep compiled.graph src dst := by
  rcases frontierCheckpointAllowed_run compiled hallowed with
    ⟨batch, hrun, _hne⟩
  exact
    EventGraph.ToMachine.checkpointStep_of_availableRunFrom
      (primitiveMachineSpec compiled) hrun

private theorem frontierCheckpointAllowed_advances
    (compiled : CompiledProgram P L)
    {src dst : (PrimitiveMachine compiled).State}
    (hallowed : FrontierCheckpointAllowed compiled src dst) :
    src.1.done ⊂ dst.1.done := by
  rcases frontierCheckpointAllowed_run compiled hallowed with
    ⟨batch, hrun, hne⟩
  exact
    EventGraph.ToMachine.primitiveMachine_availableRunFrom_done_ssubset_of_ne_nil
      (primitiveMachineSpec compiled) hrun hne

/-- Checkpoint presentation matching the canonical frontier round policy. -/
noncomputable def frontierPresentation
    (compiled : CompiledProgram P L)
    (guards : EventGraph.GuardLive compiled.graph) :
    EventGraph.CheckpointPresentation compiled.graph where
  policy :=
    { allowed := FrontierCheckpointAllowed compiled
      realizable := frontierCheckpointAllowed_realizable compiled
      advances := frontierCheckpointAllowed_advances compiled }
  nonterminal_exists_allowed := by
    intro state hterminal
    classical
    by_cases hinternal :
        (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty
    · rcases (internalClosureAfterReady compiled state).support_nonempty with
        ⟨dst, hdst⟩
      exact ⟨dst, FrontierCheckpointAllowed.internal hinternal hdst⟩
    · by_cases hactive : (frontierActive compiled state).Nonempty
      · rcases EventGraph.exists_legal_frontier_action_of_reachable
          compiled.graphWF guards hterminal with
          ⟨rawAction, hlegalRaw⟩
        let action :
            {a : JointAction (FrontierAct compiled) //
              JointActionLegal (FrontierAct compiled)
                (frontierActive compiled)
                (PrimitiveMachine compiled).terminal
                (frontierAvailableActions compiled) state a} :=
          ⟨rawAction, by
            constructor
            · simpa [PrimitiveMachine,
                EventGraph.ToMachine.primitiveMachine] using hlegalRaw.1
            · intro who
              have hwho := hlegalRaw.2 who
              cases haction : rawAction who with
              | none =>
                  simpa [haction, frontierActive,
                    EventGraph.frontierActive, hinternal,
                    frontierAvailableActions, PrimitiveMachine,
                    EventGraph.ToMachine.primitiveMachine] using hwho
              | some localAction =>
                  simpa [haction, frontierActive,
                    EventGraph.frontierActive, hinternal,
                    frontierAvailableActions, PrimitiveMachine,
                    EventGraph.ToMachine.primitiveMachine] using hwho⟩
        rcases
            (selectedCommitClosureTransition compiled action hactive).support_nonempty with
          ⟨dst, hdst⟩
        exact
          ⟨dst,
            FrontierCheckpointAllowed.strategic
              hinternal hactive action hdst⟩
      · have hactiveEmpty := active_eq_empty_of_not_nonempty
          compiled hactive
        exact False.elim
          (no_ready_internal_no_active_impossible
            compiled guards hterminal hinternal hactiveEmpty)

private noncomputable def canonicalFrontierTransition
    (compiled : CompiledProgram P L)
    (guards : EventGraph.GuardLive compiled.graph)
    (state : (PrimitiveMachine compiled).State)
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
        (frontierAvailableActions compiled) state a}) :
    PMF (PrimitiveMachine compiled).State := by
  classical
  if _hinternal :
      (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty then
    exact internalClosureAfterReady compiled state
  else if hactive : (frontierActive compiled state).Nonempty then
    exact selectedCommitClosureTransition compiled action hactive
  else
    let hactiveEmpty := active_eq_empty_of_not_nonempty
      compiled hactive
    exact False.elim
      (no_ready_internal_no_active_impossible
        compiled guards action.2.1 _hinternal hactiveEmpty)

private noncomputable def canonicalFrontierEventBatch
    (compiled : CompiledProgram P L)
    (guards : EventGraph.GuardLive compiled.graph)
    (state : (PrimitiveMachine compiled).State)
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a})
    (_dst : (PrimitiveMachine compiled).State) :
    List (PrimitiveMachine compiled).Event := by
  classical
  if _hinternal :
      (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty then
    exact internalClosureEventBatch compiled state _dst
  else if hactive : (frontierActive compiled state).Nonempty then
    exact
      selectedCommitEvents compiled action.1 ++
        internalClosureRunEventBatch compiled
          (selectedCommitDestination compiled action hactive) _dst
  else
    let hactiveEmpty := active_eq_empty_of_not_nonempty
      compiled hactive
    exact False.elim
      (no_ready_internal_no_active_impossible
        compiled guards action.2.1 _hinternal hactiveEmpty)

/-- Canonical frontier semantics.

When internal graph nodes are ready, the round closes internal work before
presenting any strategic frontier. Otherwise, when players are active, the
round executes the selected commit frontier and then closes newly-ready
internal work before the checkpoint observation. A nonterminal checkpoint with
neither ready internal work nor active commits is impossible under graph
well-formedness and live guards. -/
noncomputable def canonicalFrontierRoundSemantics
    (compiled : CompiledProgram P L)
    (guards : EventGraph.GuardLive compiled.graph) :
    FrontierRoundSemantics compiled
      (frontierPresentation compiled guards) where
  guards := guards
  transition := canonicalFrontierTransition compiled guards
  eventBatch := canonicalFrontierEventBatch compiled guards
  certifies := by
    classical
    intro state action dst hsupport
    by_cases hinternal :
        (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty
    · have hsupportMem :
          dst ∈
            (internalClosureAfterReady compiled state).support :=
        (PMF.mem_support_iff _ _).2 (by
          simpa [canonicalFrontierTransition, hinternal]
            using hsupport)
      have hcert :
          InternalClosureBatchCert compiled state dst :=
        internalClosureAfterReady_support_cert
          compiled hinternal hsupportMem
      have hbatchSpec :=
        internalClosureEventBatch_spec compiled hcert
      have hrealizes :
          FrontierBatchRealizesAction compiled action.1
            (internalClosureEventBatch compiled state dst) := by
        constructor
        · intro event hmem
          rcases hbatchSpec.1 event hmem with
            ⟨internalEvent, hevent⟩
          rw [hevent]
          trivial
        · intro who frontierAction node value haction _hvalue
          have hlocal := action.2.2 who
          rw [haction] at hlocal
          have hwho : who ∈ frontierActive compiled state := hlocal.1
          have hfrontierEmpty :
              frontierActive compiled state = ∅ := by
            simp [frontierActive, EventGraph.frontierActive, hinternal]
          rw [hfrontierEmpty] at hwho
          cases hwho
      exact
        { realizesAction := by
            simpa [canonicalFrontierEventBatch, hinternal] using
              hrealizes
          availableRun := by
            simpa [canonicalFrontierEventBatch, hinternal] using
              hbatchSpec.2.1
          allowed :=
            FrontierCheckpointAllowed.internal hinternal hsupportMem }
    · by_cases hactive : (frontierActive compiled state).Nonempty
      · have hsupportMem :
            dst ∈
              (selectedCommitClosureTransition
                compiled action hactive).support :=
          (PMF.mem_support_iff _ _).2 (by
            simpa [canonicalFrontierTransition, hinternal, hactive]
              using hsupport)
        have hclosureCert :
            InternalClosureRunCert compiled
              (selectedCommitDestination compiled action hactive) dst :=
          selectedCommitClosure_support_cert
            compiled action hactive hsupportMem
        have hclosureSpec :=
          internalClosureRunEventBatch_spec compiled hclosureCert
        have hspec :=
          selectedCommitDestination_spec compiled action hactive
        have hrealizes :
            EventGraph.FrontierBatchRealizesAction
              (primitiveMachineSpec compiled) action.1
              (canonicalFrontierEventBatch compiled guards
                state action
                dst) := by
          have hselectedRealizes :
              FrontierBatchRealizesAction compiled action.1
                (selectedCommitEvents compiled action.1) :=
            selectedCommitEvents_realizesAction
              compiled action.1 action.2
          simpa [canonicalFrontierEventBatch, hinternal, hactive] using
            frontierBatchRealizesAction_append_internalOnly
              compiled hselectedRealizes hclosureSpec.1
        have hrun :
            (EventGraph.PrimitiveMachineOf
              (primitiveMachineSpec compiled)).AvailableRunFrom state
              (canonicalFrontierEventBatch compiled guards
                state action
                dst)
              dst := by
          simpa [canonicalFrontierEventBatch, hinternal, hactive] using
            hspec.1.append hclosureSpec.2
        have hne :
            canonicalFrontierEventBatch compiled guards
              state action dst ≠ [] := by
          have hselectedNe :
              selectedCommitEvents compiled action.1 ≠ [] :=
            selectedCommitEvents_ne_nil_of_active
              compiled action.2 hactive
          intro hnil
          have hselectedNil :
              selectedCommitEvents compiled action.1 = [] :=
            (List.eq_nil_of_append_eq_nil
              (by
                simpa [canonicalFrontierEventBatch, hinternal,
                  hactive] using hnil)).1
          exact hselectedNe hselectedNil
        exact
          { realizesAction := hrealizes
            availableRun := hrun
            allowed :=
              FrontierCheckpointAllowed.strategic
                hinternal hactive action hsupportMem }
      · let hactiveEmpty := active_eq_empty_of_not_nonempty
          compiled hactive
        exact False.elim
          (no_ready_internal_no_active_impossible
            compiled guards action.2.1 hinternal hactiveEmpty)

/-- Every supported default frontier transition lands at an internal-closed
checkpoint. -/
theorem canonicalFrontierRoundSemantics_transition_support_closed
    (compiled : CompiledProgram P L)
    (guards : EventGraph.GuardLive compiled.graph)
    {state dst : (PrimitiveMachine compiled).State}
    (action :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a})
    (hsupport :
      (canonicalFrontierRoundSemantics compiled guards).transition
        state action dst ≠ 0) :
    EventGraph.readyInternalNodes compiled.graph dst.1 = ∅ := by
  classical
  change canonicalFrontierTransition compiled guards
    state action dst ≠ 0 at hsupport
  by_cases hinternal :
      (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty
  · have hsupportMem :
        dst ∈ (internalClosureAfterReady compiled state).support :=
      (PMF.mem_support_iff _ _).2 (by
        simpa [canonicalFrontierTransition, hinternal] using hsupport)
    exact internalClosureAfterReady_support_closed compiled hsupportMem
  · by_cases hactive : (frontierActive compiled state).Nonempty
    · have hsupportMem :
          dst ∈
            (selectedCommitClosureTransition
              compiled action hactive).support :=
        (PMF.mem_support_iff _ _).2 (by
          simpa [canonicalFrontierTransition, hinternal, hactive]
            using hsupport)
      exact selectedCommitClosure_support_closed
        compiled action hactive hsupportMem
    · let hactiveEmpty := active_eq_empty_of_not_nonempty
        compiled hactive
      exact False.elim
        (no_ready_internal_no_active_impossible
          compiled guards action.2.1 hinternal hactiveEmpty)

/-- Certified bounded pure-strategy kernel game induced by a compiled event
graph's frontier round view.

The wrapper keeps the frontier-round semantics together with the `KernelGame`,
so operational trace soundness is not lost when passing the strategic game
object downstream. -/
structure FrontierPureKernelGame
    (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph) where
  private mk ::
  semantics : FrontierRoundSemantics compiled presentation
  horizon : Nat
  steps : Nat
  cutoff : Payoff P
  game : KernelGame P

/-- Build a certified bounded pure-strategy kernel game. The cutoff utility is
used only for bounded executions that stop before a terminal machine outcome. -/
noncomputable def frontierPureKernelGame
    (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph)
    (semantics : FrontierRoundSemantics compiled presentation)
    (horizon steps : Nat)
    [∀ node : Fin compiled.graph.nodeCount,
      Fintype (L.Val (compiled.graph.nodeRow node).ty)]
    (cutoff : Payoff P) :
    FrontierPureKernelGame compiled presentation := by
  classical
  let view := frontierRoundView compiled presentation semantics
  letI : ∀ player, Fintype (Option (view.Act player)) := by
    intro player
    dsimp [view, frontierRoundView, EventGraph.frontierRoundView]
    infer_instance
  exact
    { semantics := semantics
      horizon := horizon
      steps := steps
      cutoff := cutoff
      game := view.boundedPureKernelGame horizon steps cutoff }

/-- The natural round bound for a strict-downset frontier presentation.

Every supported nonterminal frontier round strictly increases the completed
node downset, so `nodeCount` rounds are enough for the default completed-game
presentation. -/
def completionBound (compiled : CompiledProgram P L) : Nat :=
  compiled.graph.nodeCount

/-- Cutoff utility for bounded option-outcome games.

Default completed frontier games use `completionBound` and erase this branch
with support-totality proofs. -/
def unreachableCutoff : Payoff P :=
  fun _ => 0

/-- Compile a finite checked program and build its certified bounded
pure-strategy frontier kernel game. The returned artifact is graph-based; the
source program is used only to derive the compiled graph and finite node value
domains. -/
noncomputable def frontierPureKernelGameOfProgram
    (program : WFProgram P L) [FiniteDomains program]
    (presentation :
      EventGraph.CheckpointPresentation
        (ToEventGraph.compile program.core).graph)
    (semantics :
      FrontierRoundSemantics (ToEventGraph.compile program.core)
        presentation)
    (horizon steps : Nat)
    (cutoff : Payoff P) :
    FrontierPureKernelGame (ToEventGraph.compile program.core) presentation := by
  classical
  letI :
      ∀ node : Fin (ToEventGraph.compile program.core).graph.nodeCount,
        Fintype (L.Val
          (((ToEventGraph.compile program.core).graph.nodeRow node).ty)) :=
    ToEventGraph.compile_nodeFintype program
  exact
    frontierPureKernelGame
      (ToEventGraph.compile program.core)
      presentation semantics horizon steps cutoff

/-- Bounded option-outcome pure-strategy frontier kernel game for a finite
checked program, using the canonical frontier checkpoint presentation.

This is the raw bounded game underneath the completed API. Its outcome type is
`Option`, with `none` representing the unreachable cutoff branch. -/
noncomputable def optionFrontierPureKernelGame
    (program : WFProgram P L) [FiniteDomains program] :
    FrontierPureKernelGame (ToEventGraph.compile program.core)
      (frontierPresentation
        (ToEventGraph.compile program.core)
        (ToEventGraph.compile_guardLive program)) :=
  let compiled := ToEventGraph.compile program.core
  frontierPureKernelGameOfProgram program
    (frontierPresentation
      compiled
      (ToEventGraph.compile_guardLive program))
    (canonicalFrontierRoundSemantics
      compiled
      (ToEventGraph.compile_guardLive program))
    (completionBound compiled) (completionBound compiled) unreachableCutoff

/-- Certified bounded behavioral-strategy kernel game induced by a compiled
event graph's frontier round view. -/
structure FrontierBehavioralKernelGame
    (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph) where
  private mk ::
  semantics : FrontierRoundSemantics compiled presentation
  horizon : Nat
  steps : Nat
  cutoff : Payoff P
  game : KernelGame P

/-- Build a certified bounded behavioral-strategy kernel game. The cutoff
utility is used only for bounded executions that stop before a terminal machine
outcome. -/
noncomputable def frontierBehavioralKernelGame
    (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph)
    (semantics : FrontierRoundSemantics compiled presentation)
    (horizon steps : Nat)
    [∀ node : Fin compiled.graph.nodeCount,
      Fintype (L.Val (compiled.graph.nodeRow node).ty)]
    (cutoff : Payoff P) :
    FrontierBehavioralKernelGame compiled presentation := by
  classical
  let view := frontierRoundView compiled presentation semantics
  letI : ∀ player, Fintype (Option (view.Act player)) := by
    intro player
    dsimp [view, frontierRoundView, EventGraph.frontierRoundView]
    infer_instance
  exact
    { semantics := semantics
      horizon := horizon
      steps := steps
      cutoff := cutoff
      game := view.boundedBehavioralKernelGame horizon steps cutoff }

/-- Compile a finite checked program and build its certified bounded
behavioral-strategy frontier kernel game. The returned artifact is graph-based;
the source program is used only to derive the compiled graph and finite node
value domains. -/
noncomputable def frontierBehavioralKernelGameOfProgram
    (program : WFProgram P L) [FiniteDomains program]
    (presentation :
      EventGraph.CheckpointPresentation
        (ToEventGraph.compile program.core).graph)
    (semantics :
      FrontierRoundSemantics (ToEventGraph.compile program.core)
        presentation)
    (horizon steps : Nat)
    (cutoff : Payoff P) :
    FrontierBehavioralKernelGame
      (ToEventGraph.compile program.core) presentation := by
  classical
  letI :
      ∀ node : Fin (ToEventGraph.compile program.core).graph.nodeCount,
        Fintype (L.Val
          (((ToEventGraph.compile program.core).graph.nodeRow node).ty)) :=
    ToEventGraph.compile_nodeFintype program
  exact
    frontierBehavioralKernelGame
      (ToEventGraph.compile program.core)
      presentation semantics horizon steps cutoff

/-- Bounded option-outcome behavioral-strategy frontier kernel game for a
finite checked program, using the canonical frontier checkpoint presentation.

This is the raw bounded game underneath the completed API. Its outcome type is
`Option`, with `none` representing the unreachable cutoff branch. -/
noncomputable def optionFrontierBehavioralKernelGame
    (program : WFProgram P L) [FiniteDomains program] :
    FrontierBehavioralKernelGame (ToEventGraph.compile program.core)
      (frontierPresentation
        (ToEventGraph.compile program.core)
        (ToEventGraph.compile_guardLive program)) :=
  let compiled := ToEventGraph.compile program.core
  frontierBehavioralKernelGameOfProgram program
    (frontierPresentation
      compiled
      (ToEventGraph.compile_guardLive program))
    (canonicalFrontierRoundSemantics
      compiled
      (ToEventGraph.compile_guardLive program))
    (completionBound compiled) (completionBound compiled) unreachableCutoff

namespace FrontierRoundSemantics

variable {compiled : CompiledProgram P L}
variable {presentation : EventGraph.CheckpointPresentation compiled.graph}

private noncomputable abbrev View
    (semantics : FrontierRoundSemantics compiled presentation) :
    (PrimitiveMachine compiled).RoundView :=
  frontierRoundView compiled presentation semantics

private theorem boundedStep_transition_support
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (step : (View semantics).BoundedStep horizon) :
    (View semantics).transition step.src.state
        ((View semantics).boundedActionToAction horizon step.src step.act)
        step.dst.state ≠ 0 := by
  classical
  let view := View semantics
  have hmem :
      step.dst ∈
        (view.boundedTransition horizon step.src step.act).support := by
    exact (PMF.mem_support_iff _ _).2 step.support
  rw [Machine.RoundView.boundedTransition] at hmem
  rcases (PMF.mem_support_map_iff _ _ _).mp hmem with
    ⟨next, hnext, hdst⟩
  have hstate : next = step.dst.state := by
    simpa [Machine.BoundedState.succ] using congrArg
      (fun bounded : (PrimitiveMachine compiled).BoundedState horizon =>
        bounded.state) hdst
  rw [← hstate]
  exact (PMF.mem_support_iff _ _).1 hnext

private theorem boundedStep_eventBatch_eq_semantics
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (step : (View semantics).BoundedStep horizon) :
    (View semantics).eventBatch step.src.state step.act.1 step.dst.state =
      semantics.eventBatch step.src.state
        ((View semantics).boundedActionToAction horizon step.src step.act)
        step.dst.state := by
  classical
  let action :=
    (View semantics).boundedActionToAction horizon step.src step.act
  change
    (if hlegal :
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) step.src.state step.act.1 then
      semantics.eventBatch step.src.state ⟨step.act.1, hlegal⟩
        step.dst.state
    else []) =
      semantics.eventBatch step.src.state action step.dst.state
  have hlegal :
      JointActionLegal (FrontierAct compiled)
        (frontierActive compiled)
        (PrimitiveMachine compiled).terminal
        (frontierAvailableActions compiled) step.src.state step.act.1 := by
    simpa [action, View, frontierRoundView]
      using action.2
  rw [dif_pos hlegal]
  have haction :
      (⟨step.act.1, hlegal⟩ :
        {a : JointAction (FrontierAct compiled) //
          JointActionLegal (FrontierAct compiled)
            (frontierActive compiled)
            (PrimitiveMachine compiled).terminal
            (frontierAvailableActions compiled) step.src.state a}) =
        action := by
    exact Subtype.ext rfl
  exact congrArg
    (fun legalAction =>
      semantics.eventBatch step.src.state legalAction step.dst.state)
    haction

/-- The primitive event batch recorded by a supported bounded frontier round
really is an available primitive machine run from the source checkpoint to the
destination checkpoint. -/
theorem boundedStep_eventBatch_availableRun
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (step : (View semantics).BoundedStep horizon) :
    (PrimitiveMachine compiled).AvailableRunFrom step.src.state
      ((View semantics).eventBatch step.src.state step.act.1 step.dst.state)
      step.dst.state := by
  rw [boundedStep_eventBatch_eq_semantics semantics step]
  exact
    (semantics.certifies
      ((View semantics).boundedActionToAction horizon step.src step.act)
      (boundedStep_transition_support semantics step)).availableRun

/-- The frontier round view is operationally certified: every supported
strategic round transition records a primitive event batch that replays that
transition on the underlying protocol machine. -/
theorem view_operationallyCertified
    (semantics : FrontierRoundSemantics compiled presentation) :
    (View semantics).OperationallyCertified := by
  classical
  intro state action dst hsupport
  let hlegal :
      JointActionLegal (FrontierAct compiled)
        (frontierActive compiled)
        (PrimitiveMachine compiled).terminal
        (frontierAvailableActions compiled) state action.1 := by
    simpa [View, frontierRoundView] using action.2
  let action' :
      {a : JointAction (FrontierAct compiled) //
        JointActionLegal (FrontierAct compiled)
          (frontierActive compiled)
          (PrimitiveMachine compiled).terminal
          (frontierAvailableActions compiled) state a} :=
    ⟨action.1, hlegal⟩
  have hbatch :
      (View semantics).eventBatch state action.1 dst =
        semantics.eventBatch state action' dst := by
    change
      (if hlegal :
          JointActionLegal (FrontierAct compiled)
            (frontierActive compiled)
            (PrimitiveMachine compiled).terminal
            (frontierAvailableActions compiled) state action.1 then
        semantics.eventBatch state ⟨action.1, hlegal⟩ dst
      else []) =
        semantics.eventBatch state action' dst
    rw [dif_pos hlegal]
    rfl
  have hsupport' : semantics.transition state action' dst ≠ 0 := by
    simpa [View, frontierRoundView, action'] using hsupport
  rw [hbatch]
  exact (semantics.certifies action' hsupport').availableRun

/-- The primitive event batch recorded by a supported bounded frontier round
faithfully contains the strategic commit choices selected by that round's
joint action. -/
theorem boundedStep_eventBatch_realizesAction
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (step : (View semantics).BoundedStep horizon) :
    FrontierBatchRealizesAction compiled step.act.1
      ((View semantics).eventBatch step.src.state step.act.1
        step.dst.state) := by
  rw [boundedStep_eventBatch_eq_semantics semantics step]
  exact
    (semantics.certifies
      ((View semantics).boundedActionToAction horizon step.src step.act)
      (boundedStep_transition_support semantics step)).realizesAction

/-- The recorded primitive event batch for a supported bounded frontier round
is also a graph-level checkpoint batch certificate. -/
theorem boundedStep_checkpointStep
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (step : (View semantics).BoundedStep horizon) :
    EventGraph.CheckpointStep compiled.graph
      step.src.state step.dst.state :=
  EventGraph.ToMachine.checkpointStep_of_availableRunFrom
    (primitiveMachineSpec compiled)
    (boundedStep_eventBatch_availableRun semantics step)

/-- Every supported bounded frontier round follows the attached checkpoint
presentation policy. -/
theorem boundedStep_allowed
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (step : (View semantics).BoundedStep horizon) :
    presentation.policy.allowed step.src.state step.dst.state := by
  exact
    (semantics.certifies
      ((View semantics).boundedActionToAction horizon step.src step.act)
      (boundedStep_transition_support semantics step)).allowed

/-- Every supported bounded frontier round strictly advances the completed-node
downset of the underlying graph state. -/
theorem boundedStep_done_ssubset
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (step : (View semantics).BoundedStep horizon) :
    step.src.state.1.done ⊂ step.dst.state.1.done :=
  presentation.policy.advances
    (boundedStep_allowed semantics step)

private theorem stepChain_done_card_add_length_le
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat} :
    ∀ {start : (PrimitiveMachine compiled).BoundedState horizon}
      {steps : List ((View semantics).BoundedStep horizon)},
      (View semantics).StepChainFrom horizon start steps →
        start.state.1.done.card + steps.length ≤
          ((View semantics).lastStateFrom horizon start steps).state.1.done.card
  | start, [], _hchain => by
      simp [Machine.RoundView.lastStateFrom]
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      subst hsrc
      have hhead :
          step.src.state.1.done.card + 1 ≤
            step.dst.state.1.done.card :=
        Nat.succ_le_of_lt
          (Finset.card_lt_card
            (boundedStep_done_ssubset semantics step))
      have htailCard :
          step.dst.state.1.done.card + steps.length ≤
            ((View semantics).lastStateFrom horizon step.dst
              steps).state.1.done.card :=
        stepChain_done_card_add_length_le semantics htail
      simp [Machine.RoundView.lastStateFrom]
      omega

/-- A certified frontier history with one round per graph node must be
terminal. The proof uses only strict completed-downset progress; it is the
history-level totality fact behind the default `completionBound`. -/
theorem boundedHistory_terminal_of_length_completionBound
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (history : (View semantics).BoundedHistory horizon)
    (hlen : history.steps.length = completionBound compiled) :
    EventGraph.Terminal compiled.graph history.lastState.state.1 := by
  have hcardGe :
      compiled.graph.nodeCount ≤ history.lastState.state.1.done.card := by
    have hchain :=
      stepChain_done_card_add_length_le
        semantics history.chain
    have hinit :
        ((Machine.BoundedState.init
          (PrimitiveMachine compiled) horizon).state.1.done.card) = 0 := by
      simp [Machine.BoundedState.init,
        EventGraph.ToMachine.primitiveMachine, EventGraph.Config.initial]
    rw [← Machine.RoundView.BoundedHistory.lastState] at hchain
    rw [hinit, hlen] at hchain
    simpa [completionBound] using hchain
  have hcardLe :
      history.lastState.state.1.done.card ≤ compiled.graph.nodeCount := by
    calc
      history.lastState.state.1.done.card ≤
          (Finset.univ :
            Finset (Fin compiled.graph.nodeCount)).card :=
        Finset.card_le_card (by intro node _hnode; simp)
      _ = compiled.graph.nodeCount := by simp
  have hcard :
      history.lastState.state.1.done.card =
        (Finset.univ : Finset (Fin compiled.graph.nodeCount)).card := by
    apply le_antisymm
    · simpa using hcardLe
    · simpa using hcardGe
  have hdone :
      history.lastState.state.1.done =
        (Finset.univ : Finset (Fin compiled.graph.nodeCount)) := by
    apply Finset.eq_univ_of_card
    exact hcard
  intro node
  rw [hdone]
  exact Finset.mem_univ node

/-- Any supported default-length run of a certified frontier view ends in a
graph-terminal checkpoint. If the bounded runner stops early, it stopped at a
real machine terminal state; if it uses all bounded rounds, strict downset
progress completes every graph node. -/
theorem runDist_support_terminal_of_completionBound
    (semantics : FrontierRoundSemantics compiled presentation)
    [∀ player, Fintype (Option ((View semantics).Act player))]
    (β :
      (View semantics).BoundedBehavioralProfile
        (completionBound compiled))
    {history :
      (View semantics).BoundedHistory (completionBound compiled)}
    (hsupport :
      history ∈
        ((View semantics).runDist
          (completionBound compiled) (completionBound compiled) β).support) :
    EventGraph.Terminal compiled.graph history.lastState.state.1 := by
  classical
  have hterminalOrLength :=
    Machine.RoundView.BoundedHistory.runDistFrom_support_terminal_or_length_ge
        (View semantics) (completionBound compiled) β
        (completionBound compiled)
        (Machine.RoundView.BoundedHistory.nil
          (View semantics) (completionBound compiled))
        history
        (by
          simpa [Machine.RoundView.runDist] using hsupport)
  rcases hterminalOrLength with hboundedTerminal | hlengthGe
  · rcases hboundedTerminal with hmachineTerminal | hdepth
    · change EventGraph.Terminal compiled.graph
        history.lastState.state.1 at hmachineTerminal
      exact hmachineTerminal
    · have hlenGe :
          completionBound compiled ≤ history.steps.length := by
        rw [← (View semantics).history_depth
          (completionBound compiled) history]
        exact hdepth
      have hlenLe :
          history.steps.length ≤ completionBound compiled :=
        (View semantics).history_length_le
          (completionBound compiled) history
      exact
        boundedHistory_terminal_of_length_completionBound
          semantics history (le_antisymm hlenLe hlenGe)
  · have hlenGe :
        completionBound compiled ≤ history.steps.length := by
      simpa using hlengthGe
    have hlenLe :
        history.steps.length ≤ completionBound compiled :=
      (View semantics).history_length_le
        (completionBound compiled) history
    exact
      boundedHistory_terminal_of_length_completionBound
        semantics history (le_antisymm hlenLe hlenGe)

/-- Default-length behavioral outcome kernels for certified frontier views
never support `none`. -/
theorem boundedOutcomeFromBehavioral_support_some_completionBound
    (semantics : FrontierRoundSemantics compiled presentation)
    [∀ player, Fintype (Option ((View semantics).Act player))]
    (β :
      (View semantics).BoundedBehavioralProfile
        (completionBound compiled))
    {result : Option (PrimitiveMachine compiled).Outcome}
    (hsupport :
      result ∈
        ((View semantics).boundedOutcomeFromBehavioral
          (completionBound compiled) β
          (completionBound compiled)).support) :
    ∃ outcome, result = some outcome := by
  classical
  rcases (PMF.mem_support_map_iff _ _ _).mp hsupport with
    ⟨trace, htrace, hresult⟩
  rcases (PMF.mem_support_map_iff _ _ _).mp htrace with
    ⟨history, hhistory, htraceEq⟩
  have hterminal :
      EventGraph.Terminal compiled.graph history.lastState.state.1 :=
    runDist_support_terminal_of_completionBound
      semantics β (by
        simpa [Machine.RoundView.boundedEventBatchTraceFromBehavioral]
          using hhistory)
  have hresultEq :
      (PrimitiveMachine compiled).outcome history.lastState.state = result := by
    rw [← htraceEq] at hresult
    simpa [Machine.RoundView.boundedHistoryTrace] using hresult
  rcases EventGraph.ToMachine.terminalPayoffTotal
      (primitiveMachineSpec compiled) history.lastState.state hterminal with
    ⟨outcome, houtcomeEval⟩
  have houtcome :
      (PrimitiveMachine compiled).outcome history.lastState.state =
        some outcome := by
    rw [EventGraph.ToMachine.primitiveMachine_outcome_terminal
      (primitiveMachineSpec compiled) hterminal]
    exact houtcomeEval
  rw [houtcome] at hresultEq
  exact ⟨outcome, hresultEq.symm⟩

/-- Default-length pure outcome kernels for certified frontier views never
support `none`. -/
theorem boundedOutcomeFromPure_support_some_completionBound
    (semantics : FrontierRoundSemantics compiled presentation)
    [∀ player, Fintype (Option ((View semantics).Act player))]
    (π :
      (View semantics).BoundedPureProfile
        (completionBound compiled))
    {result : Option (PrimitiveMachine compiled).Outcome}
    (hsupport :
      result ∈
        ((View semantics).boundedOutcomeFromPure
          (completionBound compiled) π
          (completionBound compiled)).support) :
    ∃ outcome, result = some outcome := by
  simpa [Machine.RoundView.boundedOutcomeFromPure] using
    boundedOutcomeFromBehavioral_support_some_completionBound
      semantics
      ((View semantics).legalPureToBehavioral
        (completionBound compiled) π)
      hsupport

private theorem stepChain_eventBatches_availableRun
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat} :
    ∀ {start : (PrimitiveMachine compiled).BoundedState horizon}
      {steps : List ((View semantics).BoundedStep horizon)},
      (View semantics).StepChainFrom horizon start steps →
        (PrimitiveMachine compiled).AvailableRunBatchesFrom start.state
          (steps.map fun step =>
            (View semantics).eventBatch step.src.state step.act.1
              step.dst.state)
          ((View semantics).lastStateFrom horizon start steps).state
  | start, [], _hchain => by
      exact .nil start.state
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      have hhead :
          (PrimitiveMachine compiled).AvailableRunFrom start.state
            ((View semantics).eventBatch step.src.state step.act.1
              step.dst.state)
            step.dst.state := by
        subst hsrc
        exact boundedStep_eventBatch_availableRun semantics step
      have htailRun :
          (PrimitiveMachine compiled).AvailableRunBatchesFrom step.dst.state
            (steps.map fun step =>
              (View semantics).eventBatch step.src.state step.act.1
                step.dst.state)
            ((View semantics).lastStateFrom horizon step.dst steps).state :=
        stepChain_eventBatches_availableRun semantics htail
      exact .cons hhead htailRun

private noncomputable def stepChain_checkpointHistory
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat} :
    ∀ {start : (PrimitiveMachine compiled).BoundedState horizon}
      {steps : List ((View semantics).BoundedStep horizon)},
      (View semantics).StepChainFrom horizon start steps →
        presentation.History start.state
          ((View semantics).lastStateFrom horizon start steps).state
  | start, [], _hchain => by
      exact .nil start.state
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      subst hsrc
      let head : presentation.History step.src.state step.dst.state :=
        .snoc (.nil step.src.state) (boundedStep_allowed semantics step)
      let tail : presentation.History step.dst.state
          ((View semantics).lastStateFrom horizon step.dst steps).state :=
        stepChain_checkpointHistory semantics htail
      exact head.append tail

private theorem stepChain_checkpointHistory_publicView
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat} :
    ∀ {start : (PrimitiveMachine compiled).BoundedState horizon}
      {steps : List ((View semantics).BoundedStep horizon)}
      (hchain : (View semantics).StepChainFrom horizon start steps),
        (stepChain_checkpointHistory semantics hchain).publicView =
          Machine.RoundView.BoundedHistory.publicViewFrom
            (view := View semantics) steps
  | start, [], _hchain => by
      change
        (EventGraph.CheckpointPresentation.History.nil
          (view := presentation) start.state).publicView = []
      unfold EventGraph.CheckpointPresentation.History.publicView
      rfl
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      subst hsrc
      have ih := stepChain_checkpointHistory_publicView semantics htail
      simpa [stepChain_checkpointHistory,
        EventGraph.CheckpointPresentation.History.publicView_append,
        EventGraph.CheckpointPresentation.History.publicView,
        Machine.RoundView.BoundedHistory.publicViewFrom,
        Machine.RoundView.BoundedStep.publicObs,
        frontierRoundView, EventGraph.frontierRoundView,
        EventGraph.ToMachine.primitiveMachine, primitiveMachineSpec] using ih

private theorem stepChain_checkpointHistory_playerView
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat} (player : P) :
    ∀ {start : (PrimitiveMachine compiled).BoundedState horizon}
      {steps : List ((View semantics).BoundedStep horizon)}
      (hchain : (View semantics).StepChainFrom horizon start steps),
        (stepChain_checkpointHistory semantics hchain).playerView player =
          steps.map fun step => step.privateObs player
  | start, [], _hchain => by
      change
        (EventGraph.CheckpointPresentation.History.nil
          (view := presentation) start.state).playerView player = []
      unfold EventGraph.CheckpointPresentation.History.playerView
      rfl
  | start, step :: steps, hchain => by
      rcases hchain with ⟨hsrc, htail⟩
      subst hsrc
      have ih := stepChain_checkpointHistory_playerView
        semantics player htail
      simpa [stepChain_checkpointHistory,
        EventGraph.CheckpointPresentation.History.playerView_append,
        EventGraph.CheckpointPresentation.History.playerView,
        Machine.RoundView.BoundedStep.privateObs,
        frontierRoundView, EventGraph.frontierRoundView,
        EventGraph.ToMachine.primitiveMachine, primitiveMachineSpec] using ih

/-- Event batches extracted from a bounded frontier history form an available
primitive batched machine run from the initial checkpoint to the history's
endpoint. -/
theorem boundedHistory_eventBatches_availableRun
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (history : (View semantics).BoundedHistory horizon) :
    (PrimitiveMachine compiled).AvailableRunBatchesFrom
      ((Machine.BoundedState.init (PrimitiveMachine compiled) horizon).state)
      ((View semantics).boundedHistoryEventBatches horizon history)
      history.lastState.state := by
  exact stepChain_eventBatches_availableRun semantics history.chain

/-- A supported default-length behavioral outcome has a concrete supported
bounded history behind it. The witness carries the operational facts needed by
adequacy theorems: available primitive batches, terminality, and agreement with
the primitive machine outcome. -/
theorem boundedOutcomeFromBehavioral_support_history_completionBound
    (semantics : FrontierRoundSemantics compiled presentation)
    [∀ player, Fintype (Option ((View semantics).Act player))]
    (β :
      (View semantics).BoundedBehavioralProfile
        (completionBound compiled))
    {outcome : (PrimitiveMachine compiled).Outcome}
    (hsupport :
      some outcome ∈
        ((View semantics).boundedOutcomeFromBehavioral
          (completionBound compiled) β
          (completionBound compiled)).support) :
    ∃ history :
        (View semantics).BoundedHistory (completionBound compiled),
      history ∈
        ((View semantics).runDist
          (completionBound compiled) (completionBound compiled) β).support ∧
      EventGraph.Terminal compiled.graph history.lastState.state.1 ∧
      (PrimitiveMachine compiled).outcome history.lastState.state =
        some outcome ∧
      (PrimitiveMachine compiled).AvailableRunBatchesFrom
        ((Machine.BoundedState.init
          (PrimitiveMachine compiled) (completionBound compiled)).state)
        ((View semantics).boundedHistoryEventBatches
          (completionBound compiled) history)
        history.lastState.state := by
  classical
  rcases (PMF.mem_support_map_iff _ _ _).mp hsupport with
    ⟨trace, htrace, hresult⟩
  rcases (PMF.mem_support_map_iff _ _ _).mp htrace with
    ⟨history, hhistory, htraceEq⟩
  have hterminal :
      EventGraph.Terminal compiled.graph history.lastState.state.1 :=
    runDist_support_terminal_of_completionBound
      semantics β (by
        simpa [Machine.RoundView.boundedEventBatchTraceFromBehavioral]
          using hhistory)
  have houtcome :
      (PrimitiveMachine compiled).outcome history.lastState.state =
        some outcome := by
    rw [← htraceEq] at hresult
    simpa [Machine.RoundView.boundedHistoryTrace] using hresult
  exact
    ⟨history, hhistory, hterminal, houtcome,
      boundedHistory_eventBatches_availableRun semantics history⟩

/-- Pure-strategy version of
`boundedOutcomeFromBehavioral_support_history_completionBound`. Pure runs are
the corresponding point-mass behavioral runs. -/
theorem boundedOutcomeFromPure_support_history_completionBound
    (semantics : FrontierRoundSemantics compiled presentation)
    [∀ player, Fintype (Option ((View semantics).Act player))]
    (π :
      (View semantics).BoundedPureProfile
        (completionBound compiled))
    {outcome : (PrimitiveMachine compiled).Outcome}
    (hsupport :
      some outcome ∈
        ((View semantics).boundedOutcomeFromPure
          (completionBound compiled) π
          (completionBound compiled)).support) :
    ∃ history :
        (View semantics).BoundedHistory (completionBound compiled),
      history ∈
        ((View semantics).runDist
          (completionBound compiled) (completionBound compiled)
          ((View semantics).legalPureToBehavioral
            (completionBound compiled) π)).support ∧
      EventGraph.Terminal compiled.graph history.lastState.state.1 ∧
      (PrimitiveMachine compiled).outcome history.lastState.state =
        some outcome ∧
      (PrimitiveMachine compiled).AvailableRunBatchesFrom
        ((Machine.BoundedState.init
          (PrimitiveMachine compiled) (completionBound compiled)).state)
        ((View semantics).boundedHistoryEventBatches
          (completionBound compiled) history)
        history.lastState.state := by
  simpa [Machine.RoundView.boundedOutcomeFromPure] using
    boundedOutcomeFromBehavioral_support_history_completionBound
      semantics
      ((View semantics).legalPureToBehavioral
        (completionBound compiled) π)
      hsupport

/-- Every bounded frontier-round history induces a checkpoint history in the
attached checkpoint presentation. This is the bridge from strategic round
histories back to schedule-agnostic checkpoint histories. -/
noncomputable def boundedHistory_checkpointHistory
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (history : (View semantics).BoundedHistory horizon) :
    presentation.History
      ((Machine.BoundedState.init (PrimitiveMachine compiled) horizon).state)
      history.lastState.state := by
  simpa [Machine.RoundView.BoundedHistory.lastState] using
    stepChain_checkpointHistory semantics history.chain

/-- The checkpoint history induced by a bounded frontier history has exactly
the same public observations as the bounded round history. -/
theorem boundedHistory_checkpointHistory_publicView
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (history : (View semantics).BoundedHistory horizon) :
    (boundedHistory_checkpointHistory semantics history).publicView =
      history.publicView := by
  simpa [boundedHistory_checkpointHistory,
    Machine.RoundView.BoundedHistory.publicView] using
    stepChain_checkpointHistory_publicView semantics history.chain

/-- The checkpoint history induced by a bounded frontier history has exactly
the private observations carried by the bounded round information state. -/
theorem boundedHistory_checkpointHistory_playerView
    (semantics : FrontierRoundSemantics compiled presentation)
    {horizon : Nat}
    (history : (View semantics).BoundedHistory horizon)
    (player : P) :
    (boundedHistory_checkpointHistory semantics history).playerView player =
      (Machine.RoundView.InfoState.observationEvents
        (history.playerView player)).map Prod.fst := by
  change
    (stepChain_checkpointHistory semantics history.chain).playerView player =
      (Machine.RoundView.InfoState.observationEvents
        (history.playerView player)).map Prod.fst
  rw [stepChain_checkpointHistory_playerView semantics player history.chain]
  rw [Machine.RoundView.BoundedHistory.playerView]
  rw [Machine.RoundView.BoundedHistory.observationEvents_playerViewFrom]
  simp [Function.comp_def]

end FrontierRoundSemantics

/-- The default-length pure frontier kernel constructed from certified
frontier semantics never supports the cutoff outcome. -/
theorem frontierPureKernelGame_outcomeKernel_support_some_completionBound
    (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph)
    (semantics : FrontierRoundSemantics compiled presentation)
    [∀ node : Fin compiled.graph.nodeCount,
      Fintype (L.Val (compiled.graph.nodeRow node).ty)]
    (cutoff : Payoff P)
    (σ :
      (frontierPureKernelGame compiled presentation semantics
        (completionBound compiled) (completionBound compiled)
        cutoff).game.Profile)
    {result : Option (PrimitiveMachine compiled).Outcome}
    (hsupport :
      result ∈
        ((frontierPureKernelGame compiled presentation semantics
          (completionBound compiled) (completionBound compiled)
          cutoff).game.outcomeKernel σ).support) :
    ∃ outcome, result = some outcome := by
  classical
  let view := frontierRoundView compiled presentation semantics
  letI : ∀ player, Fintype (Option (view.Act player)) := by
    intro player
    dsimp [view, frontierRoundView, EventGraph.frontierRoundView]
    infer_instance
  exact
    FrontierRoundSemantics.boundedOutcomeFromPure_support_some_completionBound
      semantics σ (by
        simpa [frontierPureKernelGame,
          Machine.RoundView.boundedPureKernelGame, view] using hsupport)

/-- The default-length behavioral frontier kernel constructed from certified
frontier semantics never supports the cutoff outcome. -/
theorem frontierBehavioralKernelGame_outcomeKernel_support_some_completionBound
    (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph)
    (semantics : FrontierRoundSemantics compiled presentation)
    [∀ node : Fin compiled.graph.nodeCount,
      Fintype (L.Val (compiled.graph.nodeRow node).ty)]
    (cutoff : Payoff P)
    (σ :
      (frontierBehavioralKernelGame compiled presentation semantics
        (completionBound compiled) (completionBound compiled)
        cutoff).game.Profile)
    {result : Option (PrimitiveMachine compiled).Outcome}
    (hsupport :
      result ∈
        ((frontierBehavioralKernelGame compiled presentation semantics
          (completionBound compiled) (completionBound compiled)
          cutoff).game.outcomeKernel σ).support) :
    ∃ outcome, result = some outcome := by
  classical
  let view := frontierRoundView compiled presentation semantics
  letI : ∀ player, Fintype (Option (view.Act player)) := by
    intro player
    dsimp [view, frontierRoundView, EventGraph.frontierRoundView]
    infer_instance
  exact
    FrontierRoundSemantics.boundedOutcomeFromBehavioral_support_some_completionBound
      semantics σ (by
        simpa [frontierBehavioralKernelGame,
          Machine.RoundView.boundedBehavioralKernelGame, view] using hsupport)

omit [Fintype P] in
/-- Erase an option-valued outcome distribution when `none` has no support. -/
noncomputable def eraseNonePMF {α : Type}
    (dist : PMF (Option α))
    (htotal : ∀ result ∈ dist.support, ∃ value, result = some value) :
    PMF α :=
  dist.bindOnSupport fun result hresult =>
    match result with
    | some value => PMF.pure value
    | none =>
        False.elim <| by
          rcases htotal none hresult with ⟨value, hvalue⟩
          cases hvalue

omit [Fintype P] in
theorem mem_support_eraseNonePMF_iff {α : Type}
    {dist : PMF (Option α)}
    {htotal : ∀ result ∈ dist.support, ∃ value, result = some value}
    {value : α} :
    value ∈ (eraseNonePMF dist htotal).support ↔
      some value ∈ dist.support := by
  unfold eraseNonePMF
  rw [PMF.mem_support_bindOnSupport_iff]
  constructor
  · rintro ⟨result, hresult, hvalue⟩
    cases result with
    | none =>
        rcases htotal none hresult with ⟨witness, hwitness⟩
        cases hwitness
    | some witness =>
        rw [PMF.support_pure, Set.mem_singleton_iff] at hvalue
        simpa [hvalue] using hresult
  · intro hsome
    exact ⟨some value, hsome, by simp [PMF.support_pure]⟩

omit [Fintype P] in
theorem eraseNonePMF_apply {α : Type}
    {dist : PMF (Option α)}
    {htotal : ∀ result ∈ dist.support, ∃ value, result = some value}
    (value : α) :
    eraseNonePMF dist htotal value = dist (some value) := by
  unfold eraseNonePMF
  rw [PMF.bindOnSupport_apply]
  rw [tsum_eq_single (some value)]
  · by_cases hzero : dist (some value) = 0
    · simp [hzero]
    · simp [hzero, PMF.pure_apply]
  · intro result hne
    cases result with
    | none =>
        by_cases hzero : dist none = 0
        · simp [hzero]
        · have hsupport : none ∈ dist.support :=
            (PMF.mem_support_iff _ _).2 hzero
          rcases htotal none hsupport with ⟨witness, hwitness⟩
          cases hwitness
    | some witness =>
        by_cases hzero : dist (some witness) = 0
        · simp [hzero]
        · have hvalue : value ≠ witness := by
            intro heq
            subst heq
            exact hne rfl
          simp [hzero, PMF.pure_apply, hvalue]

omit [Fintype P] in
theorem eraseNonePMF_map_some {α : Type}
    {dist : PMF (Option α)}
    {htotal : ∀ result ∈ dist.support, ∃ value, result = some value} :
    PMF.map some (eraseNonePMF dist htotal) = dist := by
  apply PMF.ext
  intro result
  cases result with
  | none =>
      rw [PMF.map_apply]
      simp only [reduceCtorEq, ↓reduceIte, tsum_zero]
      by_cases hzero : dist none = 0
      · exact hzero.symm
      · have hsupport : none ∈ dist.support :=
          (PMF.mem_support_iff _ _).2 hzero
        rcases htotal none hsupport with ⟨witness, hwitness⟩
        cases hwitness
  | some value =>
      rw [PMF.map_apply]
      rw [tsum_eq_single value]
      · simp [eraseNonePMF_apply (htotal := htotal)]
      · intro other hne
        have hsome : some value ≠ some other := by
          intro h
          cases h
          exact hne rfl
        simp [hsome]

omit [Fintype P] in
theorem eraseNonePMF_map {α β : Type}
    {dist : PMF (Option α)}
    {htotal : ∀ result ∈ dist.support, ∃ value, result = some value}
    (f : α → β) (fallback : β) :
    PMF.map f (eraseNonePMF dist htotal) =
      PMF.map (fun
        | some value => f value
        | none => fallback) dist := by
  let optionF : Option α → β := fun
    | some value => f value
    | none => fallback
  calc
    PMF.map f (eraseNonePMF dist htotal)
        = PMF.map (optionF ∘ some) (eraseNonePMF dist htotal) := by
            rfl
    _ = PMF.map optionF (PMF.map some (eraseNonePMF dist htotal)) := by
            rw [PMF.map_comp]
    _ = PMF.map optionF dist := by
            rw [eraseNonePMF_map_some]

omit [Fintype P] in
theorem eraseNonePMF_expect {α : Type}
    {dist : PMF (Option α)}
    {htotal : ∀ result ∈ dist.support, ∃ value, result = some value}
    (utility : α → ℝ) (cutoff : ℝ) {C : ℝ}
    (hbd : ∀ value, |utility value| ≤ C) :
    Math.Probability.expect (eraseNonePMF dist htotal) utility =
      Math.Probability.expect dist (fun
        | some value => utility value
        | none => cutoff) := by
  let optionUtility : Option α → ℝ := fun
    | some value => utility value
    | none => cutoff
  have hpush :=
    Math.ProbabilityMassFunction.expect_pushforward_of_bounded_on_source
      (μ := eraseNonePMF dist htotal) (f := some) (φ := optionUtility)
      (hbd := hbd)
  have hmap :
      Math.ProbabilityMassFunction.pushforward
        (eraseNonePMF dist htotal) some = dist := by
    simpa [Math.ProbabilityMassFunction.pushforward] using
      eraseNonePMF_map_some (dist := dist) (htotal := htotal)
  rw [hmap] at hpush
  simpa [optionUtility] using hpush.symm

/-- Pure-strategy frontier game with the impossible cutoff branch erased from
the exposed kernel-game outcome type. -/
structure CompletedFrontierPureKernelGame
    (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph) where
  semantics : FrontierRoundSemantics compiled presentation
  nodeFintype :
    (node : Fin compiled.graph.nodeCount) →
      Fintype (L.Val (compiled.graph.nodeRow node).ty)

namespace CompletedFrontierPureKernelGame

variable {compiled : CompiledProgram P L}
variable {presentation : EventGraph.CheckpointPresentation compiled.graph}

noncomputable def view
    (completed : CompletedFrontierPureKernelGame compiled presentation) :
    (PrimitiveMachine compiled).RoundView :=
  frontierRoundView compiled presentation completed.semantics

@[reducible] private noncomputable def optionalMoveFintype
    (completed : CompletedFrontierPureKernelGame compiled presentation) :
    ∀ player, Fintype (Option ((view completed).Act player)) := by
  classical
  letI :
      ∀ node : Fin compiled.graph.nodeCount,
        Fintype (L.Val (compiled.graph.nodeRow node).ty) :=
    completed.nodeFintype
  intro player
  dsimp [view, frontierRoundView, EventGraph.frontierRoundView]
  infer_instance

private noncomputable instance instOptionalMoveFintype
    (completed : CompletedFrontierPureKernelGame compiled presentation) :
    ∀ player, Fintype (Option ((view completed).Act player)) :=
  optionalMoveFintype completed

noncomputable def optionOutcomeKernel
    (completed : CompletedFrontierPureKernelGame compiled presentation) :
    (∀ player, (view completed).BoundedPureStrategy
      (completionBound compiled) player) →
      PMF (Option (PrimitiveMachine compiled).Outcome) :=
  by
    classical
    letI := optionalMoveFintype completed
    exact fun σ =>
      (view completed).boundedOutcomeFromPure
        (completionBound compiled) σ (completionBound compiled)

theorem optionOutcomeKernel_support_some
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (σ :
      ∀ player, (view completed).BoundedPureStrategy
        (completionBound compiled) player)
    {result : Option (PrimitiveMachine compiled).Outcome}
    (hsupport :
      result ∈ (completed.optionOutcomeKernel σ).support) :
    ∃ outcome, result = some outcome := by
  classical
  letI :
      ∀ player,
        Fintype (Option
          ((frontierRoundView compiled presentation completed.semantics).Act
            player)) :=
    optionalMoveFintype completed
  simpa [optionOutcomeKernel, view] using
    FrontierRoundSemantics.boundedOutcomeFromPure_support_some_completionBound
      completed.semantics σ hsupport

/-- Concrete-outcome kernel game associated with a completed pure frontier
game. The option-valued bounded kernel is total by
`optionOutcomeKernel_support_some`; `eraseNonePMF` removes the impossible
`none` branch. -/
noncomputable def game
    (completed : CompletedFrontierPureKernelGame compiled presentation) :
    KernelGame P := by
  classical
  letI := optionalMoveFintype completed
  exact
    { Strategy := fun player =>
        (view completed).BoundedPureStrategy
          (completionBound compiled) player
      Outcome := (PrimitiveMachine compiled).Outcome
      utility := (PrimitiveMachine compiled).utility
      outcomeKernel := fun σ =>
        eraseNonePMF (completed.optionOutcomeKernel σ)
          (fun result hresult =>
            completed.optionOutcomeKernel_support_some σ hresult) }

theorem none_not_mem_outcomeKernel_support
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (σ : completed.game.Profile) :
    none ∉ (completed.optionOutcomeKernel σ).support := by
  intro hnone
  rcases completed.optionOutcomeKernel_support_some σ hnone with
    ⟨outcome, houtcome⟩
  cases houtcome

/-- The completed pure-strategy game erases only the impossible cutoff branch:
concrete outcome support is exactly option-outcome support at `some`. -/
theorem outcomeKernel_support_iff
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (σ : completed.game.Profile)
    (outcome : (PrimitiveMachine compiled).Outcome) :
    outcome ∈ (completed.game.outcomeKernel σ).support ↔
      some outcome ∈ (completed.optionOutcomeKernel σ).support := by
  classical
  change
    outcome ∈
        (eraseNonePMF (completed.optionOutcomeKernel σ)
          (fun result hresult =>
            completed.optionOutcomeKernel_support_some σ hresult)).support ↔
      some outcome ∈ (completed.optionOutcomeKernel σ).support
  exact mem_support_eraseNonePMF_iff

/-- Pointwise kernel correspondence for completed pure-strategy games: erasing
the cutoff branch leaves exactly the probability mass at `some outcome`. -/
theorem outcomeKernel_apply
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (σ : completed.game.Profile)
    (outcome : (PrimitiveMachine compiled).Outcome) :
    completed.game.outcomeKernel σ outcome =
      completed.optionOutcomeKernel σ (some outcome) := by
  classical
  change
    eraseNonePMF (completed.optionOutcomeKernel σ)
        (fun result hresult =>
          completed.optionOutcomeKernel_support_some σ hresult) outcome =
      completed.optionOutcomeKernel σ (some outcome)
  exact eraseNonePMF_apply outcome

/-- Utility distributions agree between the concrete completed pure-strategy
game and the option-valued bounded game for any cutoff policy. -/
theorem utilityDistribution_eq_optionUtilityDistribution
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (σ : completed.game.Profile) (who : P) (cutoff : Payoff P) :
    PMF.map (fun outcome => (PrimitiveMachine compiled).utility outcome who)
        (completed.game.outcomeKernel σ) =
      PMF.map
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who)
        (completed.optionOutcomeKernel σ) := by
  classical
  change
    PMF.map (fun outcome => (PrimitiveMachine compiled).utility outcome who)
      (eraseNonePMF (completed.optionOutcomeKernel σ)
        (fun result hresult =>
          completed.optionOutcomeKernel_support_some σ hresult)) =
      PMF.map
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who)
        (completed.optionOutcomeKernel σ)
  convert
    eraseNonePMF_map
      (dist := completed.optionOutcomeKernel σ)
      (htotal := fun result hresult =>
        completed.optionOutcomeKernel_support_some σ hresult)
      (f := fun outcome =>
        (PrimitiveMachine compiled).utility outcome who)
      (fallback := cutoff who) using 2
  funext result
  cases result <;> rfl

/-- Expected utility in the concrete completed pure-strategy game agrees with
the option-valued bounded game for any cutoff policy, because `none` has zero
support. -/
theorem eu_eq_optionKernel_expect
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (σ : completed.game.Profile) (who : P) (cutoff : Payoff P) {C : ℝ}
    (hbd :
      ∀ outcome, |(PrimitiveMachine compiled).utility outcome who| ≤ C) :
    completed.game.eu σ who =
      Math.Probability.expect (completed.optionOutcomeKernel σ)
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who) := by
  classical
  change
    Math.Probability.expect
      (eraseNonePMF (completed.optionOutcomeKernel σ)
        (fun result hresult =>
          completed.optionOutcomeKernel_support_some σ hresult))
      (fun outcome => (PrimitiveMachine compiled).utility outcome who) =
      Math.Probability.expect (completed.optionOutcomeKernel σ)
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who)
  convert
    eraseNonePMF_expect
      (dist := completed.optionOutcomeKernel σ)
      (htotal := fun result hresult =>
        completed.optionOutcomeKernel_support_some σ hresult)
      (utility := fun outcome =>
        (PrimitiveMachine compiled).utility outcome who)
      (cutoff := cutoff who)
      hbd using 2
  funext result
  cases result <;> rfl

/-- Event batches extracted from a completed pure-strategy bounded history are
available primitive machine batches. -/
theorem boundedHistory_eventBatches_availableRun
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled)) :
    (PrimitiveMachine compiled).AvailableRunBatchesFrom
      ((Machine.BoundedState.init
        (PrimitiveMachine compiled) (completionBound compiled)).state)
      ((view completed).boundedHistoryEventBatches
        (completionBound compiled) history)
      history.lastState.state := by
  exact
    FrontierRoundSemantics.boundedHistory_eventBatches_availableRun
      completed.semantics history

/-- A supported completed pure-strategy outcome is backed by a supported
bounded frontier history with an available primitive batch run, terminal graph
state, and matching primitive-machine outcome. -/
theorem outcomeKernel_support_history
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (σ : completed.game.Profile)
    {outcome : (PrimitiveMachine compiled).Outcome}
    (hsupport : outcome ∈ (completed.game.outcomeKernel σ).support) :
    ∃ history : (view completed).BoundedHistory (completionBound compiled),
      history ∈
        ((view completed).runDist
          (completionBound compiled) (completionBound compiled)
          ((view completed).legalPureToBehavioral
            (completionBound compiled) σ)).support ∧
      EventGraph.Terminal compiled.graph history.lastState.state.1 ∧
      (PrimitiveMachine compiled).outcome history.lastState.state =
        some outcome ∧
      (PrimitiveMachine compiled).AvailableRunBatchesFrom
        ((Machine.BoundedState.init
          (PrimitiveMachine compiled) (completionBound compiled)).state)
        ((view completed).boundedHistoryEventBatches
          (completionBound compiled) history)
        history.lastState.state := by
  classical
  letI :
      ∀ node : Fin compiled.graph.nodeCount,
        Fintype (L.Val (compiled.graph.nodeRow node).ty) :=
    completed.nodeFintype
  letI :
      ∀ player,
        Fintype (Option
          ((frontierRoundView compiled presentation completed.semantics).Act
            player)) := by
    intro player
    dsimp [frontierRoundView, EventGraph.frontierRoundView]
    infer_instance
  have hsome :
      some outcome ∈ (completed.optionOutcomeKernel σ).support :=
    (completed.outcomeKernel_support_iff σ outcome).1 hsupport
  simpa [optionOutcomeKernel, view] using
    FrontierRoundSemantics.boundedOutcomeFromPure_support_history_completionBound
      completed.semantics σ hsome

/-- Every supported completed pure-strategy frontier round strictly advances
the completed-node downset. -/
theorem boundedStep_done_ssubset
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (step : (view completed).BoundedStep (completionBound compiled)) :
    step.src.state.1.done ⊂ step.dst.state.1.done :=
  FrontierRoundSemantics.boundedStep_done_ssubset
    completed.semantics step

/-- A completed pure-strategy history with one round per graph node is
terminal. -/
theorem boundedHistory_terminal_of_length_completionBound
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled))
    (hlen : history.steps.length = completionBound compiled) :
    EventGraph.Terminal compiled.graph history.lastState.state.1 :=
  FrontierRoundSemantics.boundedHistory_terminal_of_length_completionBound
    completed.semantics history hlen

/-- The completed pure-strategy history induces a checkpoint history for the
attached presentation. -/
noncomputable def boundedHistory_checkpointHistory
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled)) :
    presentation.History
      ((Machine.BoundedState.init
        (PrimitiveMachine compiled) (completionBound compiled)).state)
      history.lastState.state :=
  FrontierRoundSemantics.boundedHistory_checkpointHistory
    completed.semantics history

/-- The checkpoint history induced by a completed pure-strategy history has the
same public observations as the frontier-round history. -/
theorem boundedHistory_checkpointHistory_publicView
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled)) :
    (completed.boundedHistory_checkpointHistory history).publicView =
      history.publicView := by
  exact
    FrontierRoundSemantics.boundedHistory_checkpointHistory_publicView
      completed.semantics history

/-- The checkpoint history induced by a completed pure-strategy history has the
same per-player checkpoint observations as the frontier-round information
state. -/
theorem boundedHistory_checkpointHistory_playerView
    (completed : CompletedFrontierPureKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled))
    (player : P) :
    (completed.boundedHistory_checkpointHistory history).playerView player =
      (Machine.RoundView.InfoState.observationEvents
        (history.playerView player)).map Prod.fst := by
  exact
    FrontierRoundSemantics.boundedHistory_checkpointHistory_playerView
      completed.semantics history player

end CompletedFrontierPureKernelGame

/-- Behavioral-strategy frontier game with the impossible cutoff branch erased
from the exposed kernel-game outcome type. -/
structure CompletedFrontierBehavioralKernelGame
    (compiled : CompiledProgram P L)
    (presentation : EventGraph.CheckpointPresentation compiled.graph) where
  semantics : FrontierRoundSemantics compiled presentation
  nodeFintype :
    (node : Fin compiled.graph.nodeCount) →
      Fintype (L.Val (compiled.graph.nodeRow node).ty)

namespace CompletedFrontierBehavioralKernelGame

variable {compiled : CompiledProgram P L}
variable {presentation : EventGraph.CheckpointPresentation compiled.graph}

noncomputable def view
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation) :
    (PrimitiveMachine compiled).RoundView :=
  frontierRoundView compiled presentation completed.semantics

@[reducible] private noncomputable def optionalMoveFintype
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation) :
    ∀ player, Fintype (Option ((view completed).Act player)) := by
  classical
  letI :
      ∀ node : Fin compiled.graph.nodeCount,
        Fintype (L.Val (compiled.graph.nodeRow node).ty) :=
    completed.nodeFintype
  intro player
  dsimp [view, frontierRoundView, EventGraph.frontierRoundView]
  infer_instance

private noncomputable instance instOptionalMoveFintype
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation) :
    ∀ player, Fintype (Option ((view completed).Act player)) :=
  optionalMoveFintype completed

noncomputable def optionOutcomeKernel
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation) :
    (∀ player, (view completed).BoundedBehavioralStrategy
      (completionBound compiled) player) →
      PMF (Option (PrimitiveMachine compiled).Outcome) :=
  by
    classical
    letI := optionalMoveFintype completed
    exact fun σ =>
      (view completed).boundedOutcomeFromBehavioral
        (completionBound compiled) σ (completionBound compiled)

theorem optionOutcomeKernel_support_some
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (σ :
      ∀ player, (view completed).BoundedBehavioralStrategy
        (completionBound compiled) player)
    {result : Option (PrimitiveMachine compiled).Outcome}
    (hsupport :
      result ∈ (completed.optionOutcomeKernel σ).support) :
    ∃ outcome, result = some outcome := by
  classical
  letI :
      ∀ player,
        Fintype (Option
          ((frontierRoundView compiled presentation completed.semantics).Act
            player)) :=
    optionalMoveFintype completed
  simpa [optionOutcomeKernel, view] using
    FrontierRoundSemantics.boundedOutcomeFromBehavioral_support_some_completionBound
      completed.semantics σ hsupport

/-- Concrete-outcome kernel game associated with a completed behavioral
frontier game. The option-valued bounded kernel is total by
`optionOutcomeKernel_support_some`; `eraseNonePMF` removes the impossible
`none` branch. -/
noncomputable def game
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation) :
    KernelGame P := by
  classical
  letI := optionalMoveFintype completed
  exact
    { Strategy := fun player =>
        (view completed).BoundedBehavioralStrategy
          (completionBound compiled) player
      Outcome := (PrimitiveMachine compiled).Outcome
      utility := (PrimitiveMachine compiled).utility
      outcomeKernel := fun σ =>
        eraseNonePMF (completed.optionOutcomeKernel σ)
          (fun result hresult =>
            completed.optionOutcomeKernel_support_some σ hresult) }

theorem none_not_mem_outcomeKernel_support
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (σ : completed.game.Profile) :
    none ∉ (completed.optionOutcomeKernel σ).support := by
  intro hnone
  rcases completed.optionOutcomeKernel_support_some σ hnone with
    ⟨outcome, houtcome⟩
  cases houtcome

/-- The completed behavioral-strategy game erases only the impossible cutoff
branch: concrete outcome support is exactly option-outcome support at `some`. -/
theorem outcomeKernel_support_iff
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (σ : completed.game.Profile)
    (outcome : (PrimitiveMachine compiled).Outcome) :
    outcome ∈ (completed.game.outcomeKernel σ).support ↔
      some outcome ∈ (completed.optionOutcomeKernel σ).support := by
  classical
  change
    outcome ∈
        (eraseNonePMF (completed.optionOutcomeKernel σ)
          (fun result hresult =>
            completed.optionOutcomeKernel_support_some σ hresult)).support ↔
      some outcome ∈ (completed.optionOutcomeKernel σ).support
  exact mem_support_eraseNonePMF_iff

/-- Pointwise kernel correspondence for completed behavioral-strategy games:
erasing the cutoff branch leaves exactly the probability mass at
`some outcome`. -/
theorem outcomeKernel_apply
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (σ : completed.game.Profile)
    (outcome : (PrimitiveMachine compiled).Outcome) :
    completed.game.outcomeKernel σ outcome =
      completed.optionOutcomeKernel σ (some outcome) := by
  classical
  change
    eraseNonePMF (completed.optionOutcomeKernel σ)
        (fun result hresult =>
          completed.optionOutcomeKernel_support_some σ hresult) outcome =
      completed.optionOutcomeKernel σ (some outcome)
  exact eraseNonePMF_apply outcome

/-- Utility distributions agree between the concrete completed behavioral
game and the option-valued bounded game for any cutoff policy. -/
theorem utilityDistribution_eq_optionUtilityDistribution
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (σ : completed.game.Profile) (who : P) (cutoff : Payoff P) :
    PMF.map (fun outcome => (PrimitiveMachine compiled).utility outcome who)
        (completed.game.outcomeKernel σ) =
      PMF.map
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who)
        (completed.optionOutcomeKernel σ) := by
  classical
  change
    PMF.map (fun outcome => (PrimitiveMachine compiled).utility outcome who)
      (eraseNonePMF (completed.optionOutcomeKernel σ)
        (fun result hresult =>
          completed.optionOutcomeKernel_support_some σ hresult)) =
      PMF.map
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who)
        (completed.optionOutcomeKernel σ)
  convert
    eraseNonePMF_map
      (dist := completed.optionOutcomeKernel σ)
      (htotal := fun result hresult =>
        completed.optionOutcomeKernel_support_some σ hresult)
      (f := fun outcome =>
        (PrimitiveMachine compiled).utility outcome who)
      (fallback := cutoff who) using 2
  funext result
  cases result <;> rfl

/-- Expected utility in the concrete completed behavioral-strategy game agrees
with the option-valued bounded game for any cutoff policy, because `none` has
zero support. -/
theorem eu_eq_optionKernel_expect
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (σ : completed.game.Profile) (who : P) (cutoff : Payoff P) {C : ℝ}
    (hbd :
      ∀ outcome, |(PrimitiveMachine compiled).utility outcome who| ≤ C) :
    completed.game.eu σ who =
      Math.Probability.expect (completed.optionOutcomeKernel σ)
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who) := by
  classical
  change
    Math.Probability.expect
      (eraseNonePMF (completed.optionOutcomeKernel σ)
        (fun result hresult =>
          completed.optionOutcomeKernel_support_some σ hresult))
      (fun outcome => (PrimitiveMachine compiled).utility outcome who) =
      Math.Probability.expect (completed.optionOutcomeKernel σ)
        (fun result =>
          Machine.RoundView.optionOutcomeUtility
            (PrimitiveMachine compiled) cutoff result who)
  convert
    eraseNonePMF_expect
      (dist := completed.optionOutcomeKernel σ)
      (htotal := fun result hresult =>
        completed.optionOutcomeKernel_support_some σ hresult)
      (utility := fun outcome =>
        (PrimitiveMachine compiled).utility outcome who)
      (cutoff := cutoff who)
      hbd using 2
  funext result
  cases result <;> rfl

/-- Event batches extracted from a completed behavioral-strategy bounded
history are available primitive machine batches. -/
theorem boundedHistory_eventBatches_availableRun
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled)) :
    (PrimitiveMachine compiled).AvailableRunBatchesFrom
      ((Machine.BoundedState.init
        (PrimitiveMachine compiled) (completionBound compiled)).state)
      ((view completed).boundedHistoryEventBatches
        (completionBound compiled) history)
      history.lastState.state := by
  exact
    FrontierRoundSemantics.boundedHistory_eventBatches_availableRun
      completed.semantics history

/-- A supported completed behavioral-strategy outcome is backed by a supported
bounded frontier history with an available primitive batch run, terminal graph
state, and matching primitive-machine outcome. -/
theorem outcomeKernel_support_history
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (σ : completed.game.Profile)
    {outcome : (PrimitiveMachine compiled).Outcome}
    (hsupport : outcome ∈ (completed.game.outcomeKernel σ).support) :
    ∃ history : (view completed).BoundedHistory (completionBound compiled),
      history ∈
        ((view completed).runDist
          (completionBound compiled) (completionBound compiled) σ).support ∧
      EventGraph.Terminal compiled.graph history.lastState.state.1 ∧
      (PrimitiveMachine compiled).outcome history.lastState.state =
        some outcome ∧
      (PrimitiveMachine compiled).AvailableRunBatchesFrom
        ((Machine.BoundedState.init
          (PrimitiveMachine compiled) (completionBound compiled)).state)
        ((view completed).boundedHistoryEventBatches
          (completionBound compiled) history)
        history.lastState.state := by
  classical
  letI :
      ∀ node : Fin compiled.graph.nodeCount,
        Fintype (L.Val (compiled.graph.nodeRow node).ty) :=
    completed.nodeFintype
  letI :
      ∀ player,
        Fintype (Option
          ((frontierRoundView compiled presentation completed.semantics).Act
            player)) := by
    intro player
    dsimp [frontierRoundView, EventGraph.frontierRoundView]
    infer_instance
  have hsome :
      some outcome ∈ (completed.optionOutcomeKernel σ).support :=
    (completed.outcomeKernel_support_iff σ outcome).1 hsupport
  simpa [optionOutcomeKernel, view] using
    FrontierRoundSemantics.boundedOutcomeFromBehavioral_support_history_completionBound
      completed.semantics σ hsome

/-- Every supported completed behavioral-strategy frontier round strictly
advances the completed-node downset. -/
theorem boundedStep_done_ssubset
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (step : (view completed).BoundedStep (completionBound compiled)) :
    step.src.state.1.done ⊂ step.dst.state.1.done :=
  FrontierRoundSemantics.boundedStep_done_ssubset
    completed.semantics step

/-- A completed behavioral-strategy history with one round per graph node is
terminal. -/
theorem boundedHistory_terminal_of_length_completionBound
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled))
    (hlen : history.steps.length = completionBound compiled) :
    EventGraph.Terminal compiled.graph history.lastState.state.1 :=
  FrontierRoundSemantics.boundedHistory_terminal_of_length_completionBound
    completed.semantics history hlen

/-- The completed behavioral-strategy history induces a checkpoint history for
the attached presentation. -/
noncomputable def boundedHistory_checkpointHistory
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled)) :
    presentation.History
      ((Machine.BoundedState.init
        (PrimitiveMachine compiled) (completionBound compiled)).state)
      history.lastState.state :=
  FrontierRoundSemantics.boundedHistory_checkpointHistory
    completed.semantics history

/-- The checkpoint history induced by a completed behavioral-strategy history
has the same public observations as the frontier-round history. -/
theorem boundedHistory_checkpointHistory_publicView
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled)) :
    (completed.boundedHistory_checkpointHistory history).publicView =
      history.publicView := by
  exact
    FrontierRoundSemantics.boundedHistory_checkpointHistory_publicView
      completed.semantics history

/-- The checkpoint history induced by a completed behavioral-strategy history
has the same per-player checkpoint observations as the frontier-round
information state. -/
theorem boundedHistory_checkpointHistory_playerView
    (completed : CompletedFrontierBehavioralKernelGame compiled presentation)
    (history : (view completed).BoundedHistory (completionBound compiled))
    (player : P) :
    (completed.boundedHistory_checkpointHistory history).playerView player =
      (Machine.RoundView.InfoState.observationEvents
        (history.playerView player)).map Prod.fst := by
  exact
    FrontierRoundSemantics.boundedHistory_checkpointHistory_playerView
      completed.semantics history player

end CompletedFrontierBehavioralKernelGame

/-- Default pure-strategy frontier game for a finite checked program. The
exposed `.game` has concrete outcomes, not optional outcomes. -/
noncomputable def canonicalFrontierPureKernelGame
    (program : WFProgram P L) [FiniteDomains program] :
    CompletedFrontierPureKernelGame (ToEventGraph.compile program.core)
      (frontierPresentation
        (ToEventGraph.compile program.core)
        (ToEventGraph.compile_guardLive program)) := by
  classical
  let compiled := ToEventGraph.compile program.core
  let presentation :=
    frontierPresentation compiled
      (ToEventGraph.compile_guardLive program)
  let semantics :=
    canonicalFrontierRoundSemantics compiled
      (ToEventGraph.compile_guardLive program)
  letI :
      ∀ node : Fin compiled.graph.nodeCount,
        Fintype (L.Val (compiled.graph.nodeRow node).ty) :=
    ToEventGraph.compile_nodeFintype program
  exact
    { semantics := semantics
      nodeFintype := ToEventGraph.compile_nodeFintype program }

/-- Default behavioral-strategy frontier game for a finite checked program.
The exposed `.game` has concrete outcomes, not optional outcomes. -/
noncomputable def canonicalFrontierBehavioralKernelGame
    (program : WFProgram P L) [FiniteDomains program] :
    CompletedFrontierBehavioralKernelGame (ToEventGraph.compile program.core)
      (frontierPresentation
        (ToEventGraph.compile program.core)
        (ToEventGraph.compile_guardLive program)) := by
  classical
  let compiled := ToEventGraph.compile program.core
  let presentation :=
    frontierPresentation compiled
      (ToEventGraph.compile_guardLive program)
  let semantics :=
    canonicalFrontierRoundSemantics compiled
      (ToEventGraph.compile_guardLive program)
  letI :
      ∀ node : Fin compiled.graph.nodeCount,
        Fintype (L.Val (compiled.graph.nodeRow node).ty) :=
    ToEventGraph.compile_nodeFintype program
  exact
    { semantics := semantics
      nodeFintype := ToEventGraph.compile_nodeFintype program }

/-- A supported default pure frontier transition lands at an internal-closed
checkpoint. -/
theorem canonicalFrontierPureKernelGame_transition_support_closed
    (program : WFProgram P L) [FiniteDomains program]
    {state dst : (PrimitiveMachine (ToEventGraph.compile program.core)).State}
    (action :
      {a : JointAction (FrontierAct (ToEventGraph.compile program.core)) //
        JointActionLegal
          (FrontierAct (ToEventGraph.compile program.core))
          (frontierActive (ToEventGraph.compile program.core))
          (PrimitiveMachine (ToEventGraph.compile program.core)).terminal
          (frontierAvailableActions (ToEventGraph.compile program.core))
          state a})
    (hsupport :
      (canonicalFrontierPureKernelGame program).semantics.transition
        state action dst ≠ 0) :
    EventGraph.readyInternalNodes
        (ToEventGraph.compile program.core).graph dst.1 = ∅ := by
  simpa [canonicalFrontierPureKernelGame] using
    canonicalFrontierRoundSemantics_transition_support_closed
      (ToEventGraph.compile program.core)
      (ToEventGraph.compile_guardLive program)
      action hsupport

/-- A supported default behavioral frontier transition lands at an
internal-closed checkpoint. -/
theorem canonicalFrontierBehavioralKernelGame_transition_support_closed
    (program : WFProgram P L) [FiniteDomains program]
    {state dst : (PrimitiveMachine (ToEventGraph.compile program.core)).State}
    (action :
      {a : JointAction (FrontierAct (ToEventGraph.compile program.core)) //
        JointActionLegal
          (FrontierAct (ToEventGraph.compile program.core))
          (frontierActive (ToEventGraph.compile program.core))
          (PrimitiveMachine (ToEventGraph.compile program.core)).terminal
          (frontierAvailableActions (ToEventGraph.compile program.core))
          state a})
    (hsupport :
      (canonicalFrontierBehavioralKernelGame program).semantics.transition
        state action dst ≠ 0) :
    EventGraph.readyInternalNodes
        (ToEventGraph.compile program.core).graph dst.1 = ∅ := by
  simpa [canonicalFrontierBehavioralKernelGame] using
    canonicalFrontierRoundSemantics_transition_support_closed
      (ToEventGraph.compile program.core)
      (ToEventGraph.compile_guardLive program)
      action hsupport

namespace FrontierPureKernelGame

variable {compiled : CompiledProgram P L}
variable {presentation : EventGraph.CheckpointPresentation compiled.graph}

/-- The round view certified by this pure-strategy kernel game. -/
noncomputable def view
    (game : FrontierPureKernelGame compiled presentation) :
    (PrimitiveMachine compiled).RoundView :=
  frontierRoundView compiled presentation game.semantics

/-- Event batches extracted from a certified pure-strategy bounded history are
available primitive machine batches. -/
theorem boundedHistory_eventBatches_availableRun
    (game : FrontierPureKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon) :
    (PrimitiveMachine compiled).AvailableRunBatchesFrom
      ((Machine.BoundedState.init
        (PrimitiveMachine compiled) game.horizon).state)
      (game.view.boundedHistoryEventBatches game.horizon history)
      history.lastState.state := by
  exact
    FrontierRoundSemantics.boundedHistory_eventBatches_availableRun
      game.semantics history

/-- Every supported bounded frontier round of this pure-strategy game strictly
advances the completed-node downset. -/
theorem boundedStep_done_ssubset
    (game : FrontierPureKernelGame compiled presentation)
    (step : game.view.BoundedStep game.horizon) :
    step.src.state.1.done ⊂ step.dst.state.1.done :=
  FrontierRoundSemantics.boundedStep_done_ssubset
    game.semantics step

/-- A pure-strategy game history with one round per graph node is terminal. -/
theorem boundedHistory_terminal_of_length_completionBound
    (game : FrontierPureKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon)
    (hlen : history.steps.length = completionBound compiled) :
    EventGraph.Terminal compiled.graph history.lastState.state.1 :=
  FrontierRoundSemantics.boundedHistory_terminal_of_length_completionBound
    game.semantics history hlen

/-- The bounded strategic history of this pure-strategy game induces a
checkpoint history for the attached presentation. -/
noncomputable def boundedHistory_checkpointHistory
    (game : FrontierPureKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon) :
    presentation.History
      ((Machine.BoundedState.init
        (PrimitiveMachine compiled) game.horizon).state)
      history.lastState.state :=
  FrontierRoundSemantics.boundedHistory_checkpointHistory
    game.semantics history

/-- The checkpoint history induced by a certified pure-strategy history has
the same public observations as the frontier-round history. -/
theorem boundedHistory_checkpointHistory_publicView
    (game : FrontierPureKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon) :
    (game.boundedHistory_checkpointHistory history).publicView =
      history.publicView := by
  exact
    FrontierRoundSemantics.boundedHistory_checkpointHistory_publicView
      game.semantics history

/-- The checkpoint history induced by a certified pure-strategy history has
the same per-player checkpoint observations as the frontier-round information
state. -/
theorem boundedHistory_checkpointHistory_playerView
    (game : FrontierPureKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon)
    (player : P) :
    (game.boundedHistory_checkpointHistory history).playerView player =
      (Machine.RoundView.InfoState.observationEvents
        (history.playerView player)).map Prod.fst := by
  exact
    FrontierRoundSemantics.boundedHistory_checkpointHistory_playerView
      game.semantics history player

end FrontierPureKernelGame

namespace FrontierBehavioralKernelGame

variable {compiled : CompiledProgram P L}
variable {presentation : EventGraph.CheckpointPresentation compiled.graph}

/-- The round view certified by this behavioral-strategy kernel game. -/
noncomputable def view
    (game : FrontierBehavioralKernelGame compiled presentation) :
    (PrimitiveMachine compiled).RoundView :=
  frontierRoundView compiled presentation game.semantics

/-- Event batches extracted from a certified behavioral-strategy bounded
history are available primitive machine batches. -/
theorem boundedHistory_eventBatches_availableRun
    (game : FrontierBehavioralKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon) :
    (PrimitiveMachine compiled).AvailableRunBatchesFrom
      ((Machine.BoundedState.init
        (PrimitiveMachine compiled) game.horizon).state)
      (game.view.boundedHistoryEventBatches game.horizon history)
      history.lastState.state := by
  exact
    FrontierRoundSemantics.boundedHistory_eventBatches_availableRun
      game.semantics history

/-- Every supported bounded frontier round of this behavioral-strategy game
strictly advances the completed-node downset. -/
theorem boundedStep_done_ssubset
    (game : FrontierBehavioralKernelGame compiled presentation)
    (step : game.view.BoundedStep game.horizon) :
    step.src.state.1.done ⊂ step.dst.state.1.done :=
  FrontierRoundSemantics.boundedStep_done_ssubset
    game.semantics step

/-- A behavioral-strategy game history with one round per graph node is
terminal. -/
theorem boundedHistory_terminal_of_length_completionBound
    (game : FrontierBehavioralKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon)
    (hlen : history.steps.length = completionBound compiled) :
    EventGraph.Terminal compiled.graph history.lastState.state.1 :=
  FrontierRoundSemantics.boundedHistory_terminal_of_length_completionBound
    game.semantics history hlen

/-- The bounded strategic history of this behavioral-strategy game induces a
checkpoint history for the attached presentation. -/
noncomputable def boundedHistory_checkpointHistory
    (game : FrontierBehavioralKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon) :
    presentation.History
      ((Machine.BoundedState.init
        (PrimitiveMachine compiled) game.horizon).state)
      history.lastState.state :=
  FrontierRoundSemantics.boundedHistory_checkpointHistory
    game.semantics history

/-- The checkpoint history induced by a certified behavioral-strategy history
has the same public observations as the frontier-round history. -/
theorem boundedHistory_checkpointHistory_publicView
    (game : FrontierBehavioralKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon) :
    (game.boundedHistory_checkpointHistory history).publicView =
      history.publicView := by
  exact
    FrontierRoundSemantics.boundedHistory_checkpointHistory_publicView
      game.semantics history

/-- The checkpoint history induced by a certified behavioral-strategy history
has the same per-player checkpoint observations as the frontier-round
information state. -/
theorem boundedHistory_checkpointHistory_playerView
    (game : FrontierBehavioralKernelGame compiled presentation)
    (history : game.view.BoundedHistory game.horizon)
    (player : P) :
    (game.boundedHistory_checkpointHistory history).playerView player =
      (Machine.RoundView.InfoState.observationEvents
        (history.playerView player)).map Prod.fst := by
  exact
    FrontierRoundSemantics.boundedHistory_checkpointHistory_playerView
      game.semantics history player

end FrontierBehavioralKernelGame

end ToEventGraph

end Vegas
