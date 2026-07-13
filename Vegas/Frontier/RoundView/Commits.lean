import Vegas.Compile.Checkpoint
import Vegas.Machine.Adapter.RoundView
import Vegas.Machine.KernelGame

/-!
# Frontier actions and selected commit batches

Frontier action carriers (`FrontierAct`), event selection, and the selected
commit-batch machinery with its availability/realization theorems.
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
  exact ⟨written, next, by rw [hevent]; exact hnext, hcfg⟩

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


end ToEventGraph

end Vegas
