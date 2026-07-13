import Vegas.Frontier.RoundView.Commits

/-!
# Ready internal events and internal closure

Ready internal-event batches and the internal-closure transition that drives
all currently-ready operational/chance work to completion before a checkpoint.
-/

namespace Vegas

namespace ToEventGraph

open GameTheory

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

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
  exact ⟨written, next, by rw [hevent]; exact hnext, hcfg⟩

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
/-- Commit availability is invariant under an available primitive run made
only of internal graph events.  This is the source/frontier scheduling fact
needed when canonical frontier checkpoints close ready internal work before
asking for strategic commit choices. -/
theorem commitAvailable_persist_after_internalOnly_availableRunFrom
    (compiled : CompiledProgram P L)
    {source dst : (PrimitiveMachine compiled).State}
    {batch : List (PrimitiveMachine compiled).Event}
    {who : P} {action : EventGraph.CommitAction compiled.graph who}
    (hcommit :
      EventGraph.CommitAvailable compiled.graph source.1 who action)
    (hinternal : InternalOnlyBatch compiled batch)
    (hrun :
      (PrimitiveMachine compiled).AvailableRunFrom source batch dst) :
    EventGraph.CommitAvailable compiled.graph dst.1 who action := by
  induction hrun generalizing who action with
  | nil state =>
      exact hcommit
  | @cons source mid dst event events havailable hstep tail ih =>
      rcases hinternal event (by simp) with ⟨internalEvent, hevent⟩
      rw [hevent] at havailable hstep
      change EventGraph.InternalAvailable compiled.graph _ internalEvent at havailable
      rcases hcommit with ⟨commitStep⟩
      have hcommitSource :
          EventGraph.CommitAvailable compiled.graph _ who action :=
        ⟨commitStep⟩
      have hnodeNe : action.node ≠ internalEvent.node := by
        intro hsame
        rcases havailable with ⟨internalStep⟩
        cases internalStep with
        | sample row _ row_get sem_eq _ _ _ =>
            have hcommitRow :
                compiled.graph.nodes[(internalEvent.node : Nat)]? =
                  some commitStep.row := by
              simpa [hsame] using commitStep.row_get
            have hrowEq : commitStep.row = row :=
              Option.some.inj (hcommitRow.symm.trans row_get)
            have hsemCommit : row.sem = .commit who commitStep.guard := by
              rw [← hrowEq]
              exact commitStep.sem_eq
            rw [sem_eq] at hsemCommit
            cases hsemCommit
        | reveal row _ row_get sem_eq _ _ _ =>
            have hcommitRow :
                compiled.graph.nodes[(internalEvent.node : Nat)]? =
                  some commitStep.row := by
              simpa [hsame] using commitStep.row_get
            have hrowEq : commitStep.row = row :=
              Option.some.inj (hcommitRow.symm.trans row_get)
            have hsemCommit : row.sem = .commit who commitStep.guard := by
              rw [← hrowEq]
              exact commitStep.sem_eq
            rw [sem_eq] at hsemCommit
            cases hsemCommit
      rcases
          readyInternalAtNode_step_support_completeNode
            compiled (node := internalEvent.node)
            (event :=
              Machine.Event.internal (M := PrimitiveMachine compiled)
                internalEvent)
            rfl havailable hstep with
        ⟨written, hmid⟩
      have hcommitMid :
          EventGraph.CommitAvailable compiled.graph mid.1 who action := by
        rw [hmid]
        rcases havailable.ready with ⟨row, hrow, hready⟩
        exact
          hcommitSource.persist_after_other_ready_write
            compiled.graphWF hrow hready written hnodeNe
      have htailInternal : InternalOnlyBatch compiled events := by
        intro tailEvent hmem
        exact hinternal tailEvent (by simp [hmem])
      exact ih hcommitMid htailInternal

omit [Fintype P] in
/-- Commit availability after an internal-only primitive run reflects back to
the pre-run state when the commit node was already ready before the run. -/
theorem commitAvailable_reflect_before_internalOnly_availableRunFrom
    (compiled : CompiledProgram P L)
    {source dst : (PrimitiveMachine compiled).State}
    {batch : List (PrimitiveMachine compiled).Event}
    {who : P} {action : EventGraph.CommitAction compiled.graph who}
    (hready : EventGraph.Ready compiled.graph source.1 action.node)
    (hinternal : InternalOnlyBatch compiled batch)
    (hrun :
      (PrimitiveMachine compiled).AvailableRunFrom source batch dst)
    (hcommit :
      EventGraph.CommitAvailable compiled.graph dst.1 who action) :
    EventGraph.CommitAvailable compiled.graph source.1 who action := by
  induction hrun generalizing who action with
  | nil state =>
      exact hcommit
  | @cons source mid dst event events havailable hstep tail ih =>
      rcases hinternal event (by simp) with ⟨internalEvent, hevent⟩
      rw [hevent] at havailable hstep
      change EventGraph.InternalAvailable compiled.graph _ internalEvent at havailable
      rcases hcommit with ⟨commitStep⟩
      have hcommitDst :
          EventGraph.CommitAvailable compiled.graph dst.1 who action :=
        ⟨commitStep⟩
      have hnodeNe : action.node ≠ internalEvent.node := by
        intro hsame
        rcases havailable with ⟨internalStep⟩
        cases internalStep with
        | sample row _ row_get sem_eq _ _ _ =>
            have hcommitRow :
                compiled.graph.nodes[(internalEvent.node : Nat)]? =
                  some commitStep.row := by
              simpa [hsame] using commitStep.row_get
            have hrowEq : commitStep.row = row :=
              Option.some.inj (hcommitRow.symm.trans row_get)
            have hsemCommit : row.sem = .commit who commitStep.guard := by
              rw [← hrowEq]
              exact commitStep.sem_eq
            rw [sem_eq] at hsemCommit
            cases hsemCommit
        | reveal row _ row_get sem_eq _ _ _ =>
            have hcommitRow :
                compiled.graph.nodes[(internalEvent.node : Nat)]? =
                  some commitStep.row := by
              simpa [hsame] using commitStep.row_get
            have hrowEq : commitStep.row = row :=
              Option.some.inj (hcommitRow.symm.trans row_get)
            have hsemCommit : row.sem = .commit who commitStep.guard := by
              rw [← hrowEq]
              exact commitStep.sem_eq
            rw [sem_eq] at hsemCommit
            cases hsemCommit
      rcases
          readyInternalAtNode_step_support_completeNode
            compiled (node := internalEvent.node)
            (event :=
              Machine.Event.internal (M := PrimitiveMachine compiled)
                internalEvent)
            rfl havailable hstep with
        ⟨written, hmid⟩
      have hreadyMid :
          EventGraph.Ready compiled.graph mid.1 action.node := by
        rw [hmid]
        exact hready.completeNode_of_ne hnodeNe
      have htailInternal : InternalOnlyBatch compiled events := by
        intro tailEvent hmem
        exact hinternal tailEvent (by simp [hmem])
      have hcommitMid :
          EventGraph.CommitAvailable compiled.graph mid.1 who action :=
        ih hreadyMid htailInternal hcommitDst
      have hcommitAfter :
          EventGraph.CommitAvailable compiled.graph
            (source.1.completeNode internalEvent.node written) who action := by
        simpa [hmid] using hcommitMid
      rcases havailable.ready with ⟨row, hrow, hreadyInternal⟩
      exact
        EventGraph.CommitAvailable.reflect_before_other_ready_write
          compiled.graphWF hready hrow hreadyInternal written hcommitAfter

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
theorem commitAvailable_persist_after_internalClosureTransition_support
    (compiled : CompiledProgram P L)
    (fuel : Nat)
    {state dst : (PrimitiveMachine compiled).State}
    {who : P} {action : EventGraph.CommitAction compiled.graph who}
    (hcommit :
      EventGraph.CommitAvailable compiled.graph state.1 who action)
    (hsupport :
      dst ∈ (internalClosureTransition compiled fuel state).support) :
    EventGraph.CommitAvailable compiled.graph dst.1 who action := by
  rcases internalClosureTransition_support_cert
      compiled fuel hsupport with
    ⟨batch, hinternal, hrun⟩
  exact
    commitAvailable_persist_after_internalOnly_availableRunFrom
      compiled hcommit hinternal hrun

omit [Fintype P] in
theorem commitAvailable_reflect_before_internalClosureTransition_support
    (compiled : CompiledProgram P L)
    (fuel : Nat)
    {state dst : (PrimitiveMachine compiled).State}
    {who : P} {action : EventGraph.CommitAction compiled.graph who}
    (hready : EventGraph.Ready compiled.graph state.1 action.node)
    (hsupport :
      dst ∈ (internalClosureTransition compiled fuel state).support)
    (hcommit :
      EventGraph.CommitAvailable compiled.graph dst.1 who action) :
    EventGraph.CommitAvailable compiled.graph state.1 who action := by
  rcases internalClosureTransition_support_cert
      compiled fuel hsupport with
    ⟨batch, hinternal, hrun⟩
  exact
    commitAvailable_reflect_before_internalOnly_availableRunFrom
      compiled hready hinternal hrun hcommit

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
theorem commitAvailable_persist_after_internalClosureAfterReady_support
    (compiled : CompiledProgram P L)
    {state dst : (PrimitiveMachine compiled).State}
    (hinternal :
      (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty)
    {who : P} {action : EventGraph.CommitAction compiled.graph who}
    (hcommit :
      EventGraph.CommitAvailable compiled.graph state.1 who action)
    (hsupport :
      dst ∈ (internalClosureAfterReady compiled state).support) :
    EventGraph.CommitAvailable compiled.graph dst.1 who action := by
  rcases internalClosureAfterReady_support_cert
      compiled hinternal hsupport with
    ⟨batch, hinternalOnly, hrun, _hne⟩
  exact
    commitAvailable_persist_after_internalOnly_availableRunFrom
      compiled hcommit hinternalOnly hrun

omit [Fintype P] in
theorem commitAvailable_reflect_before_internalClosureAfterReady_support
    (compiled : CompiledProgram P L)
    {state dst : (PrimitiveMachine compiled).State}
    (hinternal :
      (EventGraph.readyInternalNodes compiled.graph state.1).Nonempty)
    {who : P} {action : EventGraph.CommitAction compiled.graph who}
    (hready : EventGraph.Ready compiled.graph state.1 action.node)
    (hsupport :
      dst ∈ (internalClosureAfterReady compiled state).support)
    (hcommit :
      EventGraph.CommitAvailable compiled.graph dst.1 who action) :
    EventGraph.CommitAvailable compiled.graph state.1 who action := by
  rcases internalClosureAfterReady_support_cert
      compiled hinternal hsupport with
    ⟨batch, hinternalOnly, hrun, _hne⟩
  exact
    commitAvailable_reflect_before_internalOnly_availableRunFrom
      compiled hready hinternalOnly hrun hcommit

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


end ToEventGraph

end Vegas
