import Vegas.GameBridge.FOSG.StateSufficiency

/-!
# Frontier stability for FOSG event-graph rounds

The event graph exposes FOSG transitions as whole frontier rounds.  This file
records the semantic reason that those rounds describe real primitive machine
executions: executing one frontier node cannot change the read environment, and
hence cannot invalidate the legal action, of another current frontier node.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- The read environment of a frontier node is unchanged after executing a
different frontier node, for any read set contained in that node's semantic
reads. -/
theorem eventGraph_readEnvOfResult_withPatch_eq_of_frontier_reads
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {first second : ProgramNode g.prog}
    {firstPatch : ProgramField.FieldPatch g.prog}
    {hfirst : first ∈ cfg.frontier}
    {hfirstLegal : (programEventGraph g).patchLegal first firstPatch}
    {reads : Finset (ProgramField g.prog)}
    (hsecond : second ∈ cfg.frontier)
    (hreads :
      reads ⊆
        (ProgramNode.sem g.obligations second).reads)
    {availableAfter :
      ∀ field, field ∈ reads →
        (ProgramField.value? g.env
          ((cfg.withPatch firstPatch hfirst hfirstLegal).result)
          field).isSome}
    {availableBefore :
      ∀ field, field ∈ reads →
        (ProgramField.value? g.env cfg.result field).isSome} :
    ProgramField.readEnvOfResult g.env
        ((cfg.withPatch firstPatch hfirst hfirstLegal).result)
        reads availableAfter =
      ProgramField.readEnvOfResult g.env cfg.result reads availableBefore := by
  ext field hmem
  exact
    ProgramField.readEnvOfResult_value_eq_of_value?_eq
      g.env
      (left := (cfg.withPatch firstPatch hfirst hfirstLegal).result)
      (right := cfg.result)
      (availableLeft := availableAfter)
      (availableRight := availableBefore)
      (field := field) (hleft := hmem) (hright := hmem)
      (eventGraph_value?_withPatch_eq_of_frontier_read
        g (writer := first) (reader := second)
        (patch := firstPatch) hsecond (hreads hmem))

/-- Internal kernels for frontier nodes are stable under execution of a
different frontier node.  Thus the stochastic part of a frontier round is not
an artifact of the chosen linearization order. -/
theorem eventGraph_internalKernel_after_frontier_withPatch_of_ne
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {first second : ProgramNode g.prog}
    {firstPatch : ProgramField.FieldPatch g.prog}
    (hfirst : first ∈ cfg.frontier)
    (hsecond : second ∈ cfg.frontier)
    (hne : second ≠ first)
    (hfirstLegal : (programEventGraph g).patchLegal first firstPatch) :
    (programEventGraph g).internalKernel second
        ((cfg.withPatch firstPatch hfirst hfirstLegal).result) =
      (programEventGraph g).internalKernel second cfg.result := by
  classical
  have hsecondAfter :
      second ∈ (cfg.withPatch firstPatch hfirst hfirstLegal).frontier :=
    cfg.withPatch_mem_frontier_of_ne hfirst hsecond hne hfirstLegal
  change
    ProgramNode.internalKernel g.env g.obligations second
        ((cfg.withPatch firstPatch hfirst hfirstLegal).result) =
      ProgramNode.internalKernel g.env g.obligations second cfg.result
  cases hsem :
      ProgramNode.sem g.obligations second with
  | assign field expr =>
      unfold ProgramNode.internalKernel
      rw [hsem]
      let availableAfter :
          ∀ read, read ∈ expr.reads →
            (ProgramField.value? g.env
              ((cfg.withPatch firstPatch hfirst hfirstLegal).result)
              read).isSome := by
        intro read hread
        exact programReadsAvailableAtFrontier_of_wfProgram g
          (cfg.withPatch firstPatch hfirst hfirstLegal)
          hsecondAfter read
          (by simpa [EventGraph.NodeSem.reads, hsem] using hread)
      let availableBefore :
          ∀ read, read ∈ expr.reads →
            (ProgramField.value? g.env cfg.result read).isSome := by
        intro read hread
        exact programReadsAvailableAtFrontier_of_wfProgram g
          cfg hsecond read
          (by simpa [EventGraph.NodeSem.reads, hsem] using hread)
      change
        (if available :
            ∀ read, read ∈ expr.reads →
              (ProgramField.value? g.env
                ((cfg.withPatch firstPatch hfirst hfirstLegal).result)
                read).isSome then
          PMF.pure
            (ProgramField.singlePatch field
              (expr.eval
                (ProgramField.readEnvOfResult g.env
                  ((cfg.withPatch firstPatch hfirst hfirstLegal).result)
                  expr.reads available)))
        else
          PMF.pure (ProgramField.emptyPatch g.prog)) =
        (if available :
            ∀ read, read ∈ expr.reads →
              (ProgramField.value? g.env cfg.result read).isSome then
          PMF.pure
            (ProgramField.singlePatch field
              (expr.eval
                (ProgramField.readEnvOfResult g.env cfg.result
                  expr.reads available)))
        else
          PMF.pure (ProgramField.emptyPatch g.prog))
      rw [dif_pos availableAfter, dif_pos availableBefore]
      have henv :
          ProgramField.readEnvOfResult g.env
              ((cfg.withPatch firstPatch hfirst hfirstLegal).result)
              expr.reads availableAfter =
            ProgramField.readEnvOfResult g.env cfg.result
              expr.reads availableBefore :=
        eventGraph_readEnvOfResult_withPatch_eq_of_frontier_reads
          g hsecond
          (by
            intro read hread
            simpa [EventGraph.NodeSem.reads, hsem] using hread)
      rw [henv]
  | sample field dist =>
      unfold ProgramNode.internalKernel
      rw [hsem]
      let availableAfter :
          ∀ read, read ∈ dist.reads →
            (ProgramField.value? g.env
              ((cfg.withPatch firstPatch hfirst hfirstLegal).result)
              read).isSome := by
        intro read hread
        exact programReadsAvailableAtFrontier_of_wfProgram g
          (cfg.withPatch firstPatch hfirst hfirstLegal)
          hsecondAfter read
          (by simpa [EventGraph.NodeSem.reads, hsem] using hread)
      let availableBefore :
          ∀ read, read ∈ dist.reads →
            (ProgramField.value? g.env cfg.result read).isSome := by
        intro read hread
        exact programReadsAvailableAtFrontier_of_wfProgram g
          cfg hsecond read
          (by simpa [EventGraph.NodeSem.reads, hsem] using hread)
      change
        (if available :
            ∀ read, read ∈ dist.reads →
              (ProgramField.value? g.env
                ((cfg.withPatch firstPatch hfirst hfirstLegal).result)
                read).isSome then
          PMF.map
            (fun value => ProgramField.singlePatch field value)
            (dist.eval
              (ProgramField.readEnvOfResult g.env
                ((cfg.withPatch firstPatch hfirst hfirstLegal).result)
                dist.reads available))
        else
          PMF.pure (ProgramField.emptyPatch g.prog)) =
        (if available :
            ∀ read, read ∈ dist.reads →
              (ProgramField.value? g.env cfg.result read).isSome then
          PMF.map
            (fun value => ProgramField.singlePatch field value)
            (dist.eval
              (ProgramField.readEnvOfResult g.env cfg.result
                dist.reads available))
        else
          PMF.pure (ProgramField.emptyPatch g.prog))
      rw [dif_pos availableAfter, dif_pos availableBefore]
      have henv :
          ProgramField.readEnvOfResult g.env
              ((cfg.withPatch firstPatch hfirst hfirstLegal).result)
              dist.reads availableAfter =
            ProgramField.readEnvOfResult g.env cfg.result
              dist.reads availableBefore :=
        eventGraph_readEnvOfResult_withPatch_eq_of_frontier_reads
          g hsecond
          (by
            intro read hread
            simpa [EventGraph.NodeSem.reads, hsem] using hread)
      rw [henv]
  | commit owner field guard =>
      unfold ProgramNode.internalKernel
      rw [hsem]
  | reveal source target hty =>
      unfold ProgramNode.internalKernel
      rw [hsem]
      let availableAfter :
          ∀ read, read ∈ ({source} : Finset (ProgramField g.prog)) →
            (ProgramField.value? g.env
              ((cfg.withPatch firstPatch hfirst hfirstLegal).result)
              read).isSome := by
        intro read hread
        exact programReadsAvailableAtFrontier_of_wfProgram g
          (cfg.withPatch firstPatch hfirst hfirstLegal)
          hsecondAfter read
          (by simpa [EventGraph.NodeSem.reads, hsem] using hread)
      let availableBefore :
          ∀ read, read ∈ ({source} : Finset (ProgramField g.prog)) →
            (ProgramField.value? g.env cfg.result read).isSome := by
        intro read hread
        exact programReadsAvailableAtFrontier_of_wfProgram g
          cfg hsecond read
          (by simpa [EventGraph.NodeSem.reads, hsem] using hread)
      change
        (if available :
            ∀ read, read ∈ ({source} : Finset (ProgramField g.prog)) →
              (ProgramField.value? g.env
                ((cfg.withPatch firstPatch hfirst hfirstLegal).result)
                read).isSome then
          let ρ :=
            ProgramField.readEnvOfResult g.env
              ((cfg.withPatch firstPatch hfirst hfirstLegal).result)
              ({source} : Finset (ProgramField g.prog)) available
          PMF.pure
            (ProgramField.singlePatch target
              (cast (by rw [hty]) (ρ.value source (by simp))))
        else
          PMF.pure (ProgramField.emptyPatch g.prog)) =
        (if available :
            ∀ read, read ∈ ({source} : Finset (ProgramField g.prog)) →
              (ProgramField.value? g.env cfg.result read).isSome then
          let ρ :=
            ProgramField.readEnvOfResult g.env cfg.result
              ({source} : Finset (ProgramField g.prog)) available
          PMF.pure
            (ProgramField.singlePatch target
              (cast (by rw [hty]) (ρ.value source (by simp))))
        else
          PMF.pure (ProgramField.emptyPatch g.prog))
      rw [dif_pos availableAfter, dif_pos availableBefore]
      have henv :
          ProgramField.readEnvOfResult g.env
              ((cfg.withPatch firstPatch hfirst hfirstLegal).result)
              ({source} : Finset (ProgramField g.prog)) availableAfter =
            ProgramField.readEnvOfResult g.env cfg.result
              ({source} : Finset (ProgramField g.prog)) availableBefore :=
        eventGraph_readEnvOfResult_withPatch_eq_of_frontier_reads
          g hsecond
          (by
            intro read hread
            simpa [EventGraph.NodeSem.reads, hsem] using hread)
      rw [henv]

/-- Every primitive event selected for a different node in a legal syntax
frontier round is still available after this frontier node has executed. -/
theorem eventGraph_roundPrimitiveEvent_available_after_withPatch_of_ne
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {joint : JointAction (EventGraph.PlayerRoundAction (programEventGraph g))}
    (hjoint :
      JointActionLegal (EventGraph.PlayerRoundAction (programEventGraph g))
        (EventGraph.roundActive (programEventGraph g))
        EventGraph.Configuration.terminal
        (EventGraph.roundAvailable (programEventGraph g)) cfg joint)
    {first second : ProgramNode g.prog}
    {firstPatch : ProgramField.FieldPatch g.prog}
    (hfirst : first ∈ cfg.frontier)
    (hsecond : second ∈ cfg.frontier)
    (hne : second ≠ first)
    (hfirstLegal : (programEventGraph g).patchLegal first firstPatch) :
    (eventGraphMachine g).EventAvailable
      (cfg.withPatch firstPatch hfirst hfirstLegal)
      (EventGraph.roundPrimitiveEvent
        (programEventGraph g) (eventGraphMachineInterface g) joint second) := by
  classical
  cases hactor : ((programEventGraph g).sem second).actor with
  | none =>
      have hfrontierAfter :
          second ∈ (cfg.withPatch firstPatch hfirst hfirstLegal).frontier :=
        cfg.withPatch_mem_frontier_of_ne hfirst hsecond hne hfirstLegal
      have hevent :
          EventGraph.roundPrimitiveEvent
              (programEventGraph g) (eventGraphMachineInterface g)
              joint second =
            Machine.Event.internal
              (EventGraph.InternalEvent.node second :
                EventGraph.InternalEvent (programEventGraph g)) := by
        simp [EventGraph.roundPrimitiveEvent, hactor]
      rw [hevent]
      change
        (EventGraph.InternalEvent.node second :
            EventGraph.InternalEvent (programEventGraph g)) ∈
          EventGraph.availableInternal (programEventGraph g)
            (cfg.withPatch firstPatch hfirst hfirstLegal)
      exact ⟨hfrontierAfter, hactor⟩
  | some who =>
      have hactive :
          who ∈ EventGraph.roundActive (programEventGraph g) cfg :=
        (EventGraph.mem_roundActive_iff
          (programEventGraph g) cfg who).mpr
          ⟨second, hsecond, hactor⟩
      have hcoord := hjoint.2 who
      cases hmove : joint who with
      | none =>
          have hnot : who ∉ EventGraph.roundActive (programEventGraph g) cfg := by
            simpa [hmove] using hcoord
          exact False.elim (hnot hactive)
      | some action =>
          have hpair :
              who ∈ EventGraph.roundActive (programEventGraph g) cfg ∧
                action ∈
                  EventGraph.roundAvailable (programEventGraph g) cfg who := by
            simpa [hmove] using hcoord
          have hnodeLegal :
              (programEventGraph g).patchLegal second (action.patch second) ∧
                (programEventGraph g).actionLegal cfg.result second
                  (action.patch second) :=
            hpair.2 hsecond hactor
          have havailable :
              ({ node := second, patch := action.patch second } :
                EventGraph.PlayerAction (programEventGraph g) who) ∈
                EventGraph.available (programEventGraph g)
                  (cfg.withPatch firstPatch hfirst hfirstLegal) who :=
            eventGraph_available_after_frontier_withPatch_of_ne
              g who hfirst hne hfirstLegal
              ⟨hsecond, hactor, hnodeLegal.1, hnodeLegal.2⟩
          have hevent :
              EventGraph.roundPrimitiveEvent
                  (programEventGraph g) (eventGraphMachineInterface g)
                  joint second =
                Machine.Event.play who
                  ({ node := second, patch := action.patch second } :
                    EventGraph.PlayerAction (programEventGraph g) who) := by
            simp [EventGraph.roundPrimitiveEvent, hactor, hmove]
          rw [hevent]
          change
            ({ node := second, patch := action.patch second } :
              EventGraph.PlayerAction (programEventGraph g) who) ∈
              EventGraph.available (programEventGraph g)
                (cfg.withPatch firstPatch hfirst hfirstLegal) who
          exact havailable

end Vegas
