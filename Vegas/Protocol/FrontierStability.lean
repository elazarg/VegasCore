import Vegas.Protocol.StateSufficiency

/-!
# Frontier stability for syntax-graph rounds

The syntax graph exposes FOSG transitions as whole frontier rounds.  This file
records the semantic reason that those rounds describe real primitive machine
executions: executing one frontier node cannot change the read environment, and
hence cannot invalidate the legal action, of another current frontier node.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

attribute [local instance] ProtocolGraph.nodeDecEq
attribute [local instance] ProtocolGraph.fieldDecEq

/-- A current frontier node cannot be the structural writer of a field read by
another current frontier node.  If it were, the writer would be a prerequisite
of the reader, contradicting simultaneous frontier membership. -/
theorem syntaxGraph_writer?_ne_of_frontier_read
    (g : WFProgram P L)
    {cfg : (syntaxProtocolGraph g).Configuration}
    {writer reader : ProgramNode g.prog} {field : ProgramField g.prog}
    (hwriterFrontier : writer ∈ cfg.frontier)
    (hreaderFrontier : reader ∈ cfg.frontier)
    (hread :
      field ∈
        (ProgramNode.sem g.wctx g.wf.1 g.wf.2.2
          g.legal g.normalized reader).reads) :
    ProgramField.writer? field ≠ some writer := by
  intro hfieldWriter
  rcases ProgramNode.read_current_or_prior_write
      g.wctx g.wf.1 g.wf.2.2 g.legal g.normalized reader hread with
    hcurrent | hprior
  · have hnone :
        ProgramField.writer? field = none :=
      ProgramField.writer?_eq_none_of_mem_currentFields hcurrent
    rw [hfieldWriter] at hnone
    simp at hnone
  · rcases hprior with ⟨prior, hrank, hpriorWrite⟩
    have hpriorWriter :
        ProgramField.writer? field = some prior :=
      ProgramNode.writer?_eq_some_of_mem_writeFields
        g.wctx g.wf.1 g.wf.2.2 g.legal g.normalized prior hpriorWrite
    rw [hfieldWriter] at hpriorWriter
    have hwriter_eq_prior : writer = prior :=
      Option.some.inj hpriorWriter
    subst prior
    have hpre :
        writer ∈ (syntaxProtocolGraph g).prereqs reader := by
      change writer ∈
        ProgramNode.prereqs g.wctx g.wf.1 g.wf.2.2
          g.legal g.normalized reader
      exact Finset.mem_filter.mpr
        ⟨ProgramNode.mem_finset g.prog writer, hrank,
          ⟨field, hread, hpriorWrite⟩⟩
    exact
      (ProtocolGraph.Configuration.not_prereq_of_mem_frontier
        hwriterFrontier hreaderFrontier) hpre

/-- Executing one frontier node leaves every read of another current frontier
node unchanged. -/
theorem syntaxGraph_value?_withResult_eq_of_frontier_read
    (g : WFProgram P L)
    {cfg : (syntaxProtocolGraph g).Configuration}
    {writer reader : ProgramNode g.prog}
    {slice : ProgramField.WriteSlice g.prog}
    {hwriterFrontier : writer ∈ cfg.frontier}
    {hwriterLegal : (syntaxProtocolGraph g).sliceLegal writer slice}
    {field : ProgramField g.prog}
    (hreaderFrontier : reader ∈ cfg.frontier)
    (hread :
      field ∈
        (ProgramNode.sem g.wctx g.wf.1 g.wf.2.2
          g.legal g.normalized reader).reads) :
    ProgramField.value? g.env
        ((cfg.withResult slice hwriterFrontier hwriterLegal).result) field =
      ProgramField.value? g.env cfg.result field := by
  classical
  have hne :
      ProgramField.writer? field ≠ some writer :=
    syntaxGraph_writer?_ne_of_frontier_read g
      hwriterFrontier hreaderFrontier hread
  simpa [ProtocolGraph.Configuration.withResult,
    ProtocolGraph.Configuration.updateResult] using
    (ProgramField.value?_update_of_writer?_ne
      (env := g.env) (result := cfg.result) (field := field)
      (node := writer) (slice := slice) hne)

/-- Dynamic commit legality for one frontier node is stable after executing a
different frontier node. -/
theorem syntaxGraph_actionLegal_after_frontier_withResult_of_ne
    (g : WFProgram P L)
    {cfg : (syntaxProtocolGraph g).Configuration}
    {first second : ProgramNode g.prog}
    {firstSlice secondSlice : ProgramField.WriteSlice g.prog}
    (hfirst : first ∈ cfg.frontier)
    (hsecond : second ∈ cfg.frontier)
    (hne : second ≠ first)
    (hfirstLegal : (syntaxProtocolGraph g).sliceLegal first firstSlice)
    (hsecondAction :
      (syntaxProtocolGraph g).actionLegal cfg.result second secondSlice) :
    (syntaxProtocolGraph g).actionLegal
      ((cfg.withResult firstSlice hfirst hfirstLegal).result)
      second secondSlice := by
  classical
  have hsecondAfter :
      second ∈ (cfg.withResult firstSlice hfirst hfirstLegal).frontier :=
    cfg.withResult_mem_frontier_of_ne hfirst hsecond hne hfirstLegal
  refine
    syntaxGraph_actionLegal_of_guardVisibleValue_eq
      g hsecondAfter ?_ hsecondAction
  intro owner target guard hsem read hreadVisible
  have hread :
      read ∈
        (ProgramNode.sem g.wctx g.wf.1 g.wf.2.2
          g.legal g.normalized second).reads := by
    rw [hsem]
    exact guard.visibleReads_subset_reads hreadVisible
  exact
    (syntaxGraph_value?_withResult_eq_of_frontier_read
      g (writer := first) (reader := second)
      (slice := firstSlice) hsecond hread).symm

/-- A player primitive event for a frontier node remains available after a
different frontier node has executed. -/
theorem syntaxGraph_available_after_frontier_withResult_of_ne
    (g : WFProgram P L) (who : P)
    {cfg : (syntaxProtocolGraph g).Configuration}
    {first : ProgramNode g.prog}
    {firstSlice : ProgramField.WriteSlice g.prog}
    {action : ProtocolGraph.PlayerAction (syntaxProtocolGraph g) who}
    (hfirst : first ∈ cfg.frontier)
    (hne : action.node ≠ first)
    (hfirstLegal : (syntaxProtocolGraph g).sliceLegal first firstSlice)
    (haction :
      action ∈ ProtocolGraph.available (syntaxProtocolGraph g) cfg who) :
    action ∈ ProtocolGraph.available (syntaxProtocolGraph g)
      (cfg.withResult firstSlice hfirst hfirstLegal) who := by
  rcases haction with ⟨hfrontier, hactor, hslice, hlegal⟩
  exact ⟨
    cfg.withResult_mem_frontier_of_ne hfirst hfrontier hne hfirstLegal,
    hactor,
    hslice,
    syntaxGraph_actionLegal_after_frontier_withResult_of_ne
      g hfirst hfrontier hne hfirstLegal hlegal⟩

/-- Every primitive event selected for a different node in a legal syntax
frontier round is still available after this frontier node has executed. -/
theorem syntaxGraph_roundPrimitiveEvent_available_after_withResult_of_ne
    (g : WFProgram P L)
    {cfg : (syntaxProtocolGraph g).Configuration}
    {joint : JointAction (ProtocolGraph.PlayerRoundAction (syntaxProtocolGraph g))}
    (hjoint :
      JointActionLegal (ProtocolGraph.PlayerRoundAction (syntaxProtocolGraph g))
        (ProtocolGraph.roundActive (syntaxProtocolGraph g))
        ProtocolGraph.Configuration.terminal
        (ProtocolGraph.roundAvailable (syntaxProtocolGraph g)) cfg joint)
    {first second : ProgramNode g.prog}
    {firstSlice : ProgramField.WriteSlice g.prog}
    (hfirst : first ∈ cfg.frontier)
    (hsecond : second ∈ cfg.frontier)
    (hne : second ≠ first)
    (hfirstLegal : (syntaxProtocolGraph g).sliceLegal first firstSlice) :
    (syntaxGraphMachine g).EventAvailable
      (cfg.withResult firstSlice hfirst hfirstLegal)
      (ProtocolGraph.roundPrimitiveEvent
        (syntaxProtocolGraph g) (syntaxGraphMachineInterface g) joint second) := by
  classical
  cases hactor : ((syntaxProtocolGraph g).sem second).actor with
  | none =>
      have hfrontierAfter :
          second ∈ (cfg.withResult firstSlice hfirst hfirstLegal).frontier :=
        cfg.withResult_mem_frontier_of_ne hfirst hsecond hne hfirstLegal
      have hevent :
          ProtocolGraph.roundPrimitiveEvent
              (syntaxProtocolGraph g) (syntaxGraphMachineInterface g)
              joint second =
            Machine.Event.internal
              (ProtocolGraph.InternalEvent.node second :
                ProtocolGraph.InternalEvent (syntaxProtocolGraph g)) := by
        simp [ProtocolGraph.roundPrimitiveEvent, hactor]
      rw [hevent]
      change
        (ProtocolGraph.InternalEvent.node second :
            ProtocolGraph.InternalEvent (syntaxProtocolGraph g)) ∈
          ProtocolGraph.availableInternal (syntaxProtocolGraph g)
            (cfg.withResult firstSlice hfirst hfirstLegal)
      exact ⟨hfrontierAfter, hactor⟩
  | some who =>
      have hactive :
          who ∈ ProtocolGraph.roundActive (syntaxProtocolGraph g) cfg :=
        (ProtocolGraph.mem_roundActive_iff
          (syntaxProtocolGraph g) cfg who).mpr
          ⟨second, hsecond, hactor⟩
      have hcoord := hjoint.2 who
      cases hmove : joint who with
      | none =>
          have hnot : who ∉ ProtocolGraph.roundActive (syntaxProtocolGraph g) cfg := by
            simpa [hmove] using hcoord
          exact False.elim (hnot hactive)
      | some action =>
          have hpair :
              who ∈ ProtocolGraph.roundActive (syntaxProtocolGraph g) cfg ∧
                action ∈
                  ProtocolGraph.roundAvailable (syntaxProtocolGraph g) cfg who := by
            simpa [hmove] using hcoord
          have hnodeLegal :
              (syntaxProtocolGraph g).sliceLegal second (action.slice second) ∧
                (syntaxProtocolGraph g).actionLegal cfg.result second
                  (action.slice second) :=
            hpair.2 hsecond hactor
          have havailable :
              ({ node := second, slice := action.slice second } :
                ProtocolGraph.PlayerAction (syntaxProtocolGraph g) who) ∈
                ProtocolGraph.available (syntaxProtocolGraph g)
                  (cfg.withResult firstSlice hfirst hfirstLegal) who :=
            syntaxGraph_available_after_frontier_withResult_of_ne
              g who hfirst hne hfirstLegal
              ⟨hsecond, hactor, hnodeLegal.1, hnodeLegal.2⟩
          have hevent :
              ProtocolGraph.roundPrimitiveEvent
                  (syntaxProtocolGraph g) (syntaxGraphMachineInterface g)
                  joint second =
                Machine.Event.play who
                  ({ node := second, slice := action.slice second } :
                    ProtocolGraph.PlayerAction (syntaxProtocolGraph g) who) := by
            simp [ProtocolGraph.roundPrimitiveEvent, hactor, hmove]
          rw [hevent]
          change
            ({ node := second, slice := action.slice second } :
              ProtocolGraph.PlayerAction (syntaxProtocolGraph g) who) ∈
              ProtocolGraph.available (syntaxProtocolGraph g)
                (cfg.withResult firstSlice hfirst hfirstLegal) who
          exact havailable

end Vegas
