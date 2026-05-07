import Vegas.Core.ToEventGraph.Obligations
import Vegas.EventGraph.ToMachine

/-!
# Checked-program event-graph construction

The canonical elaboration of checked `VegasCore` programs to event graphs,
observation/outcome projections, and the operational event-graph machine.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- Checked Vegas syntax elaborated to the canonical event graph.

This is the semantic event graph for the checked program. Source occurrences
become event nodes, and prerequisites are the causal read dependencies between
them; source order is retained only as the rank function proving acyclicity. -/
noncomputable def programEventGraph
    (g : WFProgram P L) : EventGraph P L where
  Node := ProgramNode g.prog
  Field := ProgramField g.prog
  nodeDecEq := ProgramNode.instDecidableEq g.prog
  fieldDecEq := ProgramField.instDecidableEq g.prog
  nodes := ProgramNode.finset g.prog
  fields := ProgramField.finset g.prog
  fieldTy := fun field => field.ty
  fieldOwner := fun field => field.owner
  initial := ProgramField.initialValue? g.prog g.env
  sem := ProgramNode.sem g.obligations
  prereqs := ProgramNode.prereqs g.obligations
  rank := fun node => node.rank
  prereqs_subset_nodes := by
    intro node prereq _hnode hpre
    exact (Finset.mem_filter.mp hpre).1
  prereq_rank_lt := by
    intro node prereq _hnode hpre
    exact (Finset.mem_filter.mp hpre).2.1
  read_fields_mem := by
    intro node field _hnode _hfield
    exact ProgramField.mem_finset g.prog field
  write_fields_mem := by
    intro node write _hnode hwrite
    exact ProgramField.mem_finset g.prog write.field
  no_duplicate_writes := by
    intro node field left right _hnode hleft hright hleftField hrightField
    cases hsem : ProgramNode.sem g.obligations node with
    | assign target expr =>
        simp [EventGraph.NodeSem.writes, hsem] at hleft hright
        subst left
        subst right
        rfl
    | sample target dist =>
        simp [EventGraph.NodeSem.writes, hsem] at hleft hright
        subst left
        subst right
        rfl
    | commit who target guard =>
        simp [EventGraph.NodeSem.writes, hsem] at hleft hright
        subst left
        subst right
        rfl
    | reveal source target hty =>
        simp [EventGraph.NodeSem.writes, hsem] at hleft hright
        subst left
        subst right
        rfl
  sliceLegal := ProgramNode.sliceLegal g.obligations
  actionLegal := ProgramNode.actionLegal g.env g.obligations
  internalKernel := ProgramNode.internalKernel g.env g.obligations

/-- Static read-availability invariant needed by the graph FOSG view: every
declared read of every frontier node has a value in the extensional graph
configuration. -/
def programReadsAvailableAtFrontier
    (g : WFProgram P L) : Prop :=
  ∀ (cfg : (programEventGraph g).Configuration) {node : ProgramNode g.prog},
    node ∈ cfg.frontier →
      ∀ read, read ∈
        (ProgramNode.sem g.obligations node).reads →
        (ProgramField.value? g.env cfg.result read).isSome

/-- Source graph frontier reads are available in every configuration. -/
theorem programReadsAvailableAtFrontier_of_wfProgram
    (g : WFProgram P L) :
    programReadsAvailableAtFrontier g := by
  intro cfg node hfrontier read hread
  rcases ProgramNode.read_current_or_prior_write
      g.obligations node hread with
    hcurrent | hprior
  · exact ProgramField.value?_isSome_of_initialValue? g.env
      (ProgramField.initialValue?_isSome_of_mem_currentFields
        g.prog g.env hcurrent)
  · rcases hprior with ⟨prior, hrank, hwrite⟩
    have hpre : prior ∈ (programEventGraph g).prereqs node := by
      change prior ∈
        ProgramNode.prereqs g.obligations node
      exact Finset.mem_filter.mpr
        ⟨ProgramNode.mem_finset g.prog prior, hrank,
          ⟨read, hread, hwrite⟩⟩
    have hdone : (cfg.result prior).isSome :=
      cfg.result_some_of_prereq_of_mem_frontier hfrontier hpre
    have hcfgLegal :
        ∀ {node slice},
          cfg.result node = some slice →
            ProgramNode.sliceLegal g.obligations node slice := by
      intro node slice hresult
      simpa [programEventGraph] using cfg.legal hresult
    exact ProgramNode.value?_isSome_of_completed_write
      g.env g.obligations hdone hcfgLegal hwrite

/-- Two event-graph configurations agree on every read that can affect a
generated commit guard. -/
def AgreeOnGuardVisibleReads
    (g : WFProgram P L)
    (left right : (programEventGraph g).Configuration)
    (node : ProgramNode g.prog) : Prop :=
  ∀ {owner : P} {target : ProgramField g.prog}
    {guard : EventGraph.EventGuard L (ProgramField g.prog)
      (fun field => field.ty) target},
    ProgramNode.sem g.obligations node =
        .commit owner target guard →
      ∀ read, read ∈ guard.visibleReads →
        ProgramField.value? g.env left.result read =
          ProgramField.value? g.env right.result read

theorem AgreeOnGuardVisibleReads.symm
    {g : WFProgram P L}
    {left right : (programEventGraph g).Configuration}
    {node : ProgramNode g.prog}
    (h : AgreeOnGuardVisibleReads g left right node) :
    AgreeOnGuardVisibleReads g right left node := by
  intro owner target guard hsem read hread
  exact (h hsem read hread).symm

/-- Dynamic commit legality transfers across event-graph configurations that
agree on the visible reads of the guard attached to the node. The frontier
hypothesis supplies availability of the guard reads in the target
configuration. -/
theorem eventGraph_actionLegal_of_guardVisibleValue_eq
    (g : WFProgram P L)
    {left right : (programEventGraph g).Configuration}
    {node : ProgramNode g.prog}
    {slice : ProgramField.WriteSlice g.prog}
    (hfrontierRight : node ∈ right.frontier)
    (hvisible : AgreeOnGuardVisibleReads g left right node)
    (haction :
      (programEventGraph g).actionLegal left.result node slice) :
    (programEventGraph g).actionLegal right.result node slice := by
  classical
  change
    ProgramNode.actionLegal g.env g.obligations left.result node slice at haction
  change
    ProgramNode.actionLegal g.env g.obligations right.result node slice
  cases hsem :
      ProgramNode.sem g.obligations node with
  | assign field expr =>
      simp [ProgramNode.actionLegal, hsem] at haction
  | sample field dist =>
      simp [ProgramNode.actionLegal, hsem] at haction
  | reveal source target hty =>
      simp [ProgramNode.actionLegal, hsem] at haction
  | commit owner field guard =>
      rw [ProgramNode.actionLegal, hsem] at haction ⊢
      rcases haction with
        ⟨availableLeft, value, hguardEval, hslice⟩
      have availableRight :
          ∀ read, read ∈ guard.reads →
            (ProgramField.value? g.env right.result read).isSome := by
        intro read hread
        exact programReadsAvailableAtFrontier_of_wfProgram g
          right hfrontierRight read
          (by simpa [EventGraph.NodeSem.reads, hsem] using hread)
      refine ⟨availableRight, value, ?_, hslice⟩
      let ρleft :=
        ProgramField.readEnvOfResult g.env left.result
          guard.reads availableLeft
      let ρright :=
        ProgramField.readEnvOfResult g.env right.result
          guard.reads availableRight
      have hguardEq :
          guard.eval value ρleft = guard.eval value ρright := by
        apply guard.eval_eq_of_visible_eq
        intro read hleft hright hreadVisible
        have hvalueEq :
            ProgramField.value? g.env left.result read =
              ProgramField.value? g.env right.result read := by
          exact hvisible (owner := owner) (target := field)
            (guard := guard) hsem read hreadVisible
        simpa [ρleft, ρright] using
          (ProgramField.readEnvOfResult_value_eq_of_value?_eq
            g.env (left := left.result) (right := right.result)
            (availableLeft := availableLeft)
            (availableRight := availableRight)
            (field := read) (hleft := hleft) (hright := hright)
            hvalueEq)
      rw [← hguardEq]
      exact hguardEval

/-- A current frontier node cannot be the structural writer of a field read by
another current frontier node.  If it were, the writer would be a prerequisite
of the reader, contradicting simultaneous frontier membership. -/
theorem eventGraph_writer?_ne_of_frontier_read
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {writer reader : ProgramNode g.prog} {field : ProgramField g.prog}
    (hwriterFrontier : writer ∈ cfg.frontier)
    (hreaderFrontier : reader ∈ cfg.frontier)
    (hread :
      field ∈
        (ProgramNode.sem g.obligations reader).reads) :
    ProgramField.writer? field ≠ some writer := by
  intro hfieldWriter
  rcases ProgramNode.read_current_or_prior_write
      g.obligations reader hread with
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
        g.obligations prior hpriorWrite
    rw [hfieldWriter] at hpriorWriter
    have hwriter_eq_prior : writer = prior :=
      Option.some.inj hpriorWriter
    subst prior
    have hpre :
        writer ∈ (programEventGraph g).prereqs reader := by
      change writer ∈
        ProgramNode.prereqs g.obligations reader
      exact Finset.mem_filter.mpr
        ⟨ProgramNode.mem_finset g.prog writer, hrank,
          ⟨field, hread, hpriorWrite⟩⟩
    exact
      (EventGraph.Configuration.not_prereq_of_mem_frontier
        hwriterFrontier hreaderFrontier) hpre

/-- A frontier node cannot share the frontier with a node that reads one of the
fields it writes.  This packages the `writer?` formulation in terms of the
semantic write set exposed by `NodeSem.writeFields`. -/
theorem eventGraph_writer_not_frontier_with_reader_of_read_write
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {writer reader : ProgramNode g.prog} {field : ProgramField g.prog}
    (hwriterFrontier : writer ∈ cfg.frontier)
    (hreaderFrontier : reader ∈ cfg.frontier)
    (hread :
      field ∈
        (ProgramNode.sem g.obligations reader).reads)
    (hwrite :
      field ∈
        (ProgramNode.sem g.obligations writer).writeFields) :
    False := by
  have hwriter :
      ProgramField.writer? field = some writer :=
    ProgramNode.writer?_eq_some_of_mem_writeFields
      g.obligations writer hwrite
  exact
    (eventGraph_writer?_ne_of_frontier_read g
      hwriterFrontier hreaderFrontier hread) hwriter

/-- A reveal node and a later node that reads the reveal target cannot share a
frontier.  In the current alias-writing reveal semantics, the reveal event is
the writer of the public alias; any post-reveal use must wait for that write.

This is the regression guard for the reveal-ordering invariant: changing reveal
so it no longer writes a value field must replace this dependency with an
equally explicit reveal-token dependency. -/
theorem eventGraph_reveal_not_frontier_with_reader_of_target
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {revealer reader : ProgramNode g.prog}
    {source target : ProgramField g.prog}
    {hty : source.ty = target.ty}
    (hrevealFrontier : revealer ∈ cfg.frontier)
    (hreaderFrontier : reader ∈ cfg.frontier)
    (hsem :
      ProgramNode.sem g.obligations revealer =
        EventGraph.NodeSem.reveal source target hty)
    (hread :
      target ∈
        (ProgramNode.sem g.obligations reader).reads) :
    False := by
  apply eventGraph_writer_not_frontier_with_reader_of_read_write
    g hrevealFrontier hreaderFrontier hread
  rw [hsem]
  simp [EventGraph.NodeSem.writeFields, EventGraph.NodeSem.writes,
    EventGraph.FieldWrite.field]

/-- Executing one frontier node leaves every read of another current frontier
node unchanged. -/
theorem eventGraph_value?_withResult_eq_of_frontier_read
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {writer reader : ProgramNode g.prog}
    {slice : ProgramField.WriteSlice g.prog}
    {hwriterFrontier : writer ∈ cfg.frontier}
    {hwriterLegal : (programEventGraph g).sliceLegal writer slice}
    {field : ProgramField g.prog}
    (hreaderFrontier : reader ∈ cfg.frontier)
    (hread :
      field ∈
        (ProgramNode.sem g.obligations reader).reads) :
    ProgramField.value? g.env
        ((cfg.withResult slice hwriterFrontier hwriterLegal).result) field =
      ProgramField.value? g.env cfg.result field := by
  classical
  have hne :
      ProgramField.writer? field ≠ some writer :=
    eventGraph_writer?_ne_of_frontier_read g
      hwriterFrontier hreaderFrontier hread
  simpa [EventGraph.Configuration.withResult,
    EventGraph.Configuration.updateResult] using
    (ProgramField.value?_update_of_writer?_ne
      (env := g.env) (result := cfg.result) (field := field)
      (node := writer) (slice := slice) hne)

/-- Dynamic commit legality for one frontier node is stable after executing a
different frontier node. -/
theorem eventGraph_actionLegal_after_frontier_withResult_of_ne
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {first second : ProgramNode g.prog}
    {firstSlice secondSlice : ProgramField.WriteSlice g.prog}
    (hfirst : first ∈ cfg.frontier)
    (hsecond : second ∈ cfg.frontier)
    (hne : second ≠ first)
    (hfirstLegal : (programEventGraph g).sliceLegal first firstSlice)
    (hsecondAction :
      (programEventGraph g).actionLegal cfg.result second secondSlice) :
    (programEventGraph g).actionLegal
      ((cfg.withResult firstSlice hfirst hfirstLegal).result)
      second secondSlice := by
  classical
  have hsecondAfter :
      second ∈ (cfg.withResult firstSlice hfirst hfirstLegal).frontier :=
    cfg.withResult_mem_frontier_of_ne hfirst hsecond hne hfirstLegal
  refine
    eventGraph_actionLegal_of_guardVisibleValue_eq
      g hsecondAfter ?_ hsecondAction
  intro owner target guard hsem read hreadVisible
  have hread :
      read ∈
        (ProgramNode.sem g.obligations second).reads := by
    rw [hsem]
    exact guard.visibleReads_subset_reads hreadVisible
  exact
    (eventGraph_value?_withResult_eq_of_frontier_read
      g (writer := first) (reader := second)
      (slice := firstSlice) hsecond hread).symm

/-- A player primitive event for a frontier node remains available after a
different frontier node has executed. -/
theorem eventGraph_available_after_frontier_withResult_of_ne
    (g : WFProgram P L) (who : P)
    {cfg : (programEventGraph g).Configuration}
    {first : ProgramNode g.prog}
    {firstSlice : ProgramField.WriteSlice g.prog}
    {action : EventGraph.PlayerAction (programEventGraph g) who}
    (hfirst : first ∈ cfg.frontier)
    (hne : action.node ≠ first)
    (hfirstLegal : (programEventGraph g).sliceLegal first firstSlice)
    (haction :
      action ∈ EventGraph.available (programEventGraph g) cfg who) :
    action ∈ EventGraph.available (programEventGraph g)
      (cfg.withResult firstSlice hfirst hfirstLegal) who := by
  rcases haction with ⟨hfrontier, hactor, hslice, hlegal⟩
  exact ⟨
    cfg.withResult_mem_frontier_of_ne hfirst hfrontier hne hfirstLegal,
    hactor,
    hslice,
    eventGraph_actionLegal_after_frontier_withResult_of_ne
      g hfirst hfrontier hne hfirstLegal hlegal⟩

/-- Source graph commits cannot deadlock: the generated guard carries a
satisfying action for the available read environment. -/
theorem programEventGraph_hasAvailablePlayerActions
    (g : WFProgram P L) :
    (programEventGraph g).HasAvailablePlayerActions := by
  intro cfg node who hfrontier hactor
  rcases ProgramNode.exists_actionLegal_of_reads_available
      g.env g.obligations cfg.result node
      (who := who)
      (by simpa [programEventGraph] using hactor)
      (programReadsAvailableAtFrontier_of_wfProgram g cfg hfrontier) with
    ⟨slice, hslice, haction⟩
  exact ⟨slice, hslice, haction⟩

/-- Source graph frontier rounds are stable: executing one frontier node cannot
invalidate a player action for another current frontier node. -/
theorem programEventGraph_hasStableFrontierRounds
    (g : WFProgram P L) :
    (programEventGraph g).HasStableFrontierRounds where
  availablePlayerActions := programEventGraph_hasAvailablePlayerActions g
  actionStable := by
    intro cfg first firstSlice hfirst who action hfrontier hne
      hfirstLegal haction
    exact eventGraph_available_after_frontier_withResult_of_ne
      g who hfirst hne hfirstLegal haction

/-- Public observation of the program event-graph machine.

This is the protocol transcript that every player may use for legality:
which event nodes have already produced a result, together with public field
values. It deliberately does not expose hidden field values. -/
@[ext]
structure ProgramPublicObs (g : WFProgram P L) where
  done : ProgramNode g.prog → Bool
  value? : (field : ProgramField g.prog) → Option (L.Val field.ty)

/-- Private observation of the program event-graph machine: the visible part
of the extensional field assignment. -/
@[ext]
structure ProgramPrivateObs (g : WFProgram P L) (who : P) where
  value? : (field : ProgramField g.prog) → Option (L.Val field.ty)

/-- Recover a field value from an event-graph configuration. -/
noncomputable def eventGraphConfigValue?
    (g : WFProgram P L)
    (cfg : (programEventGraph g).Configuration)
    (field : ProgramField g.prog) :
    Option (L.Val field.ty) :=
  ProgramField.value? g.env cfg.result field

/-- Terminal event-graph configurations assign a value to every source
storage field. -/
theorem eventGraphConfigValue?_isSome_of_terminal
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    (hterminal : cfg.terminal)
    (field : ProgramField g.prog) :
    (eventGraphConfigValue? g cfg field).isSome := by
  classical
  cases hsource : ProgramField.source field with
  | inl current =>
      have hfield :
          field = ProgramField.ofCurrent g.prog current :=
        ProgramField.eq_ofCurrent_of_source_eq_inl hsource
      subst field
      exact ProgramField.value?_isSome_of_initialValue? g.env
        (ProgramField.initialValue?_isSome_of_mem_currentFields
          g.prog g.env
          (ProgramField.ofCurrent_mem_currentFields g.prog current))
  | inr writer =>
      have hfield :
          field = ProgramField.writtenBy writer :=
        ProgramField.eq_writtenBy_of_source_eq_inr hsource
      subst field
      have hnode : writer ∈ (programEventGraph g).nodes := by
        change writer ∈ ProgramNode.finset g.prog
        exact ProgramNode.mem_finset g.prog writer
      have hdoneMem : writer ∈ (programEventGraph g).done cfg.result :=
        hterminal hnode
      have hdone : (cfg.result writer).isSome :=
        ((programEventGraph g).mem_done_iff cfg.result writer).mp hdoneMem |>.2
      exact ProgramNode.value?_isSome_of_completed_write
        g.env g.obligations hdone
        (by
          intro node slice hresult
          simpa [programEventGraph] using cfg.legal hresult)
        (ProgramNode.writtenBy_mem_writeFields g.obligations writer)

/-- Terminal event-graph configurations assemble the final source
environment. -/
theorem eventGraph_finalEnv?_isSome_of_terminal
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    (hterminal : cfg.terminal) :
    (ProgramField.finalEnv? g.prog (eventGraphConfigValue? g cfg)).isSome := by
  classical
  unfold ProgramField.finalEnv?
  rw [dif_pos]
  · simp
  · intro field
    exact eventGraphConfigValue?_isSome_of_terminal g hterminal
      (ProgramField.ofFinal g.prog field)

/-- Public observation for the program event-graph machine. -/
noncomputable def eventGraphPublicView
    (g : WFProgram P L)
    (cfg : (programEventGraph g).Configuration) :
    ProgramPublicObs g where
  done := fun node => (cfg.result node).isSome
  value? := fun field =>
    if field.owner = none then
      eventGraphConfigValue? g cfg field
    else
      none

/-- Player observation for the program event-graph machine. -/
noncomputable def eventGraphObserve
    (g : WFProgram P L) (who : P)
    (cfg : (programEventGraph g).Configuration) :
    ProgramPrivateObs g who where
  value? := fun field =>
    if field.VisibleTo who then
      eventGraphConfigValue? g cfg field
    else
      none

theorem eventGraphPublicView_done_eq_of_eq
    (g : WFProgram P L)
    {left right : (programEventGraph g).Configuration}
    (hobs : eventGraphPublicView g left = eventGraphPublicView g right)
    (node : ProgramNode g.prog) :
    (left.result node).isSome = (right.result node).isSome := by
  have h := congrArg (fun obs => obs.done node) hobs
  simpa [eventGraphPublicView] using h

theorem eventGraphPublicView_frontier_eq_of_eq
    (g : WFProgram P L)
    {left right : (programEventGraph g).Configuration}
    (hobs : eventGraphPublicView g left = eventGraphPublicView g right) :
    left.frontier = right.frontier := by
  classical
  apply Finset.ext
  intro node
  constructor
  · intro hnode
    rw [EventGraph.Configuration.mem_frontier_iff] at hnode ⊢
    refine ⟨hnode.1, ?_, ?_⟩
    · have hsome :=
        eventGraphPublicView_done_eq_of_eq g hobs node
      have hnone :
          (left.result node).isNone = (right.result node).isNone := by
        cases hleft : left.result node <;>
          cases hright : right.result node <;>
            simp [hleft, hright] at hsome ⊢
      simpa [hnone] using hnode.2.1
    · intro prereq hpre
      have hdone := hnode.2.2 hpre
      have hdoneData :=
        ((programEventGraph g).mem_done_iff left.result prereq).mp hdone
      have hsome :=
        eventGraphPublicView_done_eq_of_eq g hobs prereq
      have hsomeRight : (right.result prereq).isSome := by
        simpa [hsome] using hdoneData.2
      exact ((programEventGraph g).mem_done_iff right.result prereq).mpr
        ⟨hdoneData.1, hsomeRight⟩
  · intro hnode
    rw [EventGraph.Configuration.mem_frontier_iff] at hnode ⊢
    refine ⟨hnode.1, ?_, ?_⟩
    · have hsome :=
        eventGraphPublicView_done_eq_of_eq g hobs node
      have hnone :
          (left.result node).isNone = (right.result node).isNone := by
        cases hleft : left.result node <;>
          cases hright : right.result node <;>
            simp [hleft, hright] at hsome ⊢
      simpa [hnone] using hnode.2.1
    · intro prereq hpre
      have hdone := hnode.2.2 hpre
      have hdoneData :=
        ((programEventGraph g).mem_done_iff right.result prereq).mp hdone
      have hsome :=
        eventGraphPublicView_done_eq_of_eq g hobs prereq
      have hsomeLeft : (left.result prereq).isSome := by
        simpa [hsome] using hdoneData.2
      exact ((programEventGraph g).mem_done_iff left.result prereq).mpr
        ⟨hdoneData.1, hsomeLeft⟩

theorem eventGraphObserve_value?_eq_of_eq
    (g : WFProgram P L) (who : P)
    {left right : (programEventGraph g).Configuration}
    (hobs : eventGraphObserve g who left = eventGraphObserve g who right)
    {field : ProgramField g.prog}
    (hvisible : field.VisibleTo who) :
    eventGraphConfigValue? g left field =
      eventGraphConfigValue? g right field := by
  have h := congrArg (fun obs => obs.value? field) hobs
  simpa [eventGraphObserve, hvisible] using h

/-- Dynamic action legality for a commit transfers across configurations that
agree on the committing player's observation, provided the target node is still
on the frontier.  The only nontrivial case is a commit guard: generated graph
guards are invariant under changes to hidden reads outside the player's view. -/
theorem eventGraph_actionLegal_of_observe_eq
    (g : WFProgram P L) (who : P)
    {left right : (programEventGraph g).Configuration}
    {node : ProgramNode g.prog}
    {slice : ProgramField.WriteSlice g.prog}
    (hfrontierRight : node ∈ right.frontier)
    (hactor :
      ((programEventGraph g).sem node).actor = some who)
    (hobs : eventGraphObserve g who left = eventGraphObserve g who right)
    (haction :
      (programEventGraph g).actionLegal left.result node slice) :
    (programEventGraph g).actionLegal right.result node slice := by
  classical
  change
    (ProgramNode.sem g.obligations node).actor = some who at hactor
  change
    ProgramNode.actionLegal g.env g.obligations left.result node slice at haction
  change
    ProgramNode.actionLegal g.env g.obligations right.result node slice
  cases hsem :
      ProgramNode.sem g.obligations node with
  | assign field expr =>
      simp [EventGraph.NodeSem.actor, hsem] at hactor
  | sample field dist =>
      simp [EventGraph.NodeSem.actor, hsem] at hactor
  | reveal source target hty =>
      simp [EventGraph.NodeSem.actor, hsem] at hactor
  | commit owner field guard =>
      have howner : owner = who := by
        simpa [EventGraph.NodeSem.actor, hsem] using hactor
      subst owner
      rw [ProgramNode.actionLegal, hsem] at haction ⊢
      rcases haction with
        ⟨availableLeft, value, hguardEval, hslice⟩
      have availableRight :
          ∀ read, read ∈ guard.reads →
            (ProgramField.value? g.env right.result read).isSome := by
        intro read hread
        exact programReadsAvailableAtFrontier_of_wfProgram g
          right hfrontierRight read
          (by simpa [EventGraph.NodeSem.reads, hsem] using hread)
      refine ⟨availableRight, value, ?_, hslice⟩
      let ρleft :=
        ProgramField.readEnvOfResult g.env left.result
          guard.reads availableLeft
      let ρright :=
        ProgramField.readEnvOfResult g.env right.result
          guard.reads availableRight
      have hguardEq :
          guard.eval value ρleft = guard.eval value ρright := by
        apply guard.eval_eq_of_visible_eq
        intro read hleft hright hvisible
        have hreadVisible :
            read.VisibleTo who :=
          ProgramNode.guard_visibleReads_owner_of_sem_commit
            g.obligations node hsem read hvisible
        have hvalueEq :
            ProgramField.value? g.env left.result read =
              ProgramField.value? g.env right.result read := by
          have hsyntax :=
            eventGraphObserve_value?_eq_of_eq g who hobs hreadVisible
          simpa [eventGraphConfigValue?, programEventGraph,
            EventGraph.value?, ProgramField.value?] using hsyntax
        simpa [ρleft, ρright] using
          (ProgramField.readEnvOfResult_value_eq_of_value?_eq
            g.env (left := left.result) (right := right.result)
            (availableLeft := availableLeft)
            (availableRight := availableRight)
            (field := read) (hleft := hleft) (hright := hright)
            hvalueEq)
      rw [← hguardEq]
      exact hguardEval

/-- Player action availability in the event graph is determined by the public
transcript together with the acting player's private observation. -/
theorem eventGraph_available_eq_of_observation_eq
    (g : WFProgram P L) (who : P)
    {left right : (programEventGraph g).Configuration}
    (hpriv : eventGraphObserve g who left = eventGraphObserve g who right)
    (hpub : eventGraphPublicView g left = eventGraphPublicView g right) :
    EventGraph.available (programEventGraph g) left who =
      EventGraph.available (programEventGraph g) right who := by
  classical
  ext action
  constructor
  · intro haction
    rcases haction with ⟨hfrontier, hactor, hslice, hlegal⟩
    have hfrontierRight : action.node ∈ right.frontier := by
      simpa [eventGraphPublicView_frontier_eq_of_eq g hpub] using hfrontier
    exact ⟨hfrontierRight, hactor, hslice,
      eventGraph_actionLegal_of_observe_eq g who hfrontierRight
        hactor hpriv hlegal⟩
  · intro haction
    rcases haction with ⟨hfrontier, hactor, hslice, hlegal⟩
    have hfrontierLeft : action.node ∈ left.frontier := by
      simpa [eventGraphPublicView_frontier_eq_of_eq g hpub] using hfrontier
    exact ⟨hfrontierLeft, hactor, hslice,
      eventGraph_actionLegal_of_observe_eq g who hfrontierLeft
        hactor hpriv.symm hlegal⟩

/-- Outcome projection for the program event-graph machine. Nonterminal or
ill-assembled configurations project to the default zero outcome. -/
noncomputable def eventGraphOutcome
    (g : WFProgram P L)
    (cfg : (programEventGraph g).Configuration) : Outcome P :=
  match ProgramField.finalEnv? g.prog (eventGraphConfigValue? g cfg) with
  | some env => evalPayoffs (ProgramField.finalPayoffs g.prog) env
  | none => 0

/-- Terminal event-graph configurations evaluate outcomes from the
assembled final source environment. -/
theorem eventGraphOutcome_eq_evalPayoffs_of_terminal
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    (hterminal : cfg.terminal) :
    ∃ env : VEnv L (ProgramField.finalVCtx g.prog),
      ProgramField.finalEnv? g.prog (eventGraphConfigValue? g cfg) = some env ∧
        eventGraphOutcome g cfg =
          evalPayoffs (ProgramField.finalPayoffs g.prog) env := by
  rcases Option.isSome_iff_exists.mp
      (eventGraph_finalEnv?_isSome_of_terminal g hterminal) with
    ⟨env, henv⟩
  refine ⟨env, henv, ?_⟩
  simp [eventGraphOutcome, henv]

/-- Observation/outcome interface for the program event-graph machine. -/
noncomputable def eventGraphMachineInterface
    (g : WFProgram P L) :
    EventGraph.MachineInterface (programEventGraph g) where
  Public := ProgramPublicObs g
  Obs := fun who => ProgramPrivateObs g who
  Outcome := Outcome P
  publicView := eventGraphPublicView g
  observe := eventGraphObserve g
  outcome := eventGraphOutcome g
  utility := fun outcome who => (outcome who : ℝ)

/-- Canonical event-graph machine elaborated from a checked Vegas program. -/
noncomputable def eventGraphMachine
    (g : WFProgram P L) : Machine P :=
  (programEventGraph g).toMachine (eventGraphMachineInterface g)

end Vegas
