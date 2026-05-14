import Vegas.Core.ToEventGraph

/-!
# Checked-Program Graph Shape

SSA/write-field and source-induced dependency facts for `programEventGraph g`.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- Every generated source node writes its structural result field. -/
theorem programEventGraph_node_writes_structural_field
    (g : WFProgram P L) (node : ProgramNode g.prog) :
    ProgramField.writtenBy node ∈
      (ProgramNode.sem g.obligations node).writeFields :=
  ProgramNode.writtenBy_mem_writeFields g.obligations node

/-- Every generated source node writes exactly its structural result field. -/
theorem programEventGraph_writeField_eq_writtenBy
    (g : WFProgram P L) (node : ProgramNode g.prog)
    {field : ProgramField g.prog}
    (hwrite :
      field ∈ (ProgramNode.sem g.obligations node).writeFields) :
    field = ProgramField.writtenBy node :=
  ProgramNode.eq_writtenBy_of_mem_writeFields g.obligations node hwrite

/-- Membership in a generated node's write set identifies the field's
structural writer. -/
theorem programEventGraph_writer?_eq_some_of_writeField
    (g : WFProgram P L) (node : ProgramNode g.prog)
    {field : ProgramField g.prog}
    (hwrite :
      field ∈ (ProgramNode.sem g.obligations node).writeFields) :
    ProgramField.writer? field = some node :=
  ProgramNode.writer?_eq_some_of_mem_writeFields g.obligations node hwrite

/-- A generated node reads either an initial/current field or a field written
by an earlier generated node. -/
theorem programEventGraph_read_current_or_prior_write
    (g : WFProgram P L) (node : ProgramNode g.prog)
    {field : ProgramField g.prog}
    (hread : field ∈ (ProgramNode.sem g.obligations node).reads) :
    field ∈ ProgramField.currentFields g.prog ∨
      ∃ prior : ProgramNode g.prog,
        prior.rank < node.rank ∧
          field ∈ (ProgramNode.sem g.obligations prior).writeFields :=
  ProgramNode.read_current_or_prior_write g.obligations node hread

/-- If a generated node reads a field written by another generated node, the
writer is a prerequisite of the reader. -/
theorem programEventGraph_read_writer_mem_prereqs
    (g : WFProgram P L)
    {reader writer : ProgramNode g.prog} {field : ProgramField g.prog}
    (hread : field ∈ (ProgramNode.sem g.obligations reader).reads)
    (hwrite : field ∈ (ProgramNode.sem g.obligations writer).writeFields) :
    writer ∈ (programEventGraph g).prereqs reader := by
  change writer ∈ ProgramNode.prereqs g.obligations reader
  exact ProgramNode.writer_mem_prereqs_of_read_write
    g.obligations hread hwrite

/-- If a generated reveal is later than a generated commit, the commit is a
prerequisite of the reveal. This is the source-level commit/reveal information
barrier, not just a storage dependency. -/
theorem programEventGraph_priorCommit_mem_prereqs_of_reveal
    (g : WFProgram P L)
    {commit reveal : ProgramNode g.prog}
    {owner : P} {field : ProgramField g.prog}
    {guard : EventGraph.EventGuard L (ProgramField g.prog)
      (fun field => field.ty) field}
    {source target : ProgramField g.prog}
    {hty : source.ty = target.ty}
    (hcommit :
      ProgramNode.sem g.obligations commit =
        EventGraph.NodeSem.commit owner field guard)
    (hreveal :
      ProgramNode.sem g.obligations reveal =
        EventGraph.NodeSem.reveal source target hty)
    (hrank : commit.rank < reveal.rank) :
    commit ∈ (programEventGraph g).prereqs reveal := by
  classical
  change commit ∈ ProgramNode.prereqs g.obligations reveal
  exact Finset.mem_filter.mpr
    ⟨ProgramNode.mem_finset g.prog commit, hrank,
      Or.inr ⟨by rw [hreveal]; rfl, by rw [hcommit]; rfl⟩⟩

end Vegas
