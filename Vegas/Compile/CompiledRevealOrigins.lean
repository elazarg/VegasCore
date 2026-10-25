/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.CompiledReadoutSuffix
import Vegas.Compile.EventGraphPolicy
import Vegas.Source.Forfeit

/-! # Actual compiled origins of terminal source reveal cells

The reveal cells counted by source payoffs are written by the program's own
publication events. Their terminal references retain the corresponding output
field and owner, independently of execution or initial-context publications.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every source reveal cell retains its actual owned compiled output reference. -/
theorem terminalRefsWith_revealCell_output {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (outputs : ∀ event, FieldRef layout (outputLayout program event))
      (cell : RevealCell program.terminalCtx), cell ∈ revealCells program →
      ∃ event : Fin (eventCount program),
        outputLayout program event = .publication cell.payload ∧
        eventOwner? program event = some cell.owner ∧
        ((terminalRefsWith program refs outputs).get cell.cell).field = (outputs event).field
  | _, _, .ret _, _, _, _, member => by cases member
  | _, _, .sample name fresh distribution next, refs, outputs, cell, member => by
      obtain ⟨event, kind, acting, field⟩ := terminalRefsWith_revealCell_output next
        (refs.cons (outputs ⟨0, by simp [eventCount]⟩))
        (fun event => outputs event.succ) cell member
      exact ⟨event.succ, kind, acting, field⟩
  | _, _, .commit name owner fresh guard next, refs, outputs, cell, member => by
      obtain ⟨event, kind, acting, field⟩ := terminalRefsWith_revealCell_output next
        (refs.cons (outputs ⟨0, by simp [eventCount]⟩))
        (fun event => outputs event.succ) cell member
      exact ⟨event.succ, kind, acting, field⟩
  | _, _, .reveal name owner sourceName fresh source unresolved next, refs, outputs, cell,
      member => by
      rcases List.mem_cons.mp member with rfl | later
      · refine ⟨⟨0, by simp [eventCount]⟩, rfl, rfl, ?_⟩
        exact congrArg FieldRef.field (terminalRefsWith_get_terminalRef next _ _ HasVar.here)
      · obtain ⟨event, kind, acting, field⟩ := terminalRefsWith_revealCell_output next
          (refs.cons (outputs ⟨0, by simp [eventCount]⟩))
          (fun event => outputs event.succ) cell later
        exact ⟨event.succ, kind, acting, field⟩

end Vegas
