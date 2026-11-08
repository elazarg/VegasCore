/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphReadout
import Vegas.Compile.EventGraphPolicy
import Vegas.Source.Forfeit
import Vegas.EventGraph.PublicationDecision

/-! # Failed publications in the terminal readout

A reveal event's output is read back as the publication cell its reveal writes.
A failed output at a player's reveal event therefore counts as a failed reveal
of that player in the decoded public outcome.
-/

noncomputable section

namespace Vegas

open Vegas.EventGraph SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]


omit [DecidableEq Player] R in
private theorem fieldRef_heq_of_field_eq {Field : Type}
    {layout : Field → EventField Player L} {first second : EventField Player L}
    (left : FieldRef layout first) (right : FieldRef layout second)
    (same : left.field = right.field) : first = second ∧ HEq left right := by
  obtain ⟨leftField, leftEq⟩ := left
  obtain ⟨rightField, rightEq⟩ := right
  change leftField = rightField at same
  subst same
  have kinds : first = second := leftEq.symm.trans rightEq
  subst kinds
  exact ⟨rfl, HEq.rfl⟩

/-- Terminal references of an earlier cell are the references it started with. -/
theorem terminalRefsWith_get_terminalRef {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {name : VarId} {cell : CellTy Player L} :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) → (refs : ContextRefs layout Γ) →
    (outputs : ∀ event, FieldRef layout (outputLayout program event)) →
    (source : HasVar Γ name cell) →
      (terminalRefsWith program refs outputs).get (terminalRef program source) =
        refs.get source
  | _, _, .ret _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, _, _, source =>
      terminalRefsWith_get_terminalRef next _ _ (.there source)
  | _, _, .commit _ _ _ _ next, _, _, source =>
      terminalRefsWith_get_terminalRef next _ _ (.there source)
  | _, _, .reveal _ _ _ _ _ _ next, _, _, source =>
      terminalRefsWith_get_terminalRef next _ _ (.there source)

/-- Every reveal event has a reveal cell of the same owner whose terminal
reference is the event's output field. -/
theorem exists_revealCell_of_event {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) → (refs : ContextRefs layout Γ) →
    (outputs : ∀ event, FieldRef layout (outputLayout program event)) →
    (event : Fin (eventCount program)) → (who : Player) →
    (outputLayout program event).IsPublication → eventOwner? program event = some who →
      ∃ cell ∈ revealCells program, cell.owner = who ∧
        ((terminalRefsWith program refs outputs).get cell.cell).field = (outputs event).field
  | _, _, .ret _, _, _, event, _, _, _ => nomatch event
  | _, _, .sample _ _ _ next, refs, outputs, event, who, publication, owned => by
      cases event using Fin.cases with
      | zero => exact publication.elim
      | succ tail =>
          exact exists_revealCell_of_event next _ _ tail who publication owned
  | _, _, .commit _ _ _ _ next, refs, outputs, event, who, publication, owned => by
      cases event using Fin.cases with
      | zero => exact publication.elim
      | succ tail =>
          exact exists_revealCell_of_event next _ _ tail who publication owned
  | _, _, .reveal _ owner _ _ _ _ next, refs, outputs, event, who, publication, owned => by
      cases event using Fin.cases with
      | zero =>
          refine ⟨_, List.mem_cons_self, Option.some.inj owned, ?_⟩
          change ((terminalRefsWith next _ _).get (terminalRef next .here)).field = _
          rw [terminalRefsWith_get_terminalRef (Field := Field) next _ _ HasVar.here]
          rfl
      | succ tail =>
          obtain ⟨cell, member, cellOwner, field⟩ :=
            exists_revealCell_of_event (layout := layout) next _ _ tail who publication owned
          exact ⟨cell, List.mem_cons_of_mem _ member, cellOwner, field⟩

omit [DecidableEq Player] R in
private theorem get?_heq {Field : Type} {layout : Field → EventField Player L}
    {first second : EventField Player L} (left : FieldRef layout first)
    (right : FieldRef layout second) (kinds : first = second) (same : HEq left right)
    (store : Store layout) : HEq (left.get? store) (right.get? store) := by
  subst kinds
  rw [eq_of_heq same]

omit [DecidableEq Player] R in
private theorem failed_of_heq {first second : EventField Player L} (kinds : first = second)
    (left : Option first.Value) (right : Option second.Value) (same : HEq left right)
    (failed : ∃ value, right = some value ∧ EventGraph.EventField.FailedValue second value) :
    ∃ value, left = some value ∧ EventGraph.EventField.FailedValue first value := by
  subst kinds
  rw [eq_of_heq same]
  exact failed

/-- **Failed publications are failed reveals.** In a terminal configuration of
the compiled graph, a failed output at a reveal event of a player counts as a
failed reveal of that player in the decoded public outcome. -/
theorem failedReveals_pos_of_failed_output {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (result : {config : (toEventGraph program).Config // config.cut.Terminal})
    (event : (toEventGraph program).EventId) (who : Player)
    (publication : ((toEventGraph program).outputLayout event).IsPublication)
    (owned : eventOwner? program event = some who)
    (failed : ∃ value, result.1.outputs event = some value ∧
      EventGraph.EventField.FailedValue _ value) :
    1 ≤ failedReveals program who (publicOutcome program (terminalConfig program result)) := by
  obtain ⟨cell, member, cellOwner, field⟩ := exists_revealCell_of_event program
    (ContextRefs.initial Γ (outputLayout program)) (outputRef program) event who publication owned
  obtain ⟨state, decoded, agrees⟩ := exists_decodeState_agrees (terminalRefs program)
    result.1.store (fun field => result.1.store_available_of_terminal result.2 field)
  have stateEq : terminalState program result = state := by
    unfold terminalState
    simp only [decoded, Option.get_some]
  have read := agrees cell.cell
  obtain ⟨kinds, sameRef⟩ := fieldRef_heq_of_field_eq ((terminalRefs program).get cell.cell)
    (outputRef program event) field
  have reads := get?_heq _ _ kinds sameRef result.1.store
  rw [read] at reads
  obtain ⟨value, valueEq, valueFailed⟩ := failed_of_heq kinds _ _ reads failed
  have cellFailed : (state.get cell.cell).isFailure = true := by
    have same : cellValue (state.get cell.cell) = value := Option.some.inj valueEq
    rw [← same] at valueFailed
    exact valueFailed
  unfold failedReveals
  apply List.length_pos_of_mem (a := cell)
  rw [List.mem_filter]
  refine ⟨member, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, cellOwner, true_and]
  unfold RevealCell.failed
  change (!(R.valueEquiv cell.payload ((sourcePublicEnv (terminalState program result)).get
    (publicRef cell.cell))).isSuccess) = true
  rw [stateEq, sourcePublicEnv_get_publicRef, Equiv.apply_symm_apply]
  cases stored : state.get cell.cell with
  | failure => rfl
  | success inner =>
      rw [stored] at cellFailed
      simp [PublicationResult.isFailure] at cellFailed

end Vegas
