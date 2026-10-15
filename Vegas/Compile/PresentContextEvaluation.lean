/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphEvaluation
import Vegas.Source.IntendedPlay
import Vegas.Source.RegistryFailureExtension

/-! # Compiled guard evaluation from present typed source references -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Every physical value that is present has its source meaning. References
for independent publications may still be absent. -/
def ContextRefs.PresentAgrees {Field : Type} {layout : Field → EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ) (state : State L Γ)
    (store : EventGraph.Store layout) : Prop :=
  ∀ {name cell} (selected : HasVar Γ name cell) value,
    (refs.get selected).get? store = some value → value = cellValue (state.get selected)

namespace ContextRefs

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Full typed agreement supplies agreement on every present field. -/
theorem Agrees.present {Field : Type} {layout : Field → EventField Player L}
    {Γ : SourceCtx Player L} {refs : ContextRefs layout Γ} {state : State L Γ}
    {store : EventGraph.Store layout} (agree : refs.Agrees state store) :
    refs.PresentAgrees state store := by
  intro name cell selected value actual
  exact Option.some.inj (actual.symm.trans (agree selected))

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Read availability turns present agreement into the exact typed source read. -/
theorem PresentAgrees.get_of_isSome {Field : Type}
    {layout : Field → EventField Player L} {Γ : SourceCtx Player L}
    {refs : ContextRefs layout Γ} {state : State L Γ} {store : EventGraph.Store layout}
    (agree : refs.PresentAgrees state store) {name cell} (selected : HasVar Γ name cell)
    (available : ((refs.get selected).get? store).isSome = true) :
    (refs.get selected).get? store = some (cellValue (state.get selected)) := by
  cases actual : (refs.get selected).get? store with
  | none => simp only [actual, Option.isSome_none, Bool.false_eq_true] at available
  | some value => exact congrArg some (agree selected value actual)

end ContextRefs

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- An available tentative publication operand has its exact source meaning. -/
theorem revealOperand_get_of_present {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {Γ : SourceCtx Player L}
    (refs : ContextRefs layout Γ) (state : State L Γ) (store : EventGraph.Store layout)
    (agree : refs.PresentAgrees state store) {published : VarId} {payload : L.Ty}
    (proposal : PublicationResult (L.Val payload)) {name : VarId} {τ : L.Ty}
    (cell : HasVar ((published, .publication payload) :: Γ) name (.publication τ))
    (available : ((revealOperand refs cell).get? store proposal).isSome = true) :
    (revealOperand refs cell).get? store proposal =
      some ((Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload)
        proposal state).get cell) := by
  cases cell with
  | here => rfl
  | there cell => exact agree.get_of_isSome cell available

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- The compiler's published guard reads need agreement only at references
which this actual guard operand can evaluate. -/
theorem compileGuardRead_get_of_present {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {Γ : SourceCtx Player L}
    (refs : ContextRefs layout Γ) (state : State L Γ) (store : EventGraph.Store layout)
    (agree : refs.PresentAgrees state store) {published : VarId} {payload : L.Ty}
    (proposal : PublicationResult (L.Val payload))
    (revealed : Revelations ((published, .publication payload) :: Γ))
    {author : Player} {τ : L.Ty}
    (read : SourceGuardRead ((published, .publication payload) :: Γ) author τ)
    (isRevealed : read.revealed revealed = true)
    (available : ((compileGuardRead refs revealed read isRevealed).get?
      store proposal).isSome = true) :
    (compileGuardRead refs revealed read isRevealed).get? store proposal =
      some (read.result revealed
        (Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload)
          proposal state)) := by
  cases read with
  | publicData cell =>
      cases cell with
      | there cell =>
          change (((refs.get cell).get? store).map PublicationResult.success).isSome = true
            at available
          rw [Option.isSome_map] at available
          have stored := agree.get_of_isSome cell available
          change ((refs.get cell).get? store).map PublicationResult.success = _
          rw [stored]
          rfl
  | publication cell =>
      exact revealOperand_get_of_present refs state store agree proposal cell available
  | commitment cell =>
      simp only [compileGuardRead] at available ⊢
      split at *
      · next publication revelation =>
          simp only [SourceGuardRead.result, revelation, Revelation.result]
          exact revealOperand_get_of_present refs state store agree proposal publication available
      · next revelation =>
          simp [SourceGuardRead.revealed, revelation, Revelation.isRevealed] at isRevealed

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Available reads of one compiled obligation suffice for its exact verdict. -/
theorem compileGuard_eval?_of_present {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {Γ : SourceCtx Player L}
    (refs : ContextRefs layout Γ) (state : State L Γ) (store : EventGraph.Store layout)
    (agree : refs.PresentAgrees state store) {published : VarId} {payload : L.Ty}
    (proposal : PublicationResult (L.Val payload))
    (revealed : Revelations ((published, .publication payload) :: Γ))
    (obligation : Obligation (Player := Player) (L := L) ((published, .publication payload) :: Γ))
    (isRevealed : obligation.revealed revealed = true)
    (available : ∀ field ∈ (compileGuard refs revealed obligation isRevealed).readFields,
      (store field).isSome = true) :
    (compileGuard refs revealed obligation isRevealed).eval? store proposal =
      some (obligation.accepts revealed
        (Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload)
          proposal state)) := by
  let check := compileGuard refs revealed obligation isRevealed
  apply GuardCheck.eval?_eq_of_reads
  · refine compileGuardRead_get_of_present refs state store agree proposal revealed
      (.commitment obligation.source) _ ?_
    exact check.subjectRead.get?_isSome store proposal
      (fun field found => available field (check.subject_mem field found))
  · intro name input source read
    refine compileGuardRead_get_of_present refs state store agree proposal revealed
      (obligation.guard.reads source) _ ?_
    exact (check.reads source read).get?_isSome store proposal
      (fun field found => available field (check.reads_mem source read field found))

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Every member check's footprint is contained in the list footprint. -/
theorem EventGraph.GuardCheck.readFields_subset_listReadFields {Field : Type}
    [DecidableEq Field] {layout : Field → EventField Player L} {payload : L.Ty}
    (checks : List (GuardCheck layout payload)) (check : GuardCheck layout payload)
    (member : check ∈ checks) : check.readFields ⊆ GuardCheck.listReadFields checks := by
  induction checks with
  | nil => exact (List.not_mem_nil member).elim
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Finset.subset_union_left
      · exact (ih member).trans Finset.subset_union_right

/-- An intended guarded publication succeeds at any partial store agreeing on
its present source fields when the actual node's footprint is available. -/
theorem resolveOutput_of_present_intended {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {Γ : SourceCtx Player L}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (refs : ContextRefs layout Γ) (config : SourceProgram.Config Player L Γ)
    (registry : Registry Γ) (selected : HasVar Γ name (.commitment owner payload))
    (store : EventGraph.Store layout) (agree : refs.PresentAgrees config.state store)
    (valid : Registry.FailureExtension config.registry registry config.state)
    {unresolved : Finset VarId} (intended : config.Intended unresolved)
    (available : ∀ field ∈ (EventCode.resolve owner payload (refs.get selected)
      (compileChecks (published := published) refs registry
        config.revelations selected)).readFields,
      (store field).isSome = true) :
    ∃ value : L.Val payload, EventCode.resolveOutput? (refs.get selected)
      (compileChecks (published := published) refs registry config.revelations selected)
      true store = some (.success value) := by
  classical
  let revelations : Revelations Γ := config.revelations
  let proposal : PublicationResult (L.Val payload) := config.state.get selected
  have bindingPresent := (refs.get selected).get?_isSome store
    (available _ (Finset.mem_insert_self _ _))
  have boundRead := agree.get_of_isSome selected bindingPresent
  change (refs.get selected).get? store =
    some proposal at boundRead
  have failures : Revelations.PreservesFailures revelations config.state := by
    intro other τ otherName source failed
    obtain ⟨value, bound⟩ := intended.bound source
    rw [bound] at failed
    cases failed
  have checked := valid.completedBy_all_eq revelations failures intended.unique selected
    (published := published) true
  dsimp only at checked
  simp only [↓reduceIte] at checked
  have accepted := checked.symm.trans (intended.completed_accept (published := published) selected)
  let obligations := registry.completedBy (published := published) revelations selected
  let checks := compileChecks (published := published) refs registry revelations selected
  let verdicts := obligations.map (·.accepts
    (revelations.reveal (published := published) selected)
    (Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload)
      proposal config.state))
  have perCheck (obligation : {obligation // obligation ∈ obligations}) :
      (compileGuard refs (revelations.reveal (published := published) selected)
        obligation.1 (registry.revealed_of_mem_completedBy revelations selected
          obligation.2)).eval? store proposal =
      some (obligation.1.accepts (revelations.reveal (published := published) selected)
        (Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload)
          proposal config.state)) := by
    apply compileGuard_eval?_of_present refs config.state store agree
    intro field read
    apply available field
    apply Finset.mem_insert_of_mem
    apply GuardCheck.readFields_subset_listReadFields checks _
      (List.mem_map.mpr ⟨obligation, List.mem_attach _ _, rfl⟩) read
  have exactChecks : checks.map (fun check => check.eval? store proposal) =
      verdicts.map some := by
    simp only [checks, compileChecks, List.map_map, Function.comp_def]
    rw [show (fun obligation : {obligation // obligation ∈ obligations} =>
      (compileGuard refs (revelations.reveal (published := published) selected)
        obligation.1 (registry.revealed_of_mem_completedBy revelations selected
          obligation.2)).eval? store proposal) =
        (fun obligation => some (obligation.1.accepts
          (revelations.reveal (published := published) selected)
          (Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload)
            proposal config.state))) from funext perCheck]
    simp [verdicts]
    rfl
  have checkLaw := GuardCheck.allAccepted?_eq_of_map_eval? checks store
    proposal verdicts exactChecks
  simp only [verdicts, List.all_map, Function.comp_def, id] at checkLaw
  have acceptedLaw : GuardCheck.allAccepted? checks store
      proposal = some true :=
    checkLaw.trans (congrArg some accepted)
  obtain ⟨value, bound⟩ := intended.bound selected
  refine ⟨value, ?_⟩
  change EventCode.resolveOutput? (refs.get selected) checks true store = _
  simp only [EventCode.resolveOutput?, boundRead, Option.bind_eq_bind, Option.bind_some, ↓reduceIte]
  rw [acceptedLaw]
  simp only [Option.bind_some, ↓reduceIte, proposal, bound]
  rfl

end Vegas
