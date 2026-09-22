/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphCompiler
import Vegas.Source.Semantics

/-! # Local evaluation correctness for event-graph lowering

Compiled public expressions and exact distribution tables are evaluated from
typed graph fields. Their correctness depends only on agreement between those
fields and one source state; it does not assume an execution or whole-run law.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Encode one source cell as the value stored in its corresponding event-graph
field. A private cell stores its immutable binding. -/
def cellValue : {cell : CellTy Player L} →
    CellVal L cell → (cellField cell).Value
  | .publicData _, value => value
  | .commitment _ _, value => value
  | .privateInput _ _, value => value
  | .publication _, value => value

/-- Local typed agreement between a source context and its graph references. -/
def ContextRefs.Agrees {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout) : Prop :=
  ∀ {name cell} (source : HasVar Γ name cell),
    (refs.get source).get? store = some (cellValue (state.get source))

omit [DecidableEq Player] in
/-- A compiled public reference reads exactly the corresponding source public
environment value under local typed context agreement. -/
theorem publicRead_get_of_agrees {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (agree : refs.Agrees state store)
    {name payload} (source : HasVar (SourcePublicCtx L Γ) name payload) :
    (publicRead refs source).get? store =
      some ((sourcePublicEnv state).get source) := by
  induction Γ with
  | nil => exact nomatch source
  | cons entry tail ih =>
      obtain ⟨headName, cell⟩ := entry
      cases cell with
      | publicData cellPayload =>
          cases source with
          | here =>
              have stored := agree HasVar.here
              change (refs.get HasVar.here).get? store =
                some (state.get HasVar.here) at stored
              change (refs.get HasVar.here).get? store =
                some (state.get HasVar.here)
              exact stored
          | there source =>
              apply ih
                (ContextRefs.mk fun ref => refs.get (.there ref))
                (fun _ _ ref => state.get (.there ref))
              intro refName refCell ref
              exact agree (.there ref)
      | commitment owner cellPayload | privateInput owner cellPayload =>
          apply ih
            (ContextRefs.mk fun ref => refs.get (.there ref))
            (fun _ _ ref => state.get (.there ref))
          intro refName refCell ref
          exact agree (.there ref)
      | publication cellPayload =>
          cases source with
          | here =>
              have stored := agree HasVar.here
              change (refs.get HasVar.here).get? store =
                some (state.get HasVar.here) at stored
              change ((refs.get HasVar.here).get? store).map
                  (R.valueEquiv cellPayload).symm =
                some ((R.valueEquiv cellPayload).symm (state.get HasVar.here))
              rw [stored]
              rfl
          | there source =>
              apply ih
                (ContextRefs.mk fun ref => refs.get (.there ref))
                (fun _ _ ref => state.get (.there ref))
              intro refName refCell ref
              exact agree (.there ref)

omit [DecidableEq Player] in
/-- Compiled public expression evaluation equals source denotation under local
typed context-reference agreement. -/
theorem compilePublicExpr_eval? {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (agree : refs.Agrees state store) {payload : L.Ty}
    (expression : L.Expr (SourcePublicCtx L Γ) payload) :
    (compilePublicExpr refs expression).eval? store =
      some (L.eval expression (sourcePublicEnv state)) := by
  apply Vegas.EventGraph.PublicExpr.eval?_eq_of_reads
  intro name input source _
  exact publicRead_get_of_agrees refs state store agree source

omit [DecidableEq Player] in
/-- Compiled public distribution evaluation retains exactly the source's
normalized rational table under local typed context-reference agreement. -/
theorem compilePublicDist_evalLaw? {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (agree : refs.Agrees state store) {payload : L.Ty}
    (law : L.DistExpr (SourcePublicCtx L Γ) payload) :
    (compilePublicDist refs law).evalLaw? store =
      some (L.evalLaw law (sourcePublicEnv state)) := by
  apply Vegas.EventGraph.PublicDist.evalLaw?_eq_of_reads
  intro name input source _
  exact publicRead_get_of_agrees refs state store agree source

omit [DecidableEq Player] R in
/-- A reveal operand reads the tentative state: the proposal at the head, and
every earlier publication from its field. -/
theorem revealOperand_get {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (agree : refs.Agrees state store) {published : VarId} {payload : L.Ty}
    (proposal : PublicationResult (L.Val payload)) {name : VarId} {τ : L.Ty}
    (cell : HasVar ((published, .publication payload) :: Γ) name (.publication τ)) :
    (revealOperand refs cell).get? store proposal =
      some ((Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload)
        proposal state).get cell) := by
  cases cell with
  | here => rfl
  | there cell => exact agree cell

omit [DecidableEq Player] R in
/-- A compiled published guard input reads exactly its source result in the
tentative state. -/
theorem compileGuardRead_get {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (agree : refs.Agrees state store) {published : VarId} {payload : L.Ty}
    (proposal : PublicationResult (L.Val payload))
    (revealed : Revelations ((published, .publication payload) :: Γ))
    {author : Player} {τ : L.Ty}
    (read : SourceGuardRead ((published, .publication payload) :: Γ) author τ)
    (isRevealed : read.revealed revealed = true) :
    (compileGuardRead refs revealed read isRevealed).get? store proposal =
      some (read.result revealed
        (Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload)
          proposal state)) := by
  cases read with
  | publicData cell =>
      cases cell with
      | there cell =>
          have stored := agree cell
          change (refs.get cell).get? store = some (state.get cell) at stored
          change ((refs.get cell).get? store).map PublicationResult.success =
            some (PublicationResult.success (state.get cell))
          rw [stored]
          rfl
  | publication cell => exact revealOperand_get refs state store agree proposal cell
  | commitment cell =>
      simp only [compileGuardRead]
      split
      · next publication revelation =>
          simp only [SourceGuardRead.result, revelation, Revelation.result]
          exact revealOperand_get refs state store agree proposal publication
      · next revelation =>
          simp [SourceGuardRead.revealed, revelation, Revelation.isRevealed] at isRevealed

omit [DecidableEq Player] R in
/-- A compiled check decides exactly as its completed source obligation does in
the tentative state. -/
theorem compileGuard_eval? {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (agree : refs.Agrees state store) {published : VarId} {payload : L.Ty}
    (proposal : PublicationResult (L.Val payload))
    (revealed : Revelations ((published, .publication payload) :: Γ))
    (obligation : Obligation (Player := Player) (L := L) ((published, .publication payload) :: Γ))
    (isRevealed : obligation.revealed revealed = true) :
    (compileGuard refs revealed obligation isRevealed).eval? store proposal =
      some (obligation.accepts revealed
        (Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload)
          proposal state)) := by
  apply Vegas.EventGraph.GuardCheck.eval?_eq_of_reads
  · exact compileGuardRead_get refs state store agree proposal revealed
      (.commitment obligation.source) _
  · intro name input source read
    exact compileGuardRead_get refs state store agree proposal revealed
      (obligation.guard.reads source) _

omit [DecidableEq Player] in
/-- The compiled resolution node exactly implements the source reveal: its
proposal, the checks of the obligations it completes, and failure on rejection. -/
theorem compileResolve_eval? {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (registry : Registry (Player := Player) (L := L) Γ) (revelations : Revelations Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (agree : refs.Agrees state store)
    {published : VarId} {owner : Player} {payload : L.Ty} {name : VarId}
    (selected : HasVar Γ name (.commitment owner payload)) (disclose : Bool) :
    (Vegas.EventGraph.EventCode.resolve owner payload (refs.get selected)
        (compileChecks (published := published) refs registry revelations selected)).eval?
        disclose store =
      some (FinDist.pure
        (if (registry.completedBy (published := published) revelations selected).all
            (·.accepts (revelations.reveal (published := published) selected)
              (Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload)
                (if disclose then (state.get selected : PublicationResult (L.Val payload))
                  else .failure) state))
          then (if disclose then (state.get selected : PublicationResult (L.Val payload))
            else .failure) else .failure)) := by
  have bindingStored : (refs.get selected).get? store = some (state.get selected) :=
    agree selected
  have acceptedExact : ∀ proposal : PublicationResult (L.Val payload),
      Vegas.EventGraph.GuardCheck.allAccepted?
          (compileChecks (published := published) refs registry revelations selected)
          store proposal =
        some ((registry.completedBy (published := published) revelations selected).all
          (·.accepts (revelations.reveal (published := published) selected)
            (Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload)
              proposal state))) := by
    intro proposal
    rw [Vegas.EventGraph.GuardCheck.allAccepted?_eq_of_map_eval? _ store proposal
      ((registry.completedBy (published := published) revelations selected).map
        (·.accepts (revelations.reveal (published := published) selected)
          (Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload)
            proposal state)))]
    · simp only [List.all_map, Function.comp_def, id]
    · simp only [compileChecks, List.map_map, Function.comp_def]
      rw [show (fun obligation : {obligation //
            obligation ∈ registry.completedBy (published := published) revelations selected} =>
          (compileGuard refs (revelations.reveal (published := published) selected)
            obligation.1 (registry.revealed_of_mem_completedBy revelations selected
              obligation.2)).eval? store proposal) =
          fun obligation => some (obligation.1.accepts
            (revelations.reveal (published := published) selected)
            (Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload)
              proposal state)) from
        funext fun obligation => compileGuard_eval? refs state store agree proposal _ _ _]
      simp
  simp only [Vegas.EventGraph.EventCode.resolve_eval?,
    Vegas.EventGraph.EventCode.resolveOutput?, bindingStored, Option.bind_eq_bind,
    Option.bind_some, acceptedExact]
  rfl

end Vegas.SourceProgram.EventLowering
