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
field. A private cell contributes only its immutable binding result; its public
publication status is represented separately by publication cells. -/
def cellValue : {cell : CellTy Player L} →
    CellVal L cell → (cellField cell).Value
  | .publicData _, value => value
  | .privateData _ payload, value => BoundValue.resultEquiv (L.Val payload) value.1
  | .publication _, value => value

/-- Local typed agreement between a source context and its graph references. -/
def ContextRefs.Agrees {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout) : Prop :=
  ∀ {name cell} (source : HasVar Γ name cell),
    (refs.get source).get? store = some (cellValue (state.get source))

namespace ContextRefs

omit [DecidableEq Player] R in
/-- Updating one private cell's public status preserves context-reference
agreement because its graph binding field stores only the immutable bound
value. -/
theorem Agrees.updatePrivate {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (unique : (Γ.map Prod.fst).Nodup)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (agree : refs.Agrees state store)
    {owner : Player} {payload : L.Ty} {name : VarId}
    (selected : HasVar Γ name (.privateData owner payload))
    (status : Interaction.Publication (L.Val payload)) :
    refs.Agrees (updatePrivate state selected status) store := by
  intro readName readCell read
  by_cases same : readName = name
  · subst readName
    have cellEq := HasVar.type_unique unique read selected
    cases cellEq
    have readEq := HasVar.eq_of_nodup unique read selected
    subst read
    have stored := agree selected
    simpa [cellValue, updatePrivate_get_source] using stored
  · rw [updatePrivate_get_of_name_ne state selected status read same]
    exact agree read

end ContextRefs

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
      | privateData owner cellPayload =>
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

/-- Local agreement for the private-publication operands used while validating
one proposed resolution. -/
def OperandsAgree {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {currentPayload : L.Ty}
    (operands : ∀ {owner payload name},
      HasVar Γ name (.privateData owner payload) →
        Vegas.EventGraph.GuardOperand layout currentPayload payload)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (proposal : PublicationResult (L.Val currentPayload)) : Prop :=
  ∀ {owner payload name} (source : HasVar Γ name (.privateData owner payload)),
    (operands source).get? store proposal = some (state.get source).2

namespace PublicationRefs

/-- Structural agreement for retained private publication statuses. Literal
pending remains pending; a publication reference may store either success or
failure, both interpreted exactly through `publicationOfResult`. -/
def Agree {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (publications : PublicationRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout) : Prop :=
  ∀ {owner payload name} (source : HasVar Γ name (.privateData owner payload)),
    (match publications source with
      | .pending => some Interaction.Publication.pending
      | .publication ref =>
          (ref.get? store).map Vegas.EventGraph.publicationOfResult) =
        some (state.get source).2

omit [DecidableEq Player] R in
/-- A structurally agreed publication reference evaluates to the source
private cell's exact public status, including pending and failed statuses. -/
theorem operand_get_of_agrees {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (publications : PublicationRefs layout Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (agree : publications.Agree state store)
    {currentPayload : L.Ty}
    (proposal : PublicationResult (L.Val currentPayload))
    {owner payload name} (source : HasVar Γ name (.privateData owner payload)) :
    ((publications source).operand :
      Vegas.EventGraph.GuardOperand layout currentPayload payload).get? store proposal =
        some (state.get source).2 := by
  cases found : publications source with
  | pending =>
      have exactStatus := agree source
      simp only [found] at exactStatus
      simpa [PublicationRef.operand, Vegas.EventGraph.GuardOperand.get?] using exactStatus
  | publication ref =>
      have exactStatus := agree source
      simp only [found] at exactStatus
      simpa [PublicationRef.operand, Vegas.EventGraph.GuardOperand.get?] using exactStatus

end PublicationRefs

omit [DecidableEq Player] R in
private theorem initialPublications_eq_pending {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {owner : Player} {payload : L.Ty} {name : VarId}
    (source : HasVar Γ name (.privateData owner payload)) :
    initialPublications (Field := Field) (layout := layout) source = .pending := by
  induction Γ with
  | nil => nomatch source
  | cons entry tail ih =>
      obtain ⟨headName, headCell⟩ := entry
      cases headCell with
      | publicData headPayload =>
          cases source with
          | there source => exact ih source
      | privateData headOwner headPayload =>
          cases source with
          | here => rfl
          | there source => exact ih source
      | publication headPayload =>
          cases source with
          | there source => exact ih source

omit [DecidableEq Player] R in
/-- Initial publication references agree with any source state whose private
cells are still pending. -/
theorem initialPublications_agree {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (state : State L Γ)
    (store : Vegas.EventGraph.Store layout)
    (pending : ∀ {owner payload name}
      (source : HasVar Γ name (.privateData owner payload)),
        (state.get source).2 = .pending) :
    PublicationRefs.Agree
      (initialPublications (Field := Field) (layout := layout)) state store := by
  intro owner payload name source
  rw [show
    (initialPublications (Field := Field) (layout := layout) : PublicationRefs layout Γ)
        source = .pending from initialPublications_eq_pending source,
    pending source]

omit [DecidableEq Player] R in
/-- Specializing the selected private cell to the current proposal yields
operand agreement with the source tentative state. Other private statuses are
read through their retained structural publication references. -/
theorem proposedOperands_agree {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : PublicationRefs layout Γ)
    (unique : (Γ.map Prod.fst).Nodup)
    {owner : Player} {payload : L.Ty} {name : VarId}
    (selected : HasVar Γ name (.privateData owner payload))
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (refsAgree : refs.Agree state store)
    (proposal : PublicationResult (L.Val payload)) :
    OperandsAgree (proposedOperands refs unique selected)
      (updatePrivate state selected (resultPublication proposal)) store proposal := by
  intro readOwner readPayload readName source
  by_cases same : readName = name
  · subst readName
    have cellEq := HasVar.type_unique unique source selected
    have ownerEq := (CellTy.privateData.inj cellEq).1
    have payloadEq := (CellTy.privateData.inj cellEq).2
    subst readOwner
    subst readPayload
    have sourceEq := HasVar.eq_of_nodup unique source selected
    subst source
    simp [proposedOperands, Vegas.EventGraph.GuardOperand.get?,
      updatePrivate_get_source]
    cases proposal <;> rfl
  · have unchanged := congrArg Prod.snd
      (updatePrivate_get_of_name_ne state selected (resultPublication proposal)
        source same)
    rw [unchanged]
    simpa [proposedOperands, same] using
      PublicationRefs.operand_get_of_agrees refs state store refsAgree proposal source

omit [DecidableEq Player] R in
/-- Compiling one source guard read preserves its publication value under the
two local typed agreement relations. -/
theorem compileGuardRead_get_of_agrees {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {author : Player} {currentPayload input : L.Ty}
    (refs : ContextRefs layout Γ)
    (operands : ∀ {owner payload name},
      HasVar Γ name (.privateData owner payload) →
        Vegas.EventGraph.GuardOperand layout currentPayload payload)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (proposal : PublicationResult (L.Val currentPayload))
    (refsAgree : refs.Agrees state store)
    (operandsAgree : OperandsAgree operands state store proposal)
    (read : SourceGuardRead Γ author input) :
    (compileGuardRead refs operands read).get? store proposal =
      some (read.get state) := by
  cases read with
  | publicData source =>
      have stored := refsAgree source
      change (refs.get source).get? store = some (state.get source) at stored
      change ((refs.get source).get? store).map Interaction.Publication.value =
        some (Interaction.Publication.value (state.get source))
      rw [stored]
      rfl
  | privateData source => exact operandsAgree source
  | publication source =>
      have stored := refsAgree source
      change (refs.get source).get? store = some (state.get source) at stored
      change ((refs.get source).get? store).map
          Vegas.EventGraph.publicationOfResult =
        some (SourceGuardRead.get (.publication source) state)
      rw [stored]
      cases hresult : state.get source <;>
        simp [SourceGuardRead.get, Vegas.EventGraph.publicationOfResult, hresult]

omit [DecidableEq Player] R in
/-- One compiled deferred check evaluates to exactly its source obligation's
verdict under local context and operand agreement. -/
theorem compileGuard_eval? {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {currentPayload : L.Ty}
    (refs : ContextRefs layout Γ)
    (operands : ∀ {owner payload name},
      HasVar Γ name (.privateData owner payload) →
        Vegas.EventGraph.GuardOperand layout currentPayload payload)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (proposal : PublicationResult (L.Val currentPayload))
    (refsAgree : refs.Agrees state store)
    (operandsAgree : OperandsAgree operands state store proposal)
    (obligation : Obligation (Player := Player) (L := L) Γ) :
    (compileGuard refs operands obligation).eval? store proposal =
      some (obligation.check state) := by
  apply Vegas.EventGraph.DeferredCheck.eval?_eq_of_reads
  · exact operandsAgree obligation.source
  · intro name input source
    exact compileGuardRead_get_of_agrees refs operands state store proposal
      refsAgree operandsAgree (obligation.guard.reads source)

omit [DecidableEq Player] R in
/-- Every deferred check compiled from a source registry returns the matching
source obligation verdict. This is the local registry/admissibility boundary;
the resolution node's Boolean fold merely tests these verdicts for rejection. -/
theorem compileRegistry_eval? {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {currentPayload : L.Ty}
    (refs : ContextRefs layout Γ)
    (operands : ∀ {owner payload name},
      HasVar Γ name (.privateData owner payload) →
        Vegas.EventGraph.GuardOperand layout currentPayload payload)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (proposal : PublicationResult (L.Val currentPayload))
    (refsAgree : refs.Agrees state store)
    (operandsAgree : OperandsAgree operands state store proposal)
    (registry : Registry (Player := Player) (L := L) Γ) :
    (registry.map (compileGuard refs operands)).map
        (fun check => check.eval? store proposal) =
      registry.map (fun obligation => some (obligation.check state)) := by
  induction registry with
  | nil => rfl
  | cons obligation registry ih =>
      simp only [List.map_cons, ih, List.cons.injEq, and_true]
      exact compileGuard_eval? refs operands state store proposal refsAgree
        operandsAgree obligation

omit [DecidableEq Player] in
/-- The compiled resolution node exactly implements the source reveal's local
proposal, tentative registry check, and failure-on-rejection result. -/
theorem compileResolve_eval? {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ)
    (publications : PublicationRefs layout Γ)
    (unique : (Γ.map Prod.fst).Nodup)
    (registry : Registry (Player := Player) (L := L) Γ)
    (state : State L Γ) (store : Vegas.EventGraph.Store layout)
    (refsAgree : refs.Agrees state store)
    (publicationsAgree : publications.Agree state store)
    {owner : Player} {payload : L.Ty} {name : VarId}
    (selected : HasVar Γ name (.privateData owner payload))
    (disclose : Bool) :
    let proposedResult := boundResult state selected disclose
    let proposed := resultPublication proposedResult
    let tentative := updatePrivate state selected proposed
    let operands : ∀ {readOwner readPayload readName},
        HasVar Γ readName (.privateData readOwner readPayload) →
          Vegas.EventGraph.GuardOperand layout payload readPayload :=
      proposedOperands publications unique selected
    let checks := registry.map (compileGuard refs operands)
    (Vegas.EventGraph.EventCode.resolve owner payload (refs.get selected) checks).eval?
        disclose store =
      some (FinDist.pure
        (if registry.ok tentative then proposedResult else .failure)) := by
  dsimp only
  let proposedResult := boundResult state selected disclose
  let proposed := resultPublication proposedResult
  let tentative := updatePrivate state selected proposed
  let operands : ∀ {readOwner readPayload readName},
      HasVar Γ readName (.privateData readOwner readPayload) →
        Vegas.EventGraph.GuardOperand layout payload readPayload :=
    proposedOperands publications unique selected
  let checks := registry.map (compileGuard refs operands)
  have bindingStored := refsAgree selected
  change (refs.get selected).get? store =
    some (BoundValue.resultEquiv _ (state.get selected).1) at bindingStored
  have proposalEq :
      (if disclose then BoundValue.resultEquiv _ (state.get selected).1 else .failure) =
        proposedResult := by
    exact (boundResult_eq_resultEquiv state selected disclose).symm
  have tentativeRefs : refs.Agrees tentative store :=
    refsAgree.updatePrivate refs unique state store selected proposed
  have operandsAgree : OperandsAgree operands tentative store proposedResult := by
    exact proposedOperands_agree publications unique selected state store
      publicationsAgree proposedResult
  have checksExact :
      checks.map (fun check => check.eval? store proposedResult) =
        registry.map (fun obligation => some (obligation.check tentative)) := by
    exact compileRegistry_eval? refs operands tentative store proposedResult
      tentativeRefs operandsAgree registry
  have acceptedExact :
      Vegas.EventGraph.DeferredCheck.allAccepted? checks store proposedResult =
        some (registry.ok tentative) := by
    have checksExact' :
        checks.map (fun check => check.eval? store proposedResult) =
          (registry.map fun obligation => obligation.check tentative).map some := by
      simpa only [List.map_map, Function.comp_def] using checksExact
    rw [Vegas.EventGraph.DeferredCheck.allAccepted?_eq_of_map_eval?
      checks store proposedResult (registry.map fun obligation => obligation.check tentative)
      checksExact']
    simp only [List.all_map, Function.comp_def, Registry.ok]
  suffices h :
      (Vegas.EventGraph.DeferredCheck.allAccepted? checks store proposedResult).bind
          (fun accepted => some (FinDist.pure
            (if accepted then proposedResult else .failure))) =
        some (FinDist.pure
          (if registry.ok tentative then proposedResult else .failure)) by
    simpa [Vegas.EventGraph.EventCode.eval?, bindingStored, proposalEq] using h
  rw [acceptedExact]
  rfl

end Vegas.SourceProgram.EventLowering
