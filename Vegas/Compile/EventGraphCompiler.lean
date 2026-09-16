/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphLayout
import Vegas.EventGraph.Barriers

/-! # Full source-node lowering to dependency-driven event code

The functions here lower every source constructor.  They are parameterized by
typed references into one final graph layout; the graph assembly theorem then
supplies source-ranked references and the barrier dependency proof.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

open Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

private def publicReadFields {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    (deps : Finset VarId) :
    (schema : Ctx L.Ty) →
      (∀ {name payload}, HasVar schema name payload →
        Vegas.EventGraph.PublicRead (R := R) layout payload) → Finset Field
  | [], _ => ∅
  | (name, payload) :: tail, reads =>
      let rest := publicReadFields deps tail (fun source => reads (.there source))
      if name ∈ deps then
        insert (reads (HasVar.here : HasVar ((name, payload) :: tail) name payload)).field rest
      else rest

omit [DecidableEq Player] in
private theorem publicReadFields_mem {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {name payload}, HasVar schema name payload →
      Vegas.EventGraph.PublicRead (R := R) layout payload)
    {name payload} (source : HasVar schema name payload) (used : name ∈ deps) :
    (reads source).field ∈ publicReadFields deps schema reads := by
  induction source with
  | @here tail name payload => simp [publicReadFields, used]
  | @there tail name headName payload headPayload source ih =>
      simp only [publicReadFields]
      split
      · exact Finset.mem_insert_of_mem
          (ih (fun source => reads (.there source)) used)
      · exact ih (fun source => reads (.there source)) used

/-- Translate a public source schema reference through a typed prefix
environment. -/
def publicRead {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L} :
    {Γ : SourceCtx Player L} → ContextRefs layout Γ →
      ∀ {name payload}, HasVar (SourcePublicCtx L Γ) name payload →
        Vegas.EventGraph.PublicRead (R := R) layout payload
  | (_, .publicData _) :: _, refs, _, _, .here => .publicData (refs.get .here)
  | (_, .publicData _) :: tail, refs, _, _, .there source =>
      publicRead (ContextRefs.mk fun source => refs.get (.there source)) source
  | (_, .privateData _ _) :: _tail, refs, _, _, source =>
      publicRead (ContextRefs.mk fun source => refs.get (.there source)) source
  | (_, .publication _) :: _, refs, _, _, .here => .publication (refs.get .here)
  | (_, .publication _) :: tail, refs, _, _, .there source =>
      publicRead (ContextRefs.mk fun source => refs.get (.there source)) source

/-- Lower an ordinary source expression with its exact finite field
footprint. -/
def compilePublicExpr {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ) {payload : L.Ty}
    (expression : L.Expr (SourcePublicCtx L Γ) payload) :
    Vegas.EventGraph.PublicExpr layout payload where
  schema := SourcePublicCtx L Γ
  code := expression
  reads := publicRead refs
  readFields := publicReadFields (L.exprDeps expression) _ (publicRead refs)
  reads_mem source used := publicReadFields_mem _ _ _ source used

/-- Lower an exact source distribution with its exact finite field
footprint. -/
def compilePublicDist {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (refs : ContextRefs layout Γ) {payload : L.Ty}
    (law : L.DistExpr (SourcePublicCtx L Γ) payload) :
    Vegas.EventGraph.PublicDist layout payload where
  schema := SourcePublicCtx L Γ
  code := law
  reads := publicRead refs
  readFields := publicReadFields (L.distDeps law) _ (publicRead refs)
  reads_mem source used := publicReadFields_mem _ _ _ source used

namespace PublicationRef

/-- Concrete field named by a retained status, when already published. -/
def field? {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L} {payload : L.Ty} :
    PublicationRef layout payload → Option Field
  | .pending => none
  | .publication ref => some ref.field

omit [DecidableEq Player] R in
@[simp] theorem field?_cast {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L} {left right : L.Ty}
    (same : left = right) (publication : PublicationRef layout left) :
    (cast (congrArg (PublicationRef layout) same) publication).field? =
      publication.field? := by
  cases same
  rfl

/-- Use a retained private publication status as a deferred-check operand. -/
def operand {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {currentPayload payload : L.Ty} :
    PublicationRef layout payload →
      Vegas.EventGraph.GuardOperand layout currentPayload payload
  | .pending => .pending
  | .publication ref => .publication ref

end PublicationRef

/-- At a resolution, replace exactly the selected private source by the atomic
proposal operand. Other unresolved cells remain literal pending and earlier
resolutions remain typed publication references. -/
def proposedOperands {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (publications : PublicationRefs layout Γ)
    (unique : (Γ.map Prod.fst).Nodup)
    {owner : Player} {payload : L.Ty} {name : VarId}
    (selected : HasVar Γ name (.privateData owner payload)) :
    ∀ {readOwner readPayload readName},
      HasVar Γ readName (.privateData readOwner readPayload) →
        Vegas.EventGraph.GuardOperand layout payload readPayload :=
  fun {_readOwner _readPayload readName} source =>
    if same : readName = name then
      let cellEq := HasVar.type_unique unique (same ▸ source) selected
      let payloadEq := (CellTy.privateData.inj cellEq).2
      payloadEq.symm ▸ Vegas.EventGraph.GuardOperand.proposed
    else (publications source).operand

/-- Specialize one source guard read for the current atomic resolution. -/
def compileGuardRead {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {author : Player} {currentPayload input : L.Ty}
    (refs : ContextRefs layout Γ)
    (operands : ∀ {owner payload name},
      HasVar Γ name (.privateData owner payload) →
        Vegas.EventGraph.GuardOperand layout currentPayload payload) :
    SourceGuardRead Γ author input →
      Vegas.EventGraph.GuardOperand layout currentPayload input
  | .publicData source => .publicData (refs.get source)
  | .privateData source => operands source
  | .publication source => .publication (refs.get source)

private def operandField {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {currentPayload payload : L.Ty}
    (operand : Vegas.EventGraph.GuardOperand layout currentPayload payload) : Finset Field :=
  match operand.field? with
  | none => ∅
  | some field => {field}

private def guardReadFields {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {currentPayload : L.Ty} :
    (schema : Ctx L.Ty) →
      (∀ {name payload}, HasVar schema name payload →
        Vegas.EventGraph.GuardOperand layout currentPayload payload) → Finset Field
  | [], _ => ∅
  | (_, _) :: tail, reads => operandField (reads .here) ∪
      guardReadFields tail (fun source => reads (.there source))

omit [DecidableEq Player] R in
private theorem operandField_mem {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {currentPayload payload : L.Ty}
    (operand : Vegas.EventGraph.GuardOperand layout currentPayload payload)
    (field : Field) (found : operand.field? = some field) :
    field ∈ operandField operand := by
  simp [operandField, found]

omit [DecidableEq Player] R in
private theorem mem_operandField_iff {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {currentPayload payload : L.Ty}
    (operand : Vegas.EventGraph.GuardOperand layout currentPayload payload)
    (field : Field) :
    field ∈ operandField operand ↔ operand.field? = some field := by
  cases found : operand.field? with
  | none => simp [operandField, found]
  | some result => simp [operandField, found, eq_comm]

omit [DecidableEq Player] R in
private theorem guardReadFields_mem {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {currentPayload : L.Ty} (schema : Ctx L.Ty)
    (reads : ∀ {name payload}, HasVar schema name payload →
      Vegas.EventGraph.GuardOperand layout currentPayload payload)
    {name payload} (source : HasVar schema name payload) (field : Field)
    (found : (reads source).field? = some field) :
    field ∈ guardReadFields schema reads := by
  induction source with
  | here => exact Finset.mem_union_left _ (operandField_mem _ _ found)
  | there source ih =>
      apply Finset.mem_union_right
      exact ih (fun source => reads (.there source)) found

/-- Lower one retained source obligation to an executable deferred check. -/
def compileGuard {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {currentPayload : L.Ty}
    (refs : ContextRefs layout Γ)
    (operands : ∀ {owner payload name},
      HasVar Γ name (.privateData owner payload) →
        Vegas.EventGraph.GuardOperand layout currentPayload payload)
    (obligation : Obligation (Player := Player) (L := L) Γ) :
    Vegas.EventGraph.DeferredCheck layout currentPayload :=
  let subjectRead := operands obligation.source
  let reads : ∀ {name payload}, HasVar obligation.guard.schema name payload →
      Vegas.EventGraph.GuardOperand layout currentPayload payload :=
    fun source => compileGuardRead refs operands (obligation.guard.reads source)
  { subject := obligation.subject
    payload := obligation.payload
    code := obligation.guard.toDeferredGuardCode
    subjectRead := subjectRead
    reads := reads
    readFields := operandField subjectRead ∪ guardReadFields _ reads
    subject_mem := fun field found =>
      Finset.mem_union_left _ (operandField_mem subjectRead field found)
    reads_mem := fun source field found =>
      Finset.mem_union_right _ (guardReadFields_mem _ reads source field found) }

/-- Install the selected resolution's new public field while retaining every
other private cell's previous status. -/
def resolvePublications {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (publications : PublicationRefs layout Γ)
    (unique : (Γ.map Prod.fst).Nodup)
    {owner : Player} {payload : L.Ty} {name published : VarId}
    (selected : HasVar Γ name (.privateData owner payload))
    (result : Vegas.EventGraph.FieldRef layout (.publication payload)) :
    PublicationRefs layout ((published, .publication payload) :: Γ) :=
  fun {_readOwner _readPayload readName} source => match source with
    | .there source =>
      if same : readName = name then
        let cellEq := HasVar.type_unique unique (same ▸ source) selected
        let payloadEq := (CellTy.privateData.inj cellEq).2
        cast (congrArg (PublicationRef layout) payloadEq.symm)
          (PublicationRef.publication result)
      else publications source

/-! ## Structural read-rank certificate -/

/-- A combined-layout field is available before `event` when it is an input,
or when its producing event has smaller source rank. -/
def FieldBefore {inputCount eventCount : Nat} (event : Fin eventCount) :
    Vegas.EventGraph.FieldId inputCount eventCount → Prop
  | .inl _ => True
  | .inr producer => producer.val < event.val

omit [DecidableEq Player] in
private theorem publicReadFields_before {inputCount eventCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin eventCount → Vegas.EventGraph.EventField Player L}
    (target : Fin eventCount) (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {name payload}, HasVar schema name payload →
      Vegas.EventGraph.PublicRead (R := R)
        (Vegas.EventGraph.fieldLayout inputs outputs) payload)
    (before : ∀ {name payload} (source : HasVar schema name payload),
      FieldBefore target (reads source).field) :
    ∀ field, field ∈ publicReadFields deps schema reads → FieldBefore target field := by
  induction schema with
  | nil => simp [publicReadFields]
  | cons entry tail ih =>
      obtain ⟨name, payload⟩ := entry
      intro field member
      by_cases used : name ∈ deps
      · simp only [publicReadFields, if_pos used, Finset.mem_insert] at member
        rcases member with same | member
        · subst field
          exact before .here
        · exact ih (fun source => reads (.there source))
            (fun source => before (.there source)) field member
      · simp only [publicReadFields, if_neg used] at member
        exact ih (fun source => reads (.there source))
          (fun source => before (.there source)) field member

omit [DecidableEq Player] in
private theorem publicRead_before {inputCount eventCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin eventCount → Vegas.EventGraph.EventField Player L}
    {target : Fin eventCount} : {Γ : SourceCtx Player L} →
    (refs : ContextRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ) →
    (∀ {name cell} (source : HasVar Γ name cell),
      FieldBefore target (refs.get source).field) →
    ∀ {name payload} (source : HasVar (SourcePublicCtx L Γ) name payload),
      FieldBefore target (publicRead refs source).field
  | (_, .publicData _) :: _, _refs, before, _, _, .here => before .here
  | (_, .publicData _) :: tail, refs, before, _, _, .there source =>
      publicRead_before (ContextRefs.mk fun source => refs.get (.there source))
        (fun source => before (.there source)) source
  | (_, .privateData _ _) :: _tail, refs, before, _, _, source =>
      publicRead_before (ContextRefs.mk fun source => refs.get (.there source))
        (fun source => before (.there source)) source
  | (_, .publication _) :: _, _refs, before, _, _, .here => before .here
  | (_, .publication _) :: tail, refs, before, _, _, .there source =>
      publicRead_before (ContextRefs.mk fun source => refs.get (.there source))
        (fun source => before (.there source)) source

omit [DecidableEq Player] in
/-- Exact public-distribution footprints mention only fields preceding the
target source-ranked event. -/
theorem compilePublicDist_before {inputCount eventCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin eventCount → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} (target : Fin eventCount)
    (refs : ContextRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ)
    (before : ∀ {name cell} (source : HasVar Γ name cell),
      FieldBefore target (refs.get source).field)
    {payload : L.Ty} (law : L.DistExpr (SourcePublicCtx L Γ) payload) :
    ∀ field, field ∈ (compilePublicDist refs law).readFields →
      FieldBefore target field := by
  intro field member
  exact publicReadFields_before target _ _ _
    (fun source => publicRead_before refs before source) field member

/-- Every concrete field named by an operand precedes the target event. -/
def OperandBefore {inputCount eventCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin eventCount → Vegas.EventGraph.EventField Player L}
    {currentPayload payload : L.Ty} (target : Fin eventCount)
    (operand : Vegas.EventGraph.GuardOperand
      (Vegas.EventGraph.fieldLayout inputs outputs) currentPayload payload) : Prop :=
  ∀ field, operand.field? = some field → FieldBefore target field

/-- Every retained publication reference precedes the target event. -/
def PublicationsBefore {inputCount eventCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin eventCount → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L}
    (publications : PublicationRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ)
    (target : Fin eventCount) : Prop :=
  ∀ {owner payload name} (source : HasVar Γ name (.privateData owner payload)),
    ∀ field, (publications source).field? = some field → FieldBefore target field

omit [DecidableEq Player] R in
private theorem PublicationRef.operand_before {inputCount eventCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin eventCount → Vegas.EventGraph.EventField Player L}
    {target : Fin eventCount} {currentPayload payload : L.Ty}
    (publication : PublicationRef
      (Vegas.EventGraph.fieldLayout inputs outputs) payload)
    (before : ∀ field, publication.field? = some field → FieldBefore target field) :
    OperandBefore target (publication.operand (currentPayload := currentPayload)) := by
  intro field found
  apply before field
  cases publication <;> exact found

omit [DecidableEq Player] R in
private theorem proposedOperands_before {inputCount eventCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin eventCount → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L}
    (publications : PublicationRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ)
    (unique : (Γ.map Prod.fst).Nodup)
    {owner : Player} {payload : L.Ty} {name : VarId}
    (selected : HasVar Γ name (.privateData owner payload))
    (target : Fin eventCount) (before : PublicationsBefore publications target) :
    ∀ {readOwner readPayload readName}
      (source : HasVar Γ readName (.privateData readOwner readPayload)),
      OperandBefore target (proposedOperands publications unique selected source) := by
  intro readOwner readPayload readName source
  by_cases same : readName = name
  · subst readName
    have cellEq := HasVar.type_unique unique source selected
    cases cellEq
    simp [proposedOperands, OperandBefore, Vegas.EventGraph.GuardOperand.field?]
  · simp only [proposedOperands, dif_neg same]
    exact (publications source).operand_before (before source)

omit [DecidableEq Player] R in
private theorem compileGuardRead_before {inputCount eventCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin eventCount → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {author : Player} {currentPayload input : L.Ty}
    (target : Fin eventCount)
    (refs : ContextRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ)
    (refsBefore : ∀ {name cell} (source : HasVar Γ name cell),
      FieldBefore target (refs.get source).field)
    (operands : ∀ {owner payload name},
      HasVar Γ name (.privateData owner payload) →
        Vegas.EventGraph.GuardOperand
          (Vegas.EventGraph.fieldLayout inputs outputs) currentPayload payload)
    (operandsBefore : ∀ {owner payload name}
      (source : HasVar Γ name (.privateData owner payload)),
      OperandBefore target (operands source))
    (read : SourceGuardRead Γ author input) :
    OperandBefore target (compileGuardRead refs operands read) := by
  cases read with
  | publicData source | publication source =>
      intro field found
      simp only [compileGuardRead, Vegas.EventGraph.GuardOperand.field?,
        Option.some.injEq] at found
      subst field
      exact refsBefore source
  | privateData source => exact operandsBefore source

omit [DecidableEq Player] R in
private theorem guardReadFields_before {inputCount eventCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin eventCount → Vegas.EventGraph.EventField Player L}
    {target : Fin eventCount} {currentPayload : L.Ty}
    (schema : Ctx L.Ty)
    (reads : ∀ {name payload}, HasVar schema name payload →
      Vegas.EventGraph.GuardOperand
        (Vegas.EventGraph.fieldLayout inputs outputs) currentPayload payload)
    (before : ∀ {name payload} (source : HasVar schema name payload),
      OperandBefore target (reads source)) :
    ∀ field, field ∈ guardReadFields schema reads → FieldBefore target field := by
  induction schema with
  | nil => simp [guardReadFields]
  | cons entry tail ih =>
      intro field member
      rw [guardReadFields, Finset.mem_union] at member
      rcases member with head | rest
      · exact before (HasVar.here : HasVar (entry :: tail) entry.1 entry.2)
          field ((mem_operandField_iff _ _).mp head)
      · exact ih (fun source => reads (.there source))
          (fun source => before (.there source)) field rest

omit [DecidableEq Player] R in
private theorem compileGuard_before {inputCount eventCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin eventCount → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {currentPayload : L.Ty}
    (target : Fin eventCount)
    (refs : ContextRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ)
    (refsBefore : ∀ {name cell} (source : HasVar Γ name cell),
      FieldBefore target (refs.get source).field)
    (operands : ∀ {owner payload name},
      HasVar Γ name (.privateData owner payload) →
        Vegas.EventGraph.GuardOperand
          (Vegas.EventGraph.fieldLayout inputs outputs) currentPayload payload)
    (operandsBefore : ∀ {owner payload name}
      (source : HasVar Γ name (.privateData owner payload)),
      OperandBefore target (operands source))
    (obligation : Obligation (Player := Player) (L := L) Γ) :
    ∀ field, field ∈ (compileGuard refs operands obligation).readFields →
      FieldBefore target field := by
  intro field member
  rw [compileGuard, Finset.mem_union] at member
  rcases member with subject | reads
  · exact operandsBefore obligation.source field
      ((mem_operandField_iff _ _).mp subject)
  · exact guardReadFields_before _ _ (fun source =>
      compileGuardRead_before target refs refsBefore operands operandsBefore
        (obligation.guard.reads source)) field reads

omit [DecidableEq Player] R in
private theorem compileGuards_before {inputCount eventCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin eventCount → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {currentPayload : L.Ty}
    (target : Fin eventCount)
    (refs : ContextRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ)
    (refsBefore : ∀ {name cell} (source : HasVar Γ name cell),
      FieldBefore target (refs.get source).field)
    (operands : ∀ {owner payload name},
      HasVar Γ name (.privateData owner payload) →
        Vegas.EventGraph.GuardOperand
          (Vegas.EventGraph.fieldLayout inputs outputs) currentPayload payload)
    (operandsBefore : ∀ {owner payload name}
      (source : HasVar Γ name (.privateData owner payload)),
      OperandBefore target (operands source)) :
    (registry : Registry Γ) → ∀ field,
      field ∈ Vegas.EventGraph.DeferredCheck.listReadFields
        (registry.map (compileGuard refs operands)) → FieldBefore target field
  | [], field, member => by simp [Vegas.EventGraph.DeferredCheck.listReadFields] at member
  | obligation :: registry, field, member => by
      rw [List.map_cons, Vegas.EventGraph.DeferredCheck.listReadFields,
        Finset.mem_union] at member
      rcases member with head | tail
      · exact compileGuard_before target refs refsBefore operands operandsBefore
          obligation field head
      · exact compileGuards_before target refs refsBefore operands operandsBefore
          registry field tail

/-- A source suffix's outputs embedded, in order, into one whole graph. -/
structure OutputEmbedding {inputCount totalCount : Nat}
    (inputs : Fin inputCount → Vegas.EventGraph.EventField Player L)
    (outputs : Fin totalCount → Vegas.EventGraph.EventField Player L)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) where
  event : Fin (eventCount program) → Fin totalCount
  layout_eq : ∀ index, outputs (event index) = outputLayout program index
  strictMono : StrictMono event

namespace OutputEmbedding

/-- Turn an embedded source output into a typed combined-layout reference. -/
def ref {inputCount totalCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin totalCount → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {program : SourceProgram Player L Γ openNames}
    (embedding : OutputEmbedding inputs outputs program)
    (index : Fin (eventCount program)) :
    Vegas.EventGraph.FieldRef (Vegas.EventGraph.fieldLayout inputs outputs)
      (outputLayout program index) where
  field := .inr (embedding.event index)
  layout_eq := embedding.layout_eq index

/-- Restrict an embedding to the tail after its first source operation. -/
def tail {inputCount totalCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin totalCount → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {program : SourceProgram Player L Γ openNames}
    (embedding : OutputEmbedding inputs outputs program)
    {name : VarId} {cell : CellTy Player L} {nextOpen : Finset VarId}
    (next : SourceProgram Player L ((name, cell) :: Γ) nextOpen)
    (countEq : eventCount program = (eventCount next).succ)
    (layoutTail : ∀ index, outputLayout program
      (Fin.cast countEq.symm (Fin.succ index)) = outputLayout next index) :
    OutputEmbedding inputs outputs next where
  event index := embedding.event
    (Fin.cast countEq.symm (Fin.succ index))
  layout_eq index := (embedding.layout_eq _).trans (layoutTail index)
  strictMono := by
    intro left right earlier
    apply embedding.strictMono
    simpa using earlier

end OutputEmbedding

/-- Every source cell already in scope denotes either an input or an output
whose rank is smaller than every remaining embedded event. -/
def ContextRefsBefore {inputCount totalCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin totalCount → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {program : SourceProgram Player L Γ openNames}
    (refs : ContextRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ)
    (embedding : OutputEmbedding inputs outputs program) : Prop :=
  ∀ {name cell} (source : HasVar Γ name cell) index,
    FieldBefore (embedding.event index) (refs.get source).field

/-- The same prefix-rank invariant for retained private publication refs. -/
def PublicationsBeforeAll {inputCount totalCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin totalCount → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {program : SourceProgram Player L Γ openNames}
    (publications : PublicationRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ)
    (embedding : OutputEmbedding inputs outputs program) : Prop :=
  ∀ index, PublicationsBefore publications (embedding.event index)

/-- Executable node code paired with its locally constructed causal read
certificate. The certificate is derived during lowering, not assumed of the
finished graph. -/
structure RankedNode {inputCount totalCount : Nat}
    (inputs : Fin inputCount → Vegas.EventGraph.EventField Player L)
    (outputs : Fin totalCount → Vegas.EventGraph.EventField Player L)
    (event : Fin totalCount) (output : Vegas.EventGraph.EventField Player L) where
  code : Vegas.EventGraph.EventCode (Vegas.EventGraph.fieldLayout inputs outputs) output
  reads_before : ∀ field, field ∈ code.readFields → FieldBefore event field

/-- Full-language lowering that constructs node code and the source-rank
certificate in the same recursion. -/
def compileRankedNodes {inputCount totalCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin totalCount → Vegas.EventGraph.EventField Player L} :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) →
    (unique : (Γ.map Prod.fst).Nodup) →
    (refs : ContextRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ) →
    (publications : PublicationRefs
      (Vegas.EventGraph.fieldLayout inputs outputs) Γ) →
    (registry : Registry Γ) →
    (embedding : OutputEmbedding inputs outputs program) →
    ContextRefsBefore refs embedding → PublicationsBeforeAll publications embedding →
    ∀ index, RankedNode inputs outputs (embedding.event index) (outputLayout program index)
  | _, _, .ret _, _, _, _, _, _, _, _, index => nomatch index
  | _, _, .sample name fresh law next, unique, refs, publications, registry,
      embedding, refsBefore, publicationsBefore, index =>
      let headIndex : Fin (eventCount (.sample name fresh law next)) :=
        ⟨0, by simp [eventCount]⟩
      let head : RankedNode inputs outputs (embedding.event headIndex) (.publicData _) :=
        { code := .sample _ (compilePublicDist refs law)
          reads_before := compilePublicDist_before (embedding.event headIndex) refs
            (fun source => refsBefore source headIndex) law }
      let tailEmbedding := embedding.tail next rfl (fun _ => rfl)
      let tailRefs := refs.cons (embedding.ref headIndex)
      let tailRefsBefore : ContextRefsBefore tailRefs tailEmbedding := by
        intro readName cell source remaining
        cases source with
        | here =>
            change (embedding.event headIndex).val <
              (embedding.event (Fin.succ remaining)).val
            apply embedding.strictMono
            exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
        | there source => exact refsBefore source (Fin.succ remaining)
      let tailPublications : PublicationRefs
          (Vegas.EventGraph.fieldLayout inputs outputs)
          ((name, .publicData _) :: _) := weakenPublications publications
      let tailPublicationsBefore : PublicationsBeforeAll
          tailPublications tailEmbedding := by
        intro remaining readOwner readPayload readName source field found
        cases source with
        | there source =>
            change FieldBefore (embedding.event (Fin.succ remaining)) field
            exact publicationsBefore (Fin.succ remaining) source field found
      Fin.cases head
        (compileRankedNodes next (by simp [fresh, unique]) tailRefs tailPublications
          registry.weaken tailEmbedding tailRefsBefore tailPublicationsBefore) index
  | _, _, .commit name owner fresh guard next, unique, refs, publications, registry,
      embedding, refsBefore, publicationsBefore, index =>
      let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
        ⟨0, by simp [eventCount]⟩
      let head : RankedNode inputs outputs (embedding.event headIndex) (.binding owner _) :=
        { code := .bind owner _
          reads_before := by simp [Vegas.EventGraph.EventCode.readFields] }
      let obligation : Obligation _ :=
        { owner := owner, subject := name, payload := _, source := .here,
          guard := guard.weaken }
      let tailEmbedding := embedding.tail next rfl (fun _ => rfl)
      let tailRefs := refs.cons (embedding.ref headIndex)
      let tailRefsBefore : ContextRefsBefore tailRefs tailEmbedding := by
        intro readName cell source remaining
        cases source with
        | here =>
            change (embedding.event headIndex).val <
              (embedding.event (Fin.succ remaining)).val
            apply embedding.strictMono
            exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
        | there source => exact refsBefore source (Fin.succ remaining)
      let tailPublications : PublicationRefs
          (Vegas.EventGraph.fieldLayout inputs outputs)
          ((name, .privateData owner _) :: _) := weakenPublications publications
      let tailPublicationsBefore : PublicationsBeforeAll
          tailPublications tailEmbedding := by
        intro remaining readOwner readPayload readName source field found
        cases source with
        | here => cases found
        | there source =>
            change FieldBefore (embedding.event (Fin.succ remaining)) field
            exact publicationsBefore (Fin.succ remaining) source field found
      Fin.cases head
        (compileRankedNodes next (by simp [fresh, unique]) tailRefs tailPublications
          (obligation :: registry.weaken) tailEmbedding tailRefsBefore
          tailPublicationsBefore) index
  | Γ, _, .reveal published owner name fresh selected unresolved next, unique, refs,
      publications, registry, embedding, refsBefore, publicationsBefore, index =>
      let headIndex : Fin (eventCount
          (.reveal published owner name fresh selected unresolved next)) :=
        ⟨0, by simp [eventCount]⟩
      let operands : ∀ {readOwner readPayload readName},
          HasVar Γ readName (.privateData readOwner readPayload) →
            Vegas.EventGraph.GuardOperand
              (Vegas.EventGraph.fieldLayout inputs outputs) _ readPayload :=
        proposedOperands publications unique selected
      let checks := registry.map (compileGuard refs operands)
      let head : RankedNode inputs outputs (embedding.event headIndex) (.publication _) :=
        { code := .resolve owner _ (refs.get selected) checks
          reads_before := by
            intro field member
            rw [Vegas.EventGraph.EventCode.readFields.eq_def,
              Finset.mem_insert] at member
            rcases member with binding | checksMember
            · subst field
              exact refsBefore selected headIndex
            · exact compileGuards_before (embedding.event headIndex) refs
                (fun source => refsBefore source headIndex) operands
                (proposedOperands_before publications unique selected _
                  (publicationsBefore headIndex)) registry field checksMember }
      let resultRef : Vegas.EventGraph.FieldRef
          (Vegas.EventGraph.fieldLayout inputs outputs) (.publication _) := by
        simpa [headIndex, outputLayout, eventCount] using embedding.ref headIndex
      let tailEmbedding := embedding.tail next rfl (fun _ => rfl)
      let tailRefs := refs.cons resultRef
      let tailRefsBefore : ContextRefsBefore tailRefs tailEmbedding := by
        intro readName cell source remaining
        cases source with
        | here =>
            change (embedding.event headIndex).val <
              (embedding.event (Fin.succ remaining)).val
            apply embedding.strictMono
            exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
        | there source => exact refsBefore source (Fin.succ remaining)
      let tailPublications : PublicationRefs
          (Vegas.EventGraph.fieldLayout inputs outputs)
          ((published, .publication _) :: Γ) :=
        resolvePublications publications unique selected resultRef
      let tailPublicationsBefore : PublicationsBeforeAll
          tailPublications tailEmbedding := by
        intro remaining readOwner readPayload readName source field found
        cases source with
        | there source =>
            change FieldBefore (embedding.event (Fin.succ remaining)) field
            by_cases same : readName = name
            · subst readName
              have cellEq := HasVar.type_unique unique source selected
              cases cellEq
              have sameField : resultRef.field = field := by
                simpa [tailPublications, resolvePublications,
                  PublicationRef.field?] using found
              subst field
              apply embedding.strictMono
              exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
            · exact publicationsBefore (Fin.succ remaining) source field (by
                simpa [tailPublications, resolvePublications, same] using found)
      Fin.cases head
        (compileRankedNodes next (by simp [fresh, unique]) tailRefs tailPublications
          registry.weaken tailEmbedding tailRefsBefore tailPublicationsBefore) index

end Vegas.SourceProgram.EventLowering
