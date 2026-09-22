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
  | (_, .commitment _ _) :: _tail, refs, _, _, source =>
      publicRead (ContextRefs.mk fun source => refs.get (.there source)) source
  | (_, .privateInput _ _) :: _tail, refs, _, _, source =>
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

/-- Operand for a publication cell at a reveal: the reveal's own publication is
its proposal, and every earlier publication is its public field. -/
def revealOperand {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {published : VarId} {payload : L.Ty}
    (refs : ContextRefs layout Γ) :
    {name : VarId} → {τ : L.Ty} →
      HasVar ((published, .publication payload) :: Γ) name (.publication τ) →
        Vegas.EventGraph.GuardOperand layout payload τ
  | _, _, .here => .proposed
  | _, _, .there cell => .publication (refs.get cell)

/-- Lower a published guard input at a reveal. The proof that it is published
rules out an unrevealed private cell. -/
def compileGuardRead {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {published : VarId} {payload : L.Ty}
    {author : Player} {τ : L.Ty}
    (refs : ContextRefs layout Γ)
    (revealed : Revelations ((published, .publication payload) :: Γ)) :
    (read : SourceGuardRead ((published, .publication payload) :: Γ) author τ) →
      read.revealed revealed = true → Vegas.EventGraph.GuardOperand layout payload τ
  | .publicData (.there cell), _ => .publicData (refs.get cell)
  | .publication cell, _ => revealOperand refs cell
  | .commitment cell, isRevealed =>
      match revelation : revealed cell with
      | .revealed publication => revealOperand refs publication
      | .unrevealed => absurd isRevealed (by
          simp [SourceGuardRead.revealed, revelation, Revelation.isRevealed])

private def operandField {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {currentPayload payload : L.Ty}
    (operand : Vegas.EventGraph.GuardOperand layout currentPayload payload) : Finset Field :=
  match operand.field? with
  | none => ∅
  | some field => {field}

private def guardReadFields {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {currentPayload : L.Ty} (deps : Finset VarId) :
    (schema : Ctx L.Ty) →
      (∀ {name payload}, HasVar schema name payload → name ∈ deps →
        Vegas.EventGraph.GuardOperand layout currentPayload payload) → Finset Field
  | [], _ => ∅
  | (name, _) :: tail, reads =>
      (if member : name ∈ deps then operandField (reads .here member) else ∅) ∪
        guardReadFields deps tail (fun source read => reads (.there source) read)

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
    {currentPayload : L.Ty} (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {name payload}, HasVar schema name payload → name ∈ deps →
      Vegas.EventGraph.GuardOperand layout currentPayload payload)
    {name payload} (source : HasVar schema name payload) (read : name ∈ deps)
    (field : Field) (found : (reads source read).field? = some field) :
    field ∈ guardReadFields deps schema reads := by
  induction source with
  | @here tail name payload =>
      apply Finset.mem_union_left
      simpa [read] using operandField_mem _ _ found
  | there source ih =>
      apply Finset.mem_union_right
      exact ih (fun source read => reads (.there source) read) read found

omit [DecidableEq Player] R in
private theorem mem_guardReadFields {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {currentPayload : L.Ty} (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {name payload}, HasVar schema name payload → name ∈ deps →
      Vegas.EventGraph.GuardOperand layout currentPayload payload)
    (field : Field) (member : field ∈ guardReadFields deps schema reads) :
    ∃ (name : VarId) (payload : L.Ty) (source : HasVar schema name payload)
      (read : name ∈ deps), (reads source read).field? = some field := by
  induction schema with
  | nil => simp [guardReadFields] at member
  | cons entry tail ih =>
      obtain ⟨name, payload⟩ := entry
      rw [guardReadFields, Finset.mem_union] at member
      rcases member with head | rest
      · by_cases flagged : name ∈ deps
        · rw [dite_eq_left flagged] at head
          exact ⟨name, payload, .here, flagged, (mem_operandField_iff _ _).mp head⟩
        · simp [flagged] at head
      · obtain ⟨readName, readPayload, source, read, found⟩ :=
          ih (fun source read => reads (.there source) read) rest
        exact ⟨readName, readPayload, .there source, read, found⟩

/-- Lower one obligation completed by a reveal to an executable guard check. -/
def compileGuard {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {published : VarId} {payload : L.Ty}
    (refs : ContextRefs layout Γ) (revealed : Revelations ((published, .publication payload) :: Γ))
    (obligation : Obligation (Player := Player) (L := L) ((published, .publication payload) :: Γ))
    (isRevealed : obligation.revealed revealed = true) :
    Vegas.EventGraph.GuardCheck layout payload :=
  let published := (Bool.and_eq_true _ _).mp isRevealed
  let subjectRead := compileGuardRead refs revealed (.commitment obligation.source) published.1
  let reads : ∀ {name input}, HasVar obligation.guard.schema name input →
      name ∈ L.exprDeps obligation.guard.code →
        Vegas.EventGraph.GuardOperand layout payload input :=
    fun source read => compileGuardRead refs revealed (obligation.guard.reads source)
      ((GuardCode.allReads_iff _ _).mp published.2 source read)
  { subject := obligation.subject
    payload := obligation.payload
    code := obligation.guard.toGuardCode
    subjectRead := subjectRead
    reads := reads
    readFields := operandField subjectRead ∪ guardReadFields _ _ reads
    subject_mem := fun field found =>
      Finset.mem_union_left _ (operandField_mem subjectRead field found)
    reads_mem := fun source read field found =>
      Finset.mem_union_right _ (guardReadFields_mem _ _ reads source read field found) }

/-- The checks a reveal performs: one for each obligation it completes. -/
def compileChecks {Field : Type} [DecidableEq Field]
    {layout : Field → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {published name : VarId} {owner : Player} {payload : L.Ty}
    (refs : ContextRefs layout Γ) (registry : Registry (Player := Player) (L := L) Γ)
    (revelations : Revelations Γ) (selected : HasVar Γ name (.commitment owner payload)) :
    List (Vegas.EventGraph.GuardCheck layout payload) :=
  (registry.completedBy (published := published) revelations selected).attach.map
    fun obligation => compileGuard refs (revelations.reveal selected) obligation.1
      (registry.revealed_of_mem_completedBy revelations selected obligation.2)

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
      · simp only [publicReadFields, ite_eq_left used, Finset.mem_insert] at member
        rcases member with same | member
        · subst field
          exact before .here
        · exact ih (fun source => reads (.there source))
            (fun source => before (.there source)) field member
      · simp only [publicReadFields, ite_eq_right used] at member
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
  | (_, .commitment _ _) :: _tail, refs, before, _, _, source =>
      publicRead_before (ContextRefs.mk fun source => refs.get (.there source))
        (fun source => before (.there source)) source
  | (_, .privateInput _ _) :: _tail, refs, before, _, _, source =>
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

omit [DecidableEq Player] R in
private theorem revealOperand_before {inputCount eventCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin eventCount → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {published : VarId} {payload : L.Ty}
    (target : Fin eventCount)
    (refs : ContextRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ)
    (refsBefore : ∀ {name cell} (source : HasVar Γ name cell),
      FieldBefore target (refs.get source).field)
    {name : VarId} {τ : L.Ty}
    (cell : HasVar ((published, .publication payload) :: Γ) name (.publication τ)) :
    OperandBefore target (revealOperand refs cell) := by
  intro field found
  cases cell with
  | here => cases found
  | there cell =>
      simp only [revealOperand, Vegas.EventGraph.GuardOperand.field?,
        Option.some.injEq] at found
      subst field
      exact refsBefore cell

omit [DecidableEq Player] R in
private theorem compileGuardRead_before {inputCount eventCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin eventCount → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {published : VarId} {payload : L.Ty}
    {author : Player} {τ : L.Ty} (target : Fin eventCount)
    (refs : ContextRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ)
    (refsBefore : ∀ {name cell} (source : HasVar Γ name cell),
      FieldBefore target (refs.get source).field)
    (revealed : Revelations ((published, .publication payload) :: Γ))
    (read : SourceGuardRead ((published, .publication payload) :: Γ) author τ)
    (isRevealed : read.revealed revealed = true) :
    OperandBefore target (compileGuardRead refs revealed read isRevealed) := by
  cases read with
  | publicData cell =>
      cases cell with
      | there cell =>
          intro field found
          simp only [compileGuardRead, Vegas.EventGraph.GuardOperand.field?,
            Option.some.injEq] at found
          subst field
          exact refsBefore cell
  | publication cell => exact revealOperand_before target refs refsBefore cell
  | commitment cell =>
      simp only [compileGuardRead]
      split
      · exact revealOperand_before target refs refsBefore _
      · next revelation =>
          simp [SourceGuardRead.revealed, revelation, Revelation.isRevealed] at isRevealed

omit [DecidableEq Player] R in
private theorem compileGuard_before {inputCount eventCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin eventCount → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {published : VarId} {payload : L.Ty}
    (target : Fin eventCount)
    (refs : ContextRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ)
    (refsBefore : ∀ {name cell} (source : HasVar Γ name cell),
      FieldBefore target (refs.get source).field)
    (revealed : Revelations ((published, .publication payload) :: Γ))
    (obligation : Obligation (Player := Player) (L := L)
      ((published, .publication payload) :: Γ))
    (isRevealed : obligation.revealed revealed = true) :
    ∀ field, field ∈ (compileGuard refs revealed obligation isRevealed).readFields →
      FieldBefore target field := by
  intro field member
  rw [compileGuard, Finset.mem_union] at member
  rcases member with subject | reads
  · exact compileGuardRead_before target refs refsBefore revealed _ _ field
      ((mem_operandField_iff _ _).mp subject)
  · obtain ⟨name, input, source, read, found⟩ := mem_guardReadFields _ _ _ field reads
    exact compileGuardRead_before target refs refsBefore revealed _ _ field found

omit [DecidableEq Player] R in
private theorem compileChecks_before {inputCount eventCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin eventCount → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {published name : VarId} {owner : Player} {payload : L.Ty}
    (target : Fin eventCount)
    (refs : ContextRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ)
    (refsBefore : ∀ {name cell} (source : HasVar Γ name cell),
      FieldBefore target (refs.get source).field)
    (registry : Registry (Player := Player) (L := L) Γ) (revelations : Revelations Γ)
    (selected : HasVar Γ name (.commitment owner payload)) :
    ∀ field, field ∈ Vegas.EventGraph.GuardCheck.listReadFields
      (compileChecks (published := published) refs registry revelations selected) →
        FieldBefore target field := by
  unfold compileChecks
  generalize (registry.completedBy (published := published) revelations selected).attach = checks
  intro field member
  induction checks with
  | nil => simp [Vegas.EventGraph.GuardCheck.listReadFields] at member
  | cons check checks ih =>
      rw [List.map_cons, Vegas.EventGraph.GuardCheck.listReadFields,
        Finset.mem_union] at member
      rcases member with head | tail
      · exact compileGuard_before target refs refsBefore _ _ _ field head
      · exact ih tail

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
    (refs : ContextRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ) →
    (revelations : Revelations Γ) →
    (registry : Registry Γ) →
    (embedding : OutputEmbedding inputs outputs program) →
    ContextRefsBefore refs embedding →
    ∀ index, RankedNode inputs outputs (embedding.event index) (outputLayout program index)
  | _, _, .ret _, _, _, _, _, _, index => nomatch index
  | _, _, .sample name fresh law next, refs, revelations, registry,
      embedding, refsBefore, index =>
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
      Fin.cases head
        (compileRankedNodes next tailRefs revelations.weaken
          registry.weaken tailEmbedding tailRefsBefore) index
  | _, _, .commit name owner fresh guard next, refs, revelations, registry,
      embedding, refsBefore, index =>
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
      Fin.cases head
        (compileRankedNodes next tailRefs revelations.weaken
          (obligation :: registry.weaken) tailEmbedding tailRefsBefore) index
  | Γ, _, .reveal published owner name fresh selected unresolved next, refs,
      revelations, registry, embedding, refsBefore, index =>
      let headIndex : Fin (eventCount
          (.reveal published owner name fresh selected unresolved next)) :=
        ⟨0, by simp [eventCount]⟩
      let checks := compileChecks (published := published) refs registry revelations selected
      let head : RankedNode inputs outputs (embedding.event headIndex) (.publication _) :=
        { code := .resolve owner _ (refs.get selected) checks
          reads_before := by
            intro field member
            rw [Vegas.EventGraph.EventCode.readFields.eq_def,
              Finset.mem_insert] at member
            rcases member with binding | checksMember
            · subst field
              exact refsBefore selected headIndex
            · exact compileChecks_before (embedding.event headIndex) refs
                (fun source => refsBefore source headIndex) registry revelations selected
                field checksMember }
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
      Fin.cases head
        (compileRankedNodes next tailRefs
          (revelations.reveal (published := published) selected) registry.weaken
          tailEmbedding tailRefsBefore) index

end Vegas.SourceProgram.EventLowering
