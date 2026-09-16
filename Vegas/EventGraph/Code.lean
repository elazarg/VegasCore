/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Foundation.DeferredGuard

/-! # Typed node code for dependency-driven event graphs

This module contains the source-independent code carried by event-graph nodes.
It deliberately does not define event identities, scheduling, or graph execution.
Every evaluator reads a typed partial store and returns `none` when a required
field is unavailable; no arbitrary default value is used.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability Interaction

variable {Player : Type} {L : IExpr} [R : IExpr.ResultTypes L]

/-- The three semantic kinds of fields in an event graph. Binding and
publication fields retain their original payload type, independently of whether
the expression language's result-type constructor is injective. -/
inductive EventField (Player : Type) (L : IExpr) where
  | publicData (payload : L.Ty)
  | binding (owner : Player) (payload : L.Ty)
  | publication (payload : L.Ty)

namespace EventField

/-- Semantic values stored in fields. -/
abbrev Value : EventField Player L → Type
  | .publicData payload => L.Val payload
  | .binding _ payload => PublicationResult (L.Val payload)
  | .publication payload => PublicationResult (L.Val payload)

/-- The semantic action selected at an event producing this field kind. -/
abbrev Action : EventField Player L → Type
  | .publicData _ => PUnit
  | .binding _ payload => PublicationResult (L.Val payload)
  | .publication _ => Bool

end EventField

/-- A typed reference into a fixed field layout. -/
structure FieldRef {Field : Type} (layout : Field → EventField Player L)
    (kind : EventField Player L) where
  field : Field
  layout_eq : layout field = kind

/-- A partial graph store. Availability is represented only by the outer
`Option`; failure-aware field values remain ordinary stored values. -/
abbrev Store {Field : Type} (layout : Field → EventField Player L) :=
  (field : Field) → Option ((layout field).Value)

namespace FieldRef

/-- Read a referenced field, transporting along its certified layout kind. -/
def get? {Field : Type} {layout : Field → EventField Player L}
    {kind : EventField Player L} (ref : FieldRef layout kind)
    (store : Store layout) : Option kind.Value :=
  cast (congrArg (fun fieldKind => Option fieldKind.Value) ref.layout_eq) (store ref.field)

omit R in theorem get?_isSome {Field : Type} {layout : Field → EventField Player L}
    {kind : EventField Player L} (ref : FieldRef layout kind)
    (store : Store layout) (available : (store ref.field).isSome = true) :
    (ref.get? store).isSome = true := by
  cases ref with
  | mk field layout_eq =>
      cases layout_eq
      exact available

end FieldRef

namespace Store

/-- Pointwise agreement on a finite field footprint. -/
def AgreeOn {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} (left right : Store layout)
    (fields : Finset Field) : Prop :=
  ∀ field, field ∈ fields → left field = right field

end Store

/-- A public expression input. Publication fields are exposed at the embedded
language's result type while retaining their original payload in the reference. -/
inductive PublicRead {Field : Type} (layout : Field → EventField Player L) : L.Ty → Type
  | publicData {payload : L.Ty}
      (ref : FieldRef layout (.publicData payload)) : PublicRead layout payload
  | publication {payload : L.Ty}
      (ref : FieldRef layout (.publication payload)) : PublicRead layout (R.result payload)

namespace PublicRead

def field {Field : Type} {layout : Field → EventField Player L} {payload : L.Ty} :
    PublicRead (R := R) layout payload → Field
  | .publicData ref => ref.field
  | .publication ref => ref.field

/-- Read and encode a public operand for ordinary expression evaluation. -/
def get? {Field : Type} {layout : Field → EventField Player L} {payload : L.Ty}
    (read : PublicRead (R := R) layout payload) (store : Store layout) :
    Option (L.Val payload) :=
  match read with
  | .publicData ref => ref.get? store
  | .publication ref => (ref.get? store).map (R.valueEquiv _).symm

theorem get?_congr {Field : Type} {layout : Field → EventField Player L}
    {payload : L.Ty} (read : PublicRead (R := R) layout payload)
    (left right : Store layout)
    (agree : left read.field = right read.field) :
    read.get? left = read.get? right := by
  cases read with
  | publicData ref =>
      change left ref.field = right ref.field at agree
      simp only [get?, FieldRef.get?]
      rw [agree]
  | publication ref =>
      change left ref.field = right ref.field at agree
      simp only [get?, FieldRef.get?]
      rw [agree]

theorem get?_isSome {Field : Type} {layout : Field → EventField Player L}
    {payload : L.Ty} (read : PublicRead (R := R) layout payload)
    (store : Store layout) (available : (store read.field).isSome = true) :
    (read.get? store).isSome = true := by
  cases read with
  | publicData ref => exact ref.get?_isSome store available
  | publication ref =>
      have present := ref.get?_isSome store available
      change ((ref.get? store).map (R.valueEquiv _).symm).isSome = true
      cases hvalue : ref.get? store with
      | none => simp [hvalue] at present
      | some value => rfl

end PublicRead

private def collectPublicReads {Field : Type} {layout : Field → EventField Player L}
    (deps : Finset VarId) :
    (schema : Ctx L.Ty) →
      (∀ {name payload}, HasVar schema name payload → PublicRead (R := R) layout payload) →
      Store layout →
      Option (∀ {name payload}, HasVar schema name payload → name ∈ deps → L.Val payload)
  | [], _, _ => some fun h _ => nomatch h
  | (name, payload) :: tail, reads, store =>
      let rest := collectPublicReads deps tail (fun h => reads (.there h)) store
      if member : name ∈ deps then
        (reads (HasVar.here : HasVar ((name, payload) :: tail) name payload)).get? store >>=
          fun value =>
        rest.map fun tailGet {refName refPayload}
            (h : HasVar ((name, payload) :: tail) refName refPayload) hx =>
          match h with
          | HasVar.here => value
          | HasVar.there h => tailGet h hx
      else
        rest.map fun tailGet {refName refPayload}
            (h : HasVar ((name, payload) :: tail) refName refPayload) hx =>
          match h with
          | HasVar.here => False.elim (member hx)
          | HasVar.there h => tailGet h hx

private theorem collectPublicReads_congr {Field : Type}
    {layout : Field → EventField Player L} (deps : Finset VarId)
    (schema : Ctx L.Ty)
    (reads : ∀ {name payload}, HasVar schema name payload →
      PublicRead (R := R) layout payload)
    (left right : Store layout)
    (agree : ∀ {name payload} (ref : HasVar schema name payload), name ∈ deps →
      (reads ref).get? left = (reads ref).get? right) :
    collectPublicReads deps schema reads left = collectPublicReads deps schema reads right := by
  induction schema with
  | nil => rfl
  | cons entry tail ih =>
      obtain ⟨name, payload⟩ := entry
      have tailEq := ih (fun ref => reads (.there ref))
        (fun ref member => agree (.there ref) member)
      by_cases member : name ∈ deps
      · have headEq := agree
          (HasVar.here : HasVar ((name, payload) :: tail) name payload) member
        simp only [collectPublicReads, dif_pos member]
        rw [headEq, tailEq]
      · simp only [collectPublicReads, dif_neg member]
        rw [tailEq]

private theorem collectPublicReads_isSome {Field : Type}
    {layout : Field → EventField Player L} (deps : Finset VarId)
    (schema : Ctx L.Ty)
    (reads : ∀ {name payload}, HasVar schema name payload →
      PublicRead (R := R) layout payload)
    (store : Store layout)
    (available : ∀ {name payload} (ref : HasVar schema name payload), name ∈ deps →
      (store (reads ref).field).isSome = true) :
    (collectPublicReads deps schema reads store).isSome = true := by
  induction schema with
  | nil => rfl
  | cons entry tail ih =>
      obtain ⟨name, payload⟩ := entry
      have tailAvailable : ∀ {refName refPayload}
          (ref : HasVar tail refName refPayload), refName ∈ deps →
          (store (reads (.there ref)).field).isSome = true := by
        intro refName refPayload ref member
        exact available (.there ref) member
      have tailPresent := ih (fun ref => reads (.there ref)) tailAvailable
      by_cases member : name ∈ deps
      · have headPresent := PublicRead.get?_isSome (reads
          (HasVar.here : HasVar ((name, payload) :: tail) name payload)) store
          (available HasVar.here member)
        cases hhead : (reads
          (HasVar.here : HasVar ((name, payload) :: tail) name payload)).get? store <;>
            simp_all [collectPublicReads]
      · simp [collectPublicReads, member, tailPresent]

/-- Ordinary expression code whose inputs are public event fields. `readFields`
is a finite scheduling footprint covering every semantically supported read. -/
structure PublicExpr {Field : Type} [DecidableEq Field]
    (layout : Field → EventField Player L) (payload : L.Ty) where
  schema : Ctx L.Ty
  code : L.Expr schema payload
  reads : ∀ {name input}, HasVar schema name input → PublicRead (R := R) layout input
  readFields : Finset Field
  reads_mem : ∀ {name input} (ref : HasVar schema name input),
    name ∈ L.exprDeps code → (reads ref).field ∈ readFields

namespace PublicExpr

/-- Evaluate an expression if every declared dependency is available. -/
def eval? {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (expr : PublicExpr (R := R) layout payload) (store : Store layout) :
    Option (L.Val payload) :=
  (collectPublicReads (R := R) (L.exprDeps expr.code) expr.schema expr.reads store).map
    fun get => L.evalDeps expr.code fun _ _ ref member => get ref member

theorem eval?_isSome {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (expr : PublicExpr (R := R) layout payload) (store : Store layout)
    (available : ∀ field ∈ expr.readFields, (store field).isSome = true) :
    (expr.eval? store).isSome = true := by
  unfold eval?
  rw [Option.isSome_map]
  exact collectPublicReads_isSome (L.exprDeps expr.code) expr.schema expr.reads store
    (fun ref member => available _ (expr.reads_mem ref member))

theorem eval?_congr {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (expr : PublicExpr (R := R) layout payload) (left right : Store layout)
    (agree : Store.AgreeOn left right expr.readFields) :
    expr.eval? left = expr.eval? right := by
  unfold eval?
  have collected := collectPublicReads_congr (R := R) (L.exprDeps expr.code)
    expr.schema expr.reads left right
    (fun ref member => PublicRead.get?_congr (expr.reads ref) left right
      (agree _ (expr.reads_mem ref member)))
  rw [collected]

end PublicExpr

/-- Distribution code whose inputs are public event fields. -/
structure PublicDist {Field : Type} [DecidableEq Field]
    (layout : Field → EventField Player L) (payload : L.Ty) where
  schema : Ctx L.Ty
  code : L.DistExpr schema payload
  reads : ∀ {name input}, HasVar schema name input → PublicRead (R := R) layout input
  readFields : Finset Field
  reads_mem : ∀ {name input} (ref : HasVar schema name input),
    name ∈ L.distDeps code → (reads ref).field ∈ readFields

namespace PublicDist

/-- Evaluate the retained exact rational law if every declared dependency is
available. -/
def evalLaw? {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (dist : PublicDist (R := R) layout payload) (store : Store layout) :
    Option (RationalLaw (L.Val payload)) :=
  (collectPublicReads (R := R) (L.distDeps dist.code) dist.schema dist.reads store).map
    fun get => L.evalLawDeps dist.code fun _ _ ref member => get ref member

/-- Denote an available retained exact law as the semantic finite law. -/
def eval? {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (dist : PublicDist (R := R) layout payload) (store : Store layout) :
    Option (FinDist (L.Val payload)) :=
  (dist.evalLaw? store).map RationalLaw.denote

theorem evalLaw?_isSome {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (dist : PublicDist (R := R) layout payload) (store : Store layout)
    (available : ∀ field ∈ dist.readFields, (store field).isSome = true) :
    (dist.evalLaw? store).isSome = true := by
  unfold evalLaw?
  rw [Option.isSome_map]
  exact collectPublicReads_isSome (L.distDeps dist.code) dist.schema dist.reads store
    (fun ref member => available _ (dist.reads_mem ref member))

theorem eval?_isSome {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (dist : PublicDist (R := R) layout payload) (store : Store layout)
    (available : ∀ field ∈ dist.readFields, (store field).isSome = true) :
    (dist.eval? store).isSome = true := by
  unfold eval?
  rw [Option.isSome_map]
  exact dist.evalLaw?_isSome store available

end PublicDist

/-- Turn a stored publication result into a resolved deferred-guard operand. -/
def publicationOfResult {A : Type} : PublicationResult A → Publication A
  | .failure => .failed
  | .success value => .value value

/-- Deferred-guard operands available while validating a resolution. The
`proposed` constructor is intrinsically tied to that resolution's payload. -/
inductive GuardOperand {Field : Type} (layout : Field → EventField Player L)
    (currentPayload : L.Ty) : L.Ty → Type
  | pending {payload : L.Ty} : GuardOperand layout currentPayload payload
  | publicData {payload : L.Ty}
      (ref : FieldRef layout (.publicData payload)) : GuardOperand layout currentPayload payload
  | publication {payload : L.Ty}
      (ref : FieldRef layout (.publication payload)) : GuardOperand layout currentPayload payload
  | proposed : GuardOperand layout currentPayload currentPayload

namespace GuardOperand

def field? {Field : Type} {layout : Field → EventField Player L}
    {currentPayload payload : L.Ty} :
    GuardOperand layout currentPayload payload → Option Field
  | .pending | .proposed => none
  | .publicData ref | .publication ref => some ref.field

/-- Evaluate an operand. Explicit pending and the current proposal do not read
the store; referenced public fields must be available. -/
def get? {Field : Type} {layout : Field → EventField Player L}
    {currentPayload payload : L.Ty}
    (operand : GuardOperand layout currentPayload payload) (store : Store layout)
    (proposal : PublicationResult (L.Val currentPayload)) :
    Option (Publication (L.Val payload)) :=
  match operand with
  | .pending => some .pending
  | .publicData ref => (ref.get? store).map .value
  | .publication ref => (ref.get? store).map publicationOfResult
  | .proposed => some (publicationOfResult proposal)

omit R in theorem get?_isSome {Field : Type} {layout : Field → EventField Player L}
    {currentPayload payload : L.Ty}
    (operand : GuardOperand layout currentPayload payload) (store : Store layout)
    (proposal : PublicationResult (L.Val currentPayload))
    (available : ∀ field, operand.field? = some field →
      (store field).isSome = true) :
    (operand.get? store proposal).isSome = true := by
  cases operand with
  | pending | proposed => rfl
  | publicData ref =>
      have present := ref.get?_isSome store (available ref.field rfl)
      change ((ref.get? store).map Publication.value).isSome = true
      rw [Option.isSome_map]
      exact present
  | publication ref =>
      have present := ref.get?_isSome store (available ref.field rfl)
      change ((ref.get? store).map publicationOfResult).isSome = true
      rw [Option.isSome_map]
      exact present

end GuardOperand

/-- One retained deferred check for the proposal currently being resolved. -/
structure DeferredCheck {Field : Type} [DecidableEq Field]
    (layout : Field → EventField Player L) (currentPayload : L.Ty) where
  subject : VarId
  payload : L.Ty
  code : DeferredGuardCode L subject payload
  subjectRead : GuardOperand layout currentPayload payload
  reads : ∀ {name input}, HasVar code.schema name input →
    GuardOperand layout currentPayload input
  readFields : Finset Field
  subject_mem : ∀ field, subjectRead.field? = some field → field ∈ readFields
  reads_mem : ∀ {name input} (ref : HasVar code.schema name input) field,
    (reads ref).field? = some field → field ∈ readFields

namespace DeferredCheck

private def collectReads {Field : Type} {layout : Field → EventField Player L}
    {currentPayload : L.Ty} (store : Store layout)
    (proposal : PublicationResult (L.Val currentPayload)) :
    (schema : Ctx L.Ty) →
      (∀ {name input}, HasVar schema name input → GuardOperand layout currentPayload input) →
      Option (∀ {name input}, HasVar schema name input → Publication (L.Val input))
  | [], _ => some fun h => nomatch h
  | (name, input) :: tail, reads =>
      do
      let head ← (reads (HasVar.here : HasVar ((name, input) :: tail) name input)).get?
        store proposal
      let tailGet ← collectReads store proposal tail (fun ref => reads (.there ref))
      pure fun {_ _} ref => match ref with
        | .here => head
        | .there ref => tailGet ref

omit R in private theorem collectReads_isSome {Field : Type}
    {layout : Field → EventField Player L} {currentPayload : L.Ty}
    (store : Store layout) (proposal : PublicationResult (L.Val currentPayload))
    (schema : Ctx L.Ty)
    (reads : ∀ {name input}, HasVar schema name input →
      GuardOperand layout currentPayload input)
    (available : ∀ {name input} (ref : HasVar schema name input) field,
      (reads ref).field? = some field → (store field).isSome = true) :
    (collectReads store proposal schema reads).isSome = true := by
  induction schema with
  | nil => rfl
  | cons entry tail ih =>
      obtain ⟨name, input⟩ := entry
      let headRead := reads (HasVar.here : HasVar ((name, input) :: tail) name input)
      have headPresent := GuardOperand.get?_isSome headRead store proposal
        (fun field found => available HasVar.here field found)
      have tailPresent := ih (fun ref => reads (.there ref))
        (fun ref field found => available (.there ref) field found)
      cases hhead : headRead.get? store proposal with
      | none => simp [hhead] at headPresent
      | some head =>
          cases htail : collectReads store proposal tail (fun ref => reads (.there ref)) with
          | none => simp [htail] at tailPresent
          | some tailGet => simp [collectReads, hhead, htail, headRead]

/-- Evaluate a deferred check if every referenced field operand is available. -/
def eval? {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {currentPayload : L.Ty}
    (check : DeferredCheck layout currentPayload) (store : Store layout)
    (proposal : PublicationResult (L.Val currentPayload)) :
    Option PublicationGuard.Verdict := do
  let subjectValue ← check.subjectRead.get? store proposal
  let inputs ← collectReads store proposal check.code.schema check.reads
  pure (check.code.check subjectValue inputs)

omit R in theorem eval?_isSome {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {currentPayload : L.Ty}
    (check : DeferredCheck layout currentPayload) (store : Store layout)
    (proposal : PublicationResult (L.Val currentPayload))
    (available : ∀ field ∈ check.readFields, (store field).isSome = true) :
    (check.eval? store proposal).isSome = true := by
  have subjectPresent := GuardOperand.get?_isSome check.subjectRead store proposal
    (fun field found => available field (check.subject_mem field found))
  have inputsPresent := collectReads_isSome store proposal check.code.schema check.reads
    (fun ref field found => available field (check.reads_mem ref field found))
  cases hsubject : check.subjectRead.get? store proposal with
  | none => simp [hsubject] at subjectPresent
  | some subjectValue =>
      cases hinputs : collectReads store proposal check.code.schema check.reads with
      | none => simp [hinputs] at inputsPresent
      | some inputs => simp [eval?, hsubject, hinputs]

/-- Union of the public field footprints of a list of deferred checks. -/
def listReadFields {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty} :
    List (DeferredCheck layout payload) → Finset Field
  | [] => ∅
  | check :: checks => check.readFields ∪ listReadFields checks

end DeferredCheck

private def checksAccepted? {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (checks : List (DeferredCheck layout payload)) (store : Store layout)
    (proposal : PublicationResult (L.Val payload)) : Option Bool := match checks with
  | [] => some true
  | check :: rest => do
      let verdict ← check.eval? store proposal
      let accepted ← checksAccepted? rest store proposal
      pure (verdict != .rejected && accepted)

omit R in private theorem checksAccepted?_isSome {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (checks : List (DeferredCheck layout payload)) (store : Store layout)
    (proposal : PublicationResult (L.Val payload))
    (available : ∀ field ∈ DeferredCheck.listReadFields checks,
      (store field).isSome = true) :
    (checksAccepted? checks store proposal).isSome = true := by
  induction checks with
  | nil => rfl
  | cons check rest ih =>
      have checkPresent := check.eval?_isSome store proposal
        (fun field member => available field (Finset.mem_union_left _ member))
      have restPresent := ih (fun field member =>
        available field (Finset.mem_union_right _ member))
      cases hcheck : check.eval? store proposal with
      | none => simp [hcheck] at checkPresent
      | some verdict =>
          cases hrest : checksAccepted? rest store proposal with
          | none => simp [hrest] at restPresent
          | some accepted => simp [checksAccepted?, hcheck, hrest]

/-- Source-independent code for one event. Its index is exactly the kind of
field produced by the event. -/
inductive EventCode {Field : Type} [DecidableEq Field]
    (layout : Field → EventField Player L) : EventField Player L → Type
  | bind (owner : Player) (payload : L.Ty) : EventCode layout (.binding owner payload)
  | resolve (owner : Player) (payload : L.Ty)
      (binding : FieldRef layout (.binding owner payload))
      (checks : List (DeferredCheck layout payload)) : EventCode layout (.publication payload)
  | sample (payload : L.Ty) (law : PublicDist layout payload) :
      EventCode layout (.publicData payload)

namespace EventCode

/-- Strategic owner of a node, if any. -/
def actor {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L} :
    EventCode layout output → Option Player
  | .bind owner _ => some owner
  | .resolve owner _ _ _ => some owner
  | .sample _ _ => none

/-- The prescribed semantic action at a node. Chance nodes have no strategic
action; their randomness is entirely in the retained distribution code. -/
def Action {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L} :
    EventCode layout output → Type := fun _ => EventField.Action output

/-- Finite field footprint required by a node evaluator. -/
def readFields {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L} :
    EventCode layout output → Finset Field
  | .bind _ _ => ∅
  | .resolve _ _ binding checks =>
      insert binding.field (DeferredCheck.listReadFields checks)
  | .sample _ law => law.readFields

/-- Evaluate one node against a partial field store. The outer `Option` records
missing required inputs; the returned finite law is the node's semantic output. -/
def eval? {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} :
    {output : EventField Player L} → (code : EventCode layout output) →
      EventField.Action output → Store layout → Option (FinDist output.Value)
  | _, .bind _ _, action, _ => some (FinDist.pure action)
  | _, .resolve _ _ binding checks, disclose, store => do
      let bound ← binding.get? store
      let proposal := if (show Bool from disclose) then bound else .failure
      let accepted ← checksAccepted? checks store proposal
      pure (FinDist.pure (if accepted then proposal else .failure))
  | _, .sample _ law, _, store => law.eval? store

/-- Availability of the finite node footprint is sufficient for evaluation. -/
theorem eval?_isSome_of_reads {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L}
    (code : EventCode layout output) (action : EventField.Action output)
    (store : Store layout)
    (available : ∀ field ∈ code.readFields, (store field).isSome = true) :
    (code.eval? action store).isSome = true := by
  cases code with
  | bind => rfl
  | resolve owner payload binding checks =>
      have bindingPresent := binding.get?_isSome store
        (available binding.field (Finset.mem_insert_self _ _))
      cases hbinding : binding.get? store with
      | none => simp [hbinding] at bindingPresent
      | some bound =>
          have checksPresent := checksAccepted?_isSome checks store
            (if (show Bool from action) then bound else .failure)
            (fun field member => available field (Finset.mem_insert_of_mem member))
          simp only [eval?, hbinding]
          cases hchecks : checksAccepted? checks store
              (if (show Bool from action) then bound else .failure) <;>
            simp_all
  | sample payload law => exact law.eval?_isSome store available

end EventCode

end Vegas.EventGraph
