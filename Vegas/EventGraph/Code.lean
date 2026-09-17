/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Foundation.Guard

/-! # Typed node code for dependency-driven event graphs

This module contains the source-independent code carried by event-graph nodes.
It deliberately does not define event identities, scheduling, or graph execution.
Every evaluator reads a typed partial store and returns `none` when a required
field is unavailable; no arbitrary default value is used.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

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

omit R in theorem get?_congr {Field : Type} {layout : Field → EventField Player L}
    {kind : EventField Player L} (ref : FieldRef layout kind)
    (left right : Store layout) (agree : left ref.field = right ref.field) :
    ref.get? left = ref.get? right := by
  cases ref with
  | mk field layout_eq =>
      cases layout_eq
      exact agree

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

private theorem collectPublicReads_eq_of_reads {Field : Type}
    {layout : Field → EventField Player L} (deps : Finset VarId)
    (schema : Ctx L.Ty)
    (reads : ∀ {name payload}, HasVar schema name payload →
      PublicRead (R := R) layout payload)
    (store : Store layout) (env : Env L.Val schema)
    (agree : ∀ {name payload} (ref : HasVar schema name payload),
      name ∈ deps → (reads ref).get? store = some (env.get ref)) :
    ∃ get : ∀ {name payload}, HasVar schema name payload →
        name ∈ deps → L.Val payload,
      collectPublicReads deps schema reads store =
          some (fun {_ _} ref member => get ref member) ∧
      ∀ {name payload} (ref : HasVar schema name payload) (member : name ∈ deps),
        get ref member = env.get ref := by
  induction schema with
  | nil =>
      refine ⟨(fun {_ _} ref _ => nomatch ref), rfl, ?_⟩
      intro name payload ref
      nomatch ref
  | cons entry tail ih =>
      obtain ⟨name, payload⟩ := entry
      let tailEnv : Env L.Val tail := fun _ _ ref => env.get (.there ref)
      obtain ⟨tailGet, tailCollected, tailAgree⟩ :=
        ih (fun ref => reads (.there ref)) tailEnv
          (fun ref member => agree (.there ref) member)
      by_cases member : name ∈ deps
      · let get : ∀ {refName refPayload},
            HasVar ((name, payload) :: tail) refName refPayload →
              refName ∈ deps → L.Val refPayload :=
          fun {_ _} ref used => match ref with
            | .here => env.get .here
            | .there ref => tailGet ref used
        refine ⟨get, ?_, ?_⟩
        · simp only [collectPublicReads, dif_pos member]
          rw [agree HasVar.here member, tailCollected]
          simp only [Option.map_some]
          apply congrArg some
          funext refName refPayload ref used
          cases ref <;> rfl
        · intro refName refPayload ref used
          cases ref with
          | here => rfl
          | there ref => exact tailAgree ref used
      · let get : ∀ {refName refPayload},
            HasVar ((name, payload) :: tail) refName refPayload →
              refName ∈ deps → L.Val refPayload :=
          fun {_ _} ref used => match ref with
            | .here => False.elim (member used)
            | .there ref => tailGet ref used
        refine ⟨get, ?_, ?_⟩
        · simp only [collectPublicReads, dif_neg member]
          rw [tailCollected]
          simp only [Option.map_some]
          apply congrArg some
          funext refName refPayload ref used
          cases ref <;> rfl
        · intro refName refPayload ref used
          cases ref with
          | here => exact False.elim (member used)
          | there ref => exact tailAgree ref used

/-- Ordinary expression code whose inputs are public event fields. `PublicExpr.readFields`
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

/-- Evaluation agrees with a full typed environment when every declared read
returns the corresponding environment value. -/
theorem eval?_eq_of_reads {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (expr : PublicExpr (R := R) layout payload) (store : Store layout)
    (env : Env L.Val expr.schema)
    (agree : ∀ {name input} (ref : HasVar expr.schema name input),
      name ∈ L.exprDeps expr.code →
        (expr.reads ref).get? store = some (env.get ref)) :
    expr.eval? store = some (L.eval expr.code env) := by
  obtain ⟨get, collected, getEq⟩ := collectPublicReads_eq_of_reads
    (L.exprDeps expr.code) expr.schema expr.reads store env agree
  unfold eval?
  rw [collected]
  apply congrArg some
  rw [← L.evalDeps_eq_eval expr.code env]
  apply congrArg (L.evalDeps expr.code)
  funext name input ref member
  exact getEq ref member

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

/-- Exact-law evaluation agrees with a full typed environment when every
declared read returns the corresponding environment value. -/
theorem evalLaw?_eq_of_reads {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (dist : PublicDist (R := R) layout payload) (store : Store layout)
    (env : Env L.Val dist.schema)
    (agree : ∀ {name input} (ref : HasVar dist.schema name input),
      name ∈ L.distDeps dist.code →
        (dist.reads ref).get? store = some (env.get ref)) :
    dist.evalLaw? store = some (L.evalLaw dist.code env) := by
  obtain ⟨get, collected, getEq⟩ := collectPublicReads_eq_of_reads
    (L.distDeps dist.code) dist.schema dist.reads store env agree
  unfold evalLaw?
  rw [collected]
  apply congrArg some
  rw [← L.evalLawDeps_eq_evalLaw dist.code env]
  apply congrArg (L.evalLawDeps dist.code)
  funext name input ref member
  exact getEq ref member

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

theorem evalLaw?_congr {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (dist : PublicDist (R := R) layout payload) (left right : Store layout)
    (agree : Store.AgreeOn left right dist.readFields) :
    dist.evalLaw? left = dist.evalLaw? right := by
  unfold evalLaw?
  have collected := collectPublicReads_congr (R := R) (L.distDeps dist.code)
    dist.schema dist.reads left right
    (fun ref member => PublicRead.get?_congr (dist.reads ref) left right
      (agree _ (dist.reads_mem ref member)))
  rw [collected]

theorem eval?_isSome {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (dist : PublicDist (R := R) layout payload) (store : Store layout)
    (available : ∀ field ∈ dist.readFields, (store field).isSome = true) :
    (dist.eval? store).isSome = true := by
  unfold eval?
  rw [Option.isSome_map]
  exact dist.evalLaw?_isSome store available

theorem eval?_congr {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (dist : PublicDist (R := R) layout payload) (left right : Store layout)
    (agree : Store.AgreeOn left right dist.readFields) :
    dist.eval? left = dist.eval? right := by
  unfold eval?
  rw [dist.evalLaw?_congr left right agree]

end PublicDist

/-- Guard operands available while validating a resolution: public fields and
the resolution's own proposal. Every operand is published when the check runs.
The `proposed` constructor is intrinsically tied to that resolution's payload. -/
inductive GuardOperand {Field : Type} (layout : Field → EventField Player L)
    (currentPayload : L.Ty) : L.Ty → Type
  | publicData {payload : L.Ty}
      (ref : FieldRef layout (.publicData payload)) : GuardOperand layout currentPayload payload
  | publication {payload : L.Ty}
      (ref : FieldRef layout (.publication payload)) : GuardOperand layout currentPayload payload
  | proposed : GuardOperand layout currentPayload currentPayload

namespace GuardOperand

def field? {Field : Type} {layout : Field → EventField Player L}
    {currentPayload payload : L.Ty} :
    GuardOperand layout currentPayload payload → Option Field
  | .proposed => none
  | .publicData ref | .publication ref => some ref.field

/-- Evaluate an operand. The current proposal does not read the store;
referenced public fields must be available. -/
def get? {Field : Type} {layout : Field → EventField Player L}
    {currentPayload payload : L.Ty}
    (operand : GuardOperand layout currentPayload payload) (store : Store layout)
    (proposal : PublicationResult (L.Val currentPayload)) :
    Option (PublicationResult (L.Val payload)) :=
  match operand with
  | .publicData ref => (ref.get? store).map .success
  | .publication ref => ref.get? store
  | .proposed => some proposal

omit R in theorem get?_congr {Field : Type} {layout : Field → EventField Player L}
    {currentPayload payload : L.Ty}
    (operand : GuardOperand layout currentPayload payload) (left right : Store layout)
    (proposal : PublicationResult (L.Val currentPayload))
    (agree : ∀ field, operand.field? = some field → left field = right field) :
    operand.get? left proposal = operand.get? right proposal := by
  cases operand with
  | proposed => rfl
  | publicData ref =>
      simp only [get?]
      rw [ref.get?_congr left right (agree ref.field rfl)]
  | publication ref =>
      simp only [get?]
      rw [ref.get?_congr left right (agree ref.field rfl)]

omit R in theorem get?_isSome {Field : Type} {layout : Field → EventField Player L}
    {currentPayload payload : L.Ty}
    (operand : GuardOperand layout currentPayload payload) (store : Store layout)
    (proposal : PublicationResult (L.Val currentPayload))
    (available : ∀ field, operand.field? = some field →
      (store field).isSome = true) :
    (operand.get? store proposal).isSome = true := by
  cases operand with
  | proposed => rfl
  | publicData ref =>
      have present := ref.get?_isSome store (available ref.field rfl)
      change ((ref.get? store).map PublicationResult.success).isSome = true
      rw [Option.isSome_map]
      exact present
  | publication ref => exact ref.get?_isSome store (available ref.field rfl)

end GuardOperand

/-- One guard check completed by the resolution currently being evaluated. It
names an operand for its subject and for every input its code reads; every
operand is published or is the proposal itself. -/
structure GuardCheck {Field : Type} [DecidableEq Field]
    (layout : Field → EventField Player L) (currentPayload : L.Ty) where
  subject : VarId
  payload : L.Ty
  code : GuardCode L subject payload
  subjectRead : GuardOperand layout currentPayload payload
  reads : ∀ {name input}, HasVar code.schema name input → name ∈ L.exprDeps code.code →
    GuardOperand layout currentPayload input
  readFields : Finset Field
  subject_mem : ∀ field, subjectRead.field? = some field → field ∈ readFields
  reads_mem : ∀ {name input} (ref : HasVar code.schema name input)
    (read : name ∈ L.exprDeps code.code) field,
    (reads ref read).field? = some field → field ∈ readFields

namespace GuardCheck

private def collectReads {Field : Type} {layout : Field → EventField Player L}
    {currentPayload : L.Ty} (store : Store layout)
    (proposal : PublicationResult (L.Val currentPayload)) (deps : Finset VarId) :
    (schema : Ctx L.Ty) →
      (∀ {name input}, HasVar schema name input → name ∈ deps →
        GuardOperand layout currentPayload input) →
      Option (∀ {name input}, HasVar schema name input → name ∈ deps →
        PublicationResult (L.Val input))
  | [], _ => some fun h _ => nomatch h
  | (name, input) :: tail, reads =>
      do
      let tailGet ← collectReads store proposal deps tail (fun ref read => reads (.there ref) read)
      if member : name ∈ deps then
        let head ← (reads (HasVar.here : HasVar ((name, input) :: tail) name input) member).get?
          store proposal
        pure fun {_ _} ref read => match ref with
          | .here => head
          | .there ref => tailGet ref read
      else
        pure fun {_ _} ref read => match ref with
          | .here => False.elim (member read)
          | .there ref => tailGet ref read

omit R in private theorem collectReads_congr {Field : Type}
    {layout : Field → EventField Player L} {currentPayload : L.Ty}
    (left right : Store layout) (proposal : PublicationResult (L.Val currentPayload))
    (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {name input}, HasVar schema name input → name ∈ deps →
      GuardOperand layout currentPayload input)
    (agree : ∀ {name input} (ref : HasVar schema name input) (read : name ∈ deps) field,
      (reads ref read).field? = some field → left field = right field) :
    collectReads left proposal deps schema reads =
      collectReads right proposal deps schema reads := by
  induction schema with
  | nil => rfl
  | cons entry tail ih =>
      obtain ⟨name, input⟩ := entry
      have tailEq := ih (fun ref read => reads (.there ref) read)
        (fun ref read field found => agree (.there ref) read field found)
      by_cases member : name ∈ deps
      · have headEq := GuardOperand.get?_congr
          (reads (HasVar.here : HasVar ((name, input) :: tail) name input) member)
          left right proposal (fun field found => agree HasVar.here member field found)
        simp only [collectReads, tailEq, dif_pos member, headEq]
      · simp only [collectReads, tailEq, dif_neg member]

omit R in private theorem collectReads_isSome {Field : Type}
    {layout : Field → EventField Player L} {currentPayload : L.Ty}
    (store : Store layout) (proposal : PublicationResult (L.Val currentPayload))
    (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {name input}, HasVar schema name input → name ∈ deps →
      GuardOperand layout currentPayload input)
    (available : ∀ {name input} (ref : HasVar schema name input) (read : name ∈ deps) field,
      (reads ref read).field? = some field → (store field).isSome = true) :
    (collectReads store proposal deps schema reads).isSome = true := by
  induction schema with
  | nil => rfl
  | cons entry tail ih =>
      obtain ⟨name, input⟩ := entry
      have tailPresent := ih (fun ref read => reads (.there ref) read)
        (fun ref read field found => available (.there ref) read field found)
      cases htail : collectReads store proposal deps tail (fun ref read => reads (.there ref) read)
        with
      | none => simp [htail] at tailPresent
      | some tailGet =>
          by_cases member : name ∈ deps
          · have headPresent := GuardOperand.get?_isSome
              (reads (HasVar.here : HasVar ((name, input) :: tail) name input) member)
              store proposal (fun field found => available HasVar.here member field found)
            cases hhead : (reads (HasVar.here : HasVar ((name, input) :: tail) name input)
                member).get? store proposal with
            | none => simp [hhead] at headPresent
            | some head => simp [collectReads, htail, dif_pos member, hhead]
          · simp [collectReads, htail, dif_neg member]

omit R in private theorem collectReads_eq_of_reads {Field : Type}
    {layout : Field → EventField Player L} {currentPayload : L.Ty}
    (store : Store layout) (proposal : PublicationResult (L.Val currentPayload))
    (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {name input}, HasVar schema name input → name ∈ deps →
      GuardOperand layout currentPayload input)
    (env : ∀ {name input}, HasVar schema name input → name ∈ deps →
      PublicationResult (L.Val input))
    (agree : ∀ {name input} (ref : HasVar schema name input) (read : name ∈ deps),
      (reads ref read).get? store proposal = some (env ref read)) :
    collectReads store proposal deps schema reads =
      (some env : Option (∀ {name input}, HasVar schema name input → name ∈ deps →
        PublicationResult (L.Val input))) := by
  induction schema with
  | nil =>
      apply congrArg some
      funext name input ref
      nomatch ref
  | cons entry tail ih =>
      obtain ⟨name, input⟩ := entry
      have tailCollected := ih (fun ref read => reads (.there ref) read)
        (fun ref read => env (.there ref) read) (fun ref read => agree (.there ref) read)
      by_cases member : name ∈ deps
      · simp only [collectReads, tailCollected, dif_pos member, agree HasVar.here member]
        apply congrArg some
        funext refName refInput ref read
        cases ref <;> rfl
      · simp only [collectReads, tailCollected, dif_neg member]
        apply congrArg some
        funext refName refInput ref read
        cases ref with
        | here => exact absurd read member
        | there ref => rfl

/-- Decide a check if every referenced field operand is available. -/
def eval? {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {currentPayload : L.Ty}
    (check : GuardCheck layout currentPayload) (store : Store layout)
    (proposal : PublicationResult (L.Val currentPayload)) : Option Bool := do
  let subjectResult ← check.subjectRead.get? store proposal
  let inputs ← collectReads store proposal (L.exprDeps check.code.code) check.code.schema
    check.reads
  pure (check.code.accepts subjectResult inputs)

omit R in
/-- Check evaluation is exact when its subject and every code-read operand return
the supplied published results. -/
theorem eval?_eq_of_reads {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {currentPayload : L.Ty}
    (check : GuardCheck layout currentPayload) (store : Store layout)
    (proposal : PublicationResult (L.Val currentPayload))
    (subjectResult : PublicationResult (L.Val check.payload))
    (env : ∀ {name input}, HasVar check.code.schema name input →
      name ∈ L.exprDeps check.code.code → PublicationResult (L.Val input))
    (subjectEq : check.subjectRead.get? store proposal = some subjectResult)
    (readsEq : ∀ {name input} (ref : HasVar check.code.schema name input)
      (read : name ∈ L.exprDeps check.code.code),
      (check.reads ref read).get? store proposal = some (env ref read)) :
    check.eval? store proposal = some (check.code.accepts subjectResult env) := by
  unfold eval?
  rw [subjectEq, collectReads_eq_of_reads store proposal _ check.code.schema
    check.reads env readsEq]
  rfl

omit R in
/-- Only the operand fields actually read by a check matter. A declared read
footprint may conservatively contain additional fields. -/
theorem eval?_congr_reads {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {currentPayload : L.Ty}
    (check : GuardCheck layout currentPayload) (left right : Store layout)
    (proposal : PublicationResult (L.Val currentPayload))
    (subject : ∀ field, check.subjectRead.field? = some field → left field = right field)
    (reads : ∀ {name input} (ref : HasVar check.code.schema name input)
      (read : name ∈ L.exprDeps check.code.code) field,
      (check.reads ref read).field? = some field → left field = right field) :
    check.eval? left proposal = check.eval? right proposal := by
  unfold eval?
  have subjectEq := GuardOperand.get?_congr check.subjectRead left right proposal subject
  have inputsEq := collectReads_congr left right proposal _ check.code.schema check.reads
    reads
  rw [subjectEq, inputsEq]

omit R in theorem eval?_congr {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {currentPayload : L.Ty}
    (check : GuardCheck layout currentPayload) (left right : Store layout)
    (proposal : PublicationResult (L.Val currentPayload))
    (agree : Store.AgreeOn left right check.readFields) :
    check.eval? left proposal = check.eval? right proposal :=
  check.eval?_congr_reads left right proposal
    (fun field found => agree field (check.subject_mem field found))
    (fun ref read field found => agree field (check.reads_mem ref read field found))

omit R in theorem eval?_isSome {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {currentPayload : L.Ty}
    (check : GuardCheck layout currentPayload) (store : Store layout)
    (proposal : PublicationResult (L.Val currentPayload))
    (available : ∀ field ∈ check.readFields, (store field).isSome = true) :
    (check.eval? store proposal).isSome = true := by
  have subjectPresent := GuardOperand.get?_isSome check.subjectRead store proposal
    (fun field found => available field (check.subject_mem field found))
  have inputsPresent := collectReads_isSome store proposal _ check.code.schema check.reads
    (fun ref read field found => available field (check.reads_mem ref read field found))
  cases hsubject : check.subjectRead.get? store proposal with
  | none => simp [hsubject] at subjectPresent
  | some subjectResult =>
      cases hinputs : collectReads store proposal (L.exprDeps check.code.code)
          check.code.schema check.reads with
      | none => simp [hinputs] at inputsPresent
      | some inputs => simp [eval?, hsubject, hinputs]

/-- Union of the public field footprints of a list of checks. -/
def listReadFields {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty} :
    List (GuardCheck layout payload) → Finset Field
  | [] => ∅
  | check :: checks => check.readFields ∪ listReadFields checks

end GuardCheck

namespace GuardCheck

/-- Evaluate every completed check and accept exactly when all accept. -/
def allAccepted? {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (checks : List (GuardCheck layout payload)) (store : Store layout)
    (proposal : PublicationResult (L.Val payload)) : Option Bool := match checks with
  | [] => some true
  | check :: rest => do
      let accepts ← check.eval? store proposal
      let accepted ← allAccepted? rest store proposal
      pure (accepts && accepted)

omit R in theorem allAccepted?_congr {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (checks : List (GuardCheck layout payload)) (left right : Store layout)
    (proposal : PublicationResult (L.Val payload))
    (agree : Store.AgreeOn left right (GuardCheck.listReadFields checks)) :
    allAccepted? checks left proposal = allAccepted? checks right proposal := by
  induction checks with
  | nil => rfl
  | cons check rest ih =>
      have checkEq := check.eval?_congr left right proposal
        (fun field member => agree field (Finset.mem_union_left _ member))
      have restEq := ih (fun field member =>
        agree field (Finset.mem_union_right _ member))
      simp only [allAccepted?]
      rw [checkEq, restEq]

omit R in theorem allAccepted?_isSome {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (checks : List (GuardCheck layout payload)) (store : Store layout)
    (proposal : PublicationResult (L.Val payload))
    (available : ∀ field ∈ GuardCheck.listReadFields checks,
      (store field).isSome = true) :
    (allAccepted? checks store proposal).isSome = true := by
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
          cases hrest : allAccepted? rest store proposal with
          | none => simp [hrest] at restPresent
          | some accepted => simp [allAccepted?, hcheck, hrest]

omit R in
/-- Exact per-check decisions determine the acceptance fold. -/
theorem allAccepted?_eq_of_map_eval? {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (checks : List (GuardCheck layout payload)) (store : Store layout)
    (proposal : PublicationResult (L.Val payload))
    (verdicts : List Bool)
    (exact : checks.map (fun check => check.eval? store proposal) = verdicts.map some) :
    allAccepted? checks store proposal = some (verdicts.all id) := by
  induction checks generalizing verdicts with
  | nil =>
      cases verdicts with
      | nil => rfl
      | cons verdict verdicts => simp at exact
  | cons check checks ih =>
      cases verdicts with
      | nil => simp at exact
      | cons verdict verdicts =>
          simp only [List.map_cons, List.cons.injEq] at exact
          rw [allAccepted?, exact.1, ih verdicts exact.2]
          rfl

end GuardCheck

/-- Source-independent code for one event. Its index is exactly the kind of
field produced by the event. -/
inductive EventCode {Field : Type} [DecidableEq Field]
    (layout : Field → EventField Player L) : EventField Player L → Type
  | bind (owner : Player) (payload : L.Ty) : EventCode layout (.binding owner payload)
  | resolve (owner : Player) (payload : L.Ty)
      (binding : FieldRef layout (.binding owner payload))
      (checks : List (GuardCheck layout payload)) : EventCode layout (.publication payload)
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

theorem actor_cast {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {left right : EventField Player L}
    (same : left = right) (code : EventCode layout left) :
    actor (cast (congrArg (EventCode layout) same) code) = actor code := by
  cases same
  rfl

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
      insert binding.field (GuardCheck.listReadFields checks)
  | .sample _ law => law.readFields

/-- Casting an event code across an equality of output-field descriptions does
not change its retained read footprint. -/
theorem readFields_cast {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {left right : EventField Player L}
    (same : left = right) (code : EventCode layout left) :
    readFields (cast (congrArg (EventCode layout) same) code) = readFields code := by
  cases same
  rfl

/-- Deterministic resolution output before it is embedded in the general
finite-distribution evaluator.  Pending reads are represented by `none`;
binding failure and rejected publication remain ordinary output values. -/
def resolveOutput? {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {owner : Player} {payload : L.Ty}
    (binding : FieldRef layout (.binding owner payload))
    (checks : List (GuardCheck layout payload)) (disclose : Bool)
    (store : Store layout) : Option (PublicationResult (L.Val payload)) := do
  let bound ← binding.get? store
  let proposal := if disclose then bound else .failure
  let accepted ← GuardCheck.allAccepted? checks store proposal
  pure (if accepted then proposal else .failure)

omit R in
/-- Availability of a resolution node's retained footprint makes its
deterministic output defined. -/
theorem resolveOutput?_isSome {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {owner : Player} {payload : L.Ty}
    (binding : FieldRef layout (.binding owner payload))
    (checks : List (GuardCheck layout payload)) (disclose : Bool)
    (store : Store layout)
    (available : ∀ field ∈ insert binding.field
      (GuardCheck.listReadFields checks), (store field).isSome = true) :
    (resolveOutput? binding checks disclose store).isSome = true := by
  have bindingPresent := binding.get?_isSome store
    (available binding.field (Finset.mem_insert_self _ _))
  cases hbinding : binding.get? store with
  | none => simp [hbinding] at bindingPresent
  | some bound =>
      have checksPresent := GuardCheck.allAccepted?_isSome checks store
        (if disclose then bound else .failure)
        (fun field member => available field (Finset.mem_insert_of_mem member))
      cases hchecks : GuardCheck.allAccepted? checks store
          (if disclose then bound else .failure) with
      | none => simp [hchecks] at checksPresent
      | some accepted => simp [resolveOutput?, hbinding, hchecks]

omit R in
/-- Withholding always produces public failure once the retained resolution
footprint is available. -/
theorem resolveOutput?_false_eq_failure {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {owner : Player} {payload : L.Ty}
    (binding : FieldRef layout (.binding owner payload))
    (checks : List (GuardCheck layout payload)) (store : Store layout)
    (available : ∀ field ∈ insert binding.field
      (GuardCheck.listReadFields checks), (store field).isSome = true) :
    resolveOutput? binding checks false store = some .failure := by
  have defined := resolveOutput?_isSome binding checks false store available
  cases outputEq : resolveOutput? binding checks false store with
  | none => simp [outputEq] at defined
  | some output =>
      cases bindingEq : binding.get? store with
      | none => simp [resolveOutput?, bindingEq] at outputEq
      | some bound =>
          cases checksEq : GuardCheck.allAccepted? checks store .failure with
          | none => simp [resolveOutput?, bindingEq, checksEq] at outputEq
          | some accepted =>
              simpa [resolveOutput?, bindingEq, checksEq] using outputEq.symm

omit R in
/-- The deterministic resolution output depends only on the binding and
check footprint retained by the node. -/
theorem resolveOutput?_congr {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {owner : Player} {payload : L.Ty}
    (binding : FieldRef layout (.binding owner payload))
    (checks : List (GuardCheck layout payload)) (disclose : Bool)
    (left right : Store layout)
    (agree : Store.AgreeOn left right
      (insert binding.field (GuardCheck.listReadFields checks))) :
    resolveOutput? binding checks disclose left =
      resolveOutput? binding checks disclose right := by
  have bindingEq := binding.get?_congr left right
    (agree binding.field (Finset.mem_insert_self _ _))
  cases hbound : binding.get? left with
  | none =>
      rw [hbound] at bindingEq
      simp [resolveOutput?, hbound, ← bindingEq]
  | some bound =>
      rw [hbound] at bindingEq
      have checksEq := GuardCheck.allAccepted?_congr checks left right
        (if disclose then bound else .failure)
        (fun field member => agree field (Finset.mem_insert_of_mem member))
      simp [resolveOutput?, hbound, ← bindingEq, checksEq]

/-- Evaluate one node against a partial field store. The outer `Option` records
missing required inputs; the returned finite law is the node's semantic output. -/
def eval? {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} :
    {output : EventField Player L} → (code : EventCode layout output) →
      EventField.Action output → Store layout → Option (FinDist output.Value)
  | _, .bind _ _, action, _ => some (FinDist.pure action)
  | _, .resolve _ _ binding checks, disclose, store =>
      (resolveOutput? binding checks disclose store).map FinDist.pure
  | _, .sample _ law, _, store => law.eval? store

/-- The general evaluator embeds the unique deterministic resolve output as a
point law.  Public-message handlers use `resolveOutput?` directly and prove
their transition law against `eval?` through this equation. -/
@[simp] theorem resolve_eval? {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {owner : Player} {payload : L.Ty}
    (binding : FieldRef layout (.binding owner payload))
    (checks : List (GuardCheck layout payload)) (disclose : Bool)
    (store : Store layout) :
    (EventCode.resolve owner payload binding checks).eval? disclose store =
      (resolveOutput? binding checks disclose store).map FinDist.pure := rfl

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
      rw [resolve_eval?, Option.isSome_map]
      exact resolveOutput?_isSome binding checks action store available
  | sample payload law => exact law.eval?_isSome store available

/-- Strategic nodes are deterministic once their action and declared reads
are fixed. Randomness belongs to sample nodes and to the policy choosing an
action, not to the execution of a supplied strategic action. -/
theorem eval?_eq_pure_of_actor {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L}
    (code : EventCode layout output) (owner : Player) (owned : code.actor = some owner)
    (action : output.Action) (store : Store layout)
    (available : ∀ field ∈ code.readFields, (store field).isSome = true) :
    ∃ value, code.eval? action store = some (FinDist.pure value) := by
  cases code with
  | bind who payload => exact ⟨action, rfl⟩
  | resolve who payload binding checks =>
      have present := resolveOutput?_isSome binding checks action store available
      cases result : resolveOutput? binding checks action store with
      | none => simp [result] at present
      | some value => exact ⟨value, by simp [eval?, result]⟩
  | sample payload law => simp [actor] at owned

/-- Node evaluation depends only on the node's declared finite footprint. -/
theorem eval?_congr {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L}
    (code : EventCode layout output) (action : EventField.Action output)
    (left right : Store layout) (agree : Store.AgreeOn left right code.readFields) :
    code.eval? action left = code.eval? action right := by
  cases code with
  | bind => rfl
  | resolve owner payload binding checks =>
      exact congrArg (Option.map FinDist.pure)
        (resolveOutput?_congr binding checks action left right agree)
  | sample payload law => exact law.eval?_congr left right agree

end EventCode

end Vegas.EventGraph
