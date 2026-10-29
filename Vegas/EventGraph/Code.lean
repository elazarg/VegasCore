/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

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

/-- Typed graph fields distinguish persistent private inputs from bindings and
public data. Bindings and publications retain their original payload type,
independently of the expression language's result-type constructor. -/
inductive EventField (Player : Type) (L : IExpr) where
  | publicData (payload : L.Ty)
  | privateInput (owner : Player) (payload : L.Ty)
  | binding (owner : Player) (payload : L.Ty)
  | publication (payload : L.Ty)

namespace EventField

/-- Semantic values stored in fields. -/
abbrev Value : EventField Player L → Type
  | .publicData payload => L.Val payload
  | .privateInput _ payload => L.Val payload
  | .binding _ payload => PublicationResult (L.Val payload)
  | .publication payload => PublicationResult (L.Val payload)

/-- The semantic action selected at an event producing this field kind. -/
abbrev Action : EventField Player L → Type
  | .publicData _ => PUnit
  | .privateInput _ _ => PEmpty
  | .binding _ payload => Option (PublicationResult (L.Val payload))
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

omit R in theorem get?_preserved {Field : Type} {layout : Field → EventField Player L}
    {kind : EventField Player L} (ref : FieldRef layout kind)
    (before after : Store layout)
    (preserved : ∀ field value, before field = some value → after field = some value)
    (value : kind.Value) (stored : ref.get? before = some value) :
    ref.get? after = some value := by
  cases ref with
  | mk field layoutEq =>
      cases layoutEq
      exact preserved field value stored

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
    (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {name payload}, HasVar schema name payload → PublicRead (R := R) layout payload)
    (store : Store layout) :=
  PartialEnvironment.collect? (fun name _ => name ∈ deps) schema
    (fun ref _ => (reads ref).get? store)

private theorem collectPublicReads_congr {Field : Type} {layout : Field → EventField Player L}
    (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {name payload}, HasVar schema name payload → PublicRead (R := R) layout payload)
    (left right : Store layout)
    (agree : ∀ {name payload} (ref : HasVar schema name payload), name ∈ deps →
      (reads ref).get? left = (reads ref).get? right) :
    collectPublicReads deps schema reads left = collectPublicReads deps schema reads right :=
  PartialEnvironment.congr _ schema _ _ agree

private theorem collectPublicReads_isSome {Field : Type} {layout : Field → EventField Player L}
    (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {name payload}, HasVar schema name payload → PublicRead (R := R) layout payload)
    (store : Store layout)
    (available : ∀ {name payload} (ref : HasVar schema name payload), name ∈ deps →
      (store (reads ref).field).isSome = true) :
    (collectPublicReads deps schema reads store).isSome = true :=
  (PartialEnvironment.isSome_iff _ schema _).mpr
    (fun ref read => PublicRead.get?_isSome (reads ref) store (available ref read))

private theorem collectPublicReads_eq_of_reads {Field : Type} {layout : Field → EventField Player L}
    (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {name payload}, HasVar schema name payload → PublicRead (R := R) layout payload)
    (store : Store layout) (env : Env L.Val schema)
    (agree : ∀ {name payload} (ref : HasVar schema name payload), name ∈ deps →
      (reads ref).get? store = some (env.get ref)) :
    ∃ get : ∀ {name payload}, HasVar schema name payload → name ∈ deps → L.Val payload,
      collectPublicReads deps schema reads store = some (fun {_ _} ref read => get ref read) ∧
        ∀ {name payload} (ref : HasVar schema name payload) (read : name ∈ deps),
          get ref read = env.get ref :=
  ⟨fun ref _ => env.get ref, PartialEnvironment.of_some _ schema _ _ agree,
    fun {_ _} _ _ => rfl⟩

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
    Option (PMF (L.Val payload)) :=
  (dist.evalLaw? store).map RationalLaw.denote

/-- An available retained law is a finite law. -/
theorem eval?_support_finite {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (dist : PublicDist (R := R) layout payload) (store : Store layout)
    {law : PMF (L.Val payload)} (evaluated : dist.eval? store = some law) :
    law.support.Finite := by
  obtain ⟨table, _, rfl⟩ := Option.map_eq_some_iff.mp evaluated
  exact table.denote_support_finite

theorem evalLaw?_isSome {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (dist : PublicDist (R := R) layout payload) (store : Store layout)
    (available : ∀ field ∈ dist.readFields, (store field).isSome = true) :
    (dist.evalLaw? store).isSome = true := by
  unfold evalLaw?
  rw [Option.isSome_map]
  exact collectPublicReads_isSome (L.distDeps dist.code) dist.schema dist.reads store
    (fun ref member => available _ (dist.reads_mem ref member))

/-- Only the typed reads used by the distribution can influence its law.
Extra fields in a conservative footprint are immaterial. -/
theorem evalLaw?_congr_reads {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (dist : PublicDist (R := R) layout payload) (left right : Store layout)
    (agree : ∀ {name input} (ref : HasVar dist.schema name input),
      name ∈ L.distDeps dist.code → (dist.reads ref).get? left = (dist.reads ref).get? right) :
    dist.evalLaw? left = dist.evalLaw? right := by
  unfold evalLaw?
  rw [collectPublicReads_congr (R := R) (L.distDeps dist.code)
    dist.schema dist.reads left right agree]

theorem evalLaw?_congr {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (dist : PublicDist (R := R) layout payload) (left right : Store layout)
    (agree : Store.AgreeOn left right dist.readFields) :
    dist.evalLaw? left = dist.evalLaw? right := by
  exact dist.evalLaw?_congr_reads left right fun ref member =>
    PublicRead.get?_congr (dist.reads ref) left right (agree _ (dist.reads_mem ref member))

/-- Semantic public sampling has the same locality as its exact rational law. -/
theorem eval?_congr_reads {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (dist : PublicDist (R := R) layout payload) (left right : Store layout)
    (agree : ∀ {name input} (ref : HasVar dist.schema name input),
      name ∈ L.distDeps dist.code → (dist.reads ref).get? left = (dist.reads ref).get? right) :
    dist.eval? left = dist.eval? right := by
  unfold eval?
  rw [dist.evalLaw?_congr_reads left right agree]

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
    (proposal : PublicationResult (L.Val currentPayload))
    (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {name input}, HasVar schema name input → name ∈ deps →
      GuardOperand layout currentPayload input) :=
  PartialEnvironment.collect? (fun name _ => name ∈ deps) schema
    (fun ref read => (reads ref read).get? store proposal)

omit R in
private theorem collectReads_congr {Field : Type} {layout : Field → EventField Player L}
    {currentPayload : L.Ty} (left right : Store layout)
    (proposal : PublicationResult (L.Val currentPayload))
    (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {name input}, HasVar schema name input → name ∈ deps →
      GuardOperand layout currentPayload input)
    (agree : ∀ {name input} (ref : HasVar schema name input) (read : name ∈ deps) field,
      (reads ref read).field? = some field → left field = right field) :
    collectReads left proposal deps schema reads = collectReads right proposal deps schema reads :=
  PartialEnvironment.congr _ schema _ _ (fun ref read =>
    GuardOperand.get?_congr (reads ref read) left right proposal
      (fun field found => agree ref read field found))

omit R in
private theorem collectReads_isSome {Field : Type} {layout : Field → EventField Player L}
    {currentPayload : L.Ty} (store : Store layout)
    (proposal : PublicationResult (L.Val currentPayload))
    (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {name input}, HasVar schema name input → name ∈ deps →
      GuardOperand layout currentPayload input)
    (available : ∀ {name input} (ref : HasVar schema name input) (read : name ∈ deps) field,
      (reads ref read).field? = some field → (store field).isSome = true) :
    (collectReads store proposal deps schema reads).isSome = true :=
  (PartialEnvironment.isSome_iff _ schema _).mpr (fun ref read =>
    GuardOperand.get?_isSome (reads ref read) store proposal
      (fun field found => available ref read field found))

omit R in
private theorem collectReads_eq_of_reads {Field : Type} {layout : Field → EventField Player L}
    {currentPayload : L.Ty} (store : Store layout)
    (proposal : PublicationResult (L.Val currentPayload))
    (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {name input}, HasVar schema name input → name ∈ deps →
      GuardOperand layout currentPayload input)
    (env : ∀ {name input}, HasVar schema name input → name ∈ deps →
      PublicationResult (L.Val input))
    (agree : ∀ {name input} (ref : HasVar schema name input) (read : name ∈ deps),
      (reads ref read).get? store proposal = some (env ref read)) :
    collectReads store proposal deps schema reads =
      (some env : Option (∀ {name input}, HasVar schema name input → name ∈ deps →
        PublicationResult (L.Val input))) :=
  PartialEnvironment.of_some _ schema _ _ agree

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
      EventField.Action output → Store layout → Option (PMF output.Value)
  | _, .bind _ _, action, _ => some (PMF.pure (action.getD .failure))
  | _, .resolve _ _ binding checks, disclose, store =>
      (resolveOutput? binding checks disclose store).map PMF.pure
  | _, .sample _ law, _, store => law.eval? store

/-- Every node evaluation is a finite law: strategic nodes produce point laws
and chance nodes denote exact rational tables. -/
theorem eval?_support_finite {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L}
    (code : EventCode layout output) (action : EventField.Action output)
    (store : Store layout) {law : PMF output.Value}
    (evaluated : code.eval? action store = some law) :
    law.support.Finite := by
  cases code with
  | bind =>
      cases evaluated
      simp
  | resolve =>
      obtain ⟨value, _, rfl⟩ := Option.map_eq_some_iff.mp evaluated
      simp
  | sample _ dist => exact dist.eval?_support_finite store evaluated

/-- The general evaluator embeds the unique deterministic resolve output as a
point law.  Public-message handlers use `resolveOutput?` directly and prove
their transition law against `eval?` through this equation. -/
@[simp] theorem resolve_eval? {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {owner : Player} {payload : L.Ty}
    (binding : FieldRef layout (.binding owner payload))
    (checks : List (GuardCheck layout payload)) (disclose : Bool)
    (store : Store layout) :
    (EventCode.resolve owner payload binding checks).eval? disclose store =
      (resolveOutput? binding checks disclose store).map PMF.pure := rfl

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
    ∃ value, code.eval? action store = some (PMF.pure value) := by
  cases code with
  | bind who payload => exact ⟨action.getD .failure, rfl⟩
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
      exact congrArg (Option.map PMF.pure)
        (resolveOutput?_congr binding checks action left right agree)
  | sample payload law => exact law.eval?_congr left right agree

end EventCode

end Vegas.EventGraph

namespace Vegas.EventGraph.EventCode

open GameTheory.Math.Probability

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {Field : Type} [DecidableEq Field] {layout : Field → EventField Player L}
  {output : EventField Player L}

/-- The automatic action of a strategic node whose owner has already defaulted. -/
def failureAction (code : EventCode layout output) (owner : Player)
    (owned : code.actor = some owner) : code.Action := by
  cases code with
  | bind => exact none
  | resolve => exact false
  | sample => simp [actor] at owned

/-- The result of this node constitutes an owned public failure. An accepted
unopenable binding is distinct from an omitted binding. -/
def causesDefault : {output : EventField Player L} →
    (code : EventCode layout output) → code.Action → output.Value → Bool
  | _, .bind _ _, action, _ => action.isNone
  | _, .resolve _ _ _ _, _, value => value.isFailure
  | _, .sample _ _, _, _ => false

/-- A candidate default event before excluding automatic completions. -/
def defaultEvent (code : EventCode layout output) (action : code.Action)
    (value : output.Value) : Option Player :=
  if code.causesDefault action value then code.actor else none

@[simp] theorem bind_eval? (owner : Player) (payload : L.Ty)
    (action : Option (PublicationResult (L.Val payload))) (store : Store layout) :
    (EventCode.bind owner payload).eval? action store =
      some (PMF.pure (action.getD .failure)) := rfl

@[simp] theorem bind_causesDefault_none (owner : Player) (payload : L.Ty)
    (value : PublicationResult (L.Val payload)) :
    (EventCode.bind (layout := layout) owner payload).causesDefault none value = true := rfl

@[simp] theorem bind_causesDefault_some (owner : Player) (payload : L.Ty)
    (action value : PublicationResult (L.Val payload)) :
    (EventCode.bind (layout := layout) owner payload).causesDefault (some action) value = false :=
  rfl

/-- The canonical automatic action evaluates to a failure result. -/
theorem failureAction_eval? (code : EventCode layout output) (owner : Player)
    (owned : code.actor = some owner) (store : Store layout)
    (available : ∀ field ∈ code.readFields, (store field).isSome = true) :
    ∃ value, code.eval? (code.failureAction owner owned) store = some (PMF.pure value) ∧
      code.causesDefault (code.failureAction owner owned) value = true := by
  cases code with
  | bind who payload => exact ⟨.failure, rfl, rfl⟩
  | resolve who payload binding checks =>
      refine ⟨.failure, ?_, rfl⟩
      simp only [failureAction, eval?,
        resolveOutput?_false_eq_failure binding checks store available, Option.map_some]
  | sample => simp [actor] at owned

end Vegas.EventGraph.EventCode

namespace Vegas.EventGraph.EventCode

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Field : Type} [DecidableEq Field] {layout : Field → EventField Player L}
  {output : EventField Player L}

/-- The requested action, replaced by mechanical failure for a defaulted owner. -/
def effectiveAction (code : EventCode layout output) (defaulted : Finset Player)
    (requested : code.Action) : code.Action :=
  match owned : code.actor with
  | some owner => if owner ∈ defaulted then code.failureAction owner owned else requested
  | none => requested

/-- Only an active strategic node records an actual decision. -/
def actualDecision (code : EventCode layout output) (defaulted : Finset Player)
    (requested : code.Action) : Option code.Action :=
  match code.actor with
  | some owner => if owner ∈ defaulted then none else some requested
  | none => none

theorem actualDecision_effectiveAction (code : EventCode layout output)
    (defaulted : Finset Player) (requested : code.Action) :
    code.actualDecision defaulted (code.effectiveAction defaulted requested) =
      code.actualDecision defaulted requested := by
  cases code with
  | bind owner payload =>
      by_cases inactive : owner ∈ defaulted
      · simp [actualDecision, actor, inactive]
      · simp [actualDecision, effectiveAction, actor, inactive]
  | resolve owner payload binding checks =>
      by_cases inactive : owner ∈ defaulted
      · simp [actualDecision, actor, inactive]
      · simp [actualDecision, effectiveAction, actor, inactive]
  | sample => rfl

theorem effectiveAction_of_defaulted (code : EventCode layout output)
    (defaulted : Finset Player) (owner : Player) (owned : code.actor = some owner)
    (inactive : owner ∈ defaulted) (requested : code.Action) :
    code.effectiveAction defaulted requested = code.failureAction owner owned := by
  cases code with
  | bind who payload =>
      have same : who = owner := Option.some.inj owned
      subst who
      simp [effectiveAction, actor, failureAction, inactive]
  | resolve who payload binding checks =>
      have same : who = owner := Option.some.inj owned
      subst who
      simp [effectiveAction, actor, failureAction, inactive]
  | sample => simp [actor] at owned

theorem actualDecision_of_defaulted (code : EventCode layout output)
    (defaulted : Finset Player) (owner : Player) (owned : code.actor = some owner)
    (inactive : owner ∈ defaulted) (requested : code.Action) :
    code.actualDecision defaulted requested = none := by
  simp [actualDecision, owned, inactive]

end Vegas.EventGraph.EventCode

namespace Vegas.EventGraph.EventCode

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {Field : Type} [DecidableEq Field] {layout : Field → EventField Player L}
  {left right : EventField Player L}

/-- Identifying typed node code transports its automatic action along the same equality. -/
theorem failureAction_eq_cast (same : left = right) (original : EventCode layout left)
    (code : EventCode layout right)
    (codeEq : cast (congrArg (EventCode layout) same) original = code)
    (owner : Player) (ownedOriginal : original.actor = some owner)
    (ownedCode : code.actor = some owner) :
    original.failureAction owner ownedOriginal =
      cast (congrArg EventField.Action same.symm) (code.failureAction owner ownedCode) := by
  cases same
  subst code
  rfl

end Vegas.EventGraph.EventCode
