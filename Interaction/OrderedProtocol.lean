/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.CommitmentCandidates
import Interaction.MessageApplication

/-! # Publicly ordered commitment protocols

Runtime-general protocol semantics hosted by the existing `MessageApplication`
runner. The visible program counter gates application acceptance, never message
submission, delivery, or replay. Code, visible execution data, private
materialized data, and opaque candidate meanings are distinct components.

Guard verification, chance, and private initialization are explicit ideal local
capabilities. This module states no source correspondence or incentive theorem.
-/

namespace Interaction.OrderedProtocol

open GameTheory.Math.Probability

universe u

abbrev Field := Nat

inductive FieldOrigin where
  | initial (index : Nat)
  | operation (index : Nat)
  deriving DecidableEq

inductive DisclosureMode where
  | manual
  | recovery
  deriving DecidableEq

inductive BindingMode where
  | opaque
  | certifiedRecoverable
  deriving DecidableEq

inductive SiteKind (Principal : Type u) where
  | chance
  | commit (owner : Principal) (mode : BindingMode)
  | reveal (origin : FieldOrigin) (mode : DisclosureMode)
  deriving DecidableEq

/-- `resolution?` is an explicit protocol alternative for a failed or expired
commit/reveal site. Chance and automatic disclosure never consult it. -/
structure Site (Principal : Type u) (Tag : Type u) (Value : Type u) where
  kind : SiteKind Principal
  tag : Tag
  reads : List Field
  resolution? : Option Value
  deadline : Nat

structure InitialMeta (Principal : Type u) (Tag : Type u) where
  owner : Option Principal
  tag : Tag
  automaticPublic : Bool

/-- Immutable visible code. Initial and operation fields occupy disjoint numeric
ranges; `operationField` gives the field produced at a program counter. -/
structure Code (Principal : Type u) (Tag : Type u) (Value : Type u) where
  initial : List (InitialMeta Principal Tag)
  sites : List (Site Principal Tag Value)

namespace Code

variable {Principal Tag Value : Type u}

def operationField (code : Code Principal Tag Value) (pc : Nat) : Field :=
  code.initial.length + pc

def origin? (code : Code Principal Tag Value) (field : Field) : Option FieldOrigin :=
  if field < code.initial.length then some (.initial field)
  else if field - code.initial.length < code.sites.length then
    some (.operation (field - code.initial.length))
  else none

end Code

/-- Separate ideal setup data, checked against visible initial metadata by
`Runtime.initial?`. -/
structure InitialInput (Tag : Type u) (Value : Type u) where
  tag : Tag
  value : Value

/-- A finite heterogeneous store represented without any source-specific type. -/
abbrev Store (Value : Type u) := List (Field × Value)

namespace Store

variable {Value : Type u}

def lookup (store : Store Value) (field : Field) : Option Value :=
  store.findSome? fun entry => if entry.1 = field then some entry.2 else none

def write (store : Store Value) (field : Field) (value : Value) : Store Value :=
  if (store.lookup field).isSome then store else store ++ [(field, value)]

/-- Replace an effective value after explicit resolution. -/
def assign (store : Store Value) (field : Field) (value : Value) : Store Value :=
  (store.filter fun entry => entry.1 != field) ++ [(field, value)]

def snapshot (store : Store Value) (reads : List Field) : Option (Store Value) :=
  reads.attach.mapM fun entry => (store.lookup entry.1).map fun value => (entry.1, value)

end Store

inductive Validation where
  | accept
  | reject
  | unavailable
  deriving DecidableEq

/-- Local ideal capabilities receive only the declared snapshot for the current
site. Missing predecessor materialization is handled before invocation. -/
structure Capabilities (Tag : Type u) (Value : Type u) where
  hasTag : Tag → Value → Bool
  validate : Nat → Store Value → Store Value → Value → Validation
  sample : Nat → Tag → Store Value → Option (FinDist Value)
  sample_typed : ∀ site tag snapshot law value,
    sample site tag snapshot = some law → value ∈ law.support → hasTag tag value = true

abbrev Handle (Principal : Type u) := CommitmentHandle Principal Nat

/-- Raw and malformed traffic remains in the native strategy space. -/
inductive Payload (Principal : Type u) (Value : Type u) where
  | commitment (site : Nat) (handle : Handle Principal)
  | opening (site : Nat) (handle : Handle Principal) (raw : Value)
  | malformed (raw : Value)
  deriving DecidableEq

inductive PrivateCommand (Value : Type u) where
  | prepare (candidate : Nat) (value : Value)

inductive EnvironmentCommand (Value : Type u) where
  | tick (marker : Option Value)
  deriving DecidableEq

inductive Failure where
  | rejected
  | unavailable
  | expired
  deriving DecidableEq

inductive Event (Principal : Type u) (Value : Type u) where
  | initialDisclosure (field : Field) (value : Value)
  | accepted (site : Nat) (handle : Handle Principal)
  | resolved (site : Nat) (value : Value)
  | resolution (site : Nat) (failure : Failure) (value : Value)
  | sampled (site : Nat) (value : Value)
  | disclosed (site : Nat) (origin : FieldOrigin) (value : Value)
  deriving DecidableEq

structure PublicState (Principal : Type u) (Value : Type u) where
  pc : Nat := 0
  clock : Nat := 0
  enteredAt : Nat := 0
  store : Store Value := []
  events : List (Event Principal Value) := []
  deriving DecidableEq

/-- Captured declared-read context at the first accepted commitment for a site. -/
abbrev Snapshots (Value : Type u) := List (Nat × Store Value)

structure State (Principal : Type u) (Value : Type u) where
  visible : PublicState Principal Value
  bound : Store Value
  effective : Store Value
  snapshots : Snapshots Value
  candidates : CommitmentCandidates Principal Nat Value

structure PlayerView (Principal : Type u) (Tag : Type u) (Value : Type u) where
  visible : PublicState Principal Value
  initial : List (Field × Tag × Value)
  owned : Store Value
  prepared : Nat → CommitmentCandidate Value

abbrev EnvironmentView (Principal : Type u) (Value : Type u) :=
  PublicState Principal Value

structure Runtime (Principal : Type u) (Tag : Type u) (Value : Type u) where
  code : Code Principal Tag Value
  capabilities : Capabilities Tag Value

namespace Runtime

variable {Principal : Type u} {Tag : Type u} {Value : Type u}
variable [DecidableEq Principal] [DecidableEq Tag] [DecidableEq Value]

def accepted? (events : List (Event Principal Value)) (site : Nat) :
    Option (Handle Principal) :=
  events.findSome? fun
    | .accepted visited handle => if visited = site then some handle else none
    | _ => none

def snapshot? (snapshots : Snapshots Value) (site : Nat) : Option (Store Value) :=
  snapshots.findSome? fun entry => if entry.1 = site then some entry.2 else none

def current? (runtime : Runtime Principal Tag Value) (state : State Principal Value) :=
  runtime.code.sites[state.visible.pc]?

def initial? (runtime : Runtime Principal Tag Value) (inputs : List (InitialInput Tag Value)) :
    Option (State Principal Value) := do
  if inputs.length != runtime.code.initial.length then none else
  let indexed := inputs.zipIdx
  if !indexed.all (fun (input, index) =>
      runtime.code.initial[index]?.any (fun info =>
        info.tag = input.tag && runtime.capabilities.hasTag info.tag input.value)) then none else
  let initialStore := indexed.map fun (input, index) => (index, input.value)
  let disclosures := indexed.filterMap fun (input, index) =>
    runtime.code.initial[index]?.bind (fun info =>
      if info.automaticPublic then some (index, input.value) else none)
  some {
    visible := {
      store := disclosures
      events := disclosures.map fun entry => .initialDisclosure entry.1 entry.2 }
    bound := initialStore
    effective := initialStore
    snapshots := []
    candidates := .empty }

def advance (runtime : Runtime Principal Tag Value) (state : State Principal Value)
    (value : Value) (event : Event Principal Value) : State Principal Value :=
  let field := runtime.code.operationField state.visible.pc
  { state with
    visible := { state.visible with
      pc := state.visible.pc + 1
      enteredAt := state.visible.clock
      store := state.visible.store.write field value
      events := state.visible.events ++ [event] }
    bound := state.bound.write field value
    effective := state.effective.assign field value }

def resolve (runtime : Runtime Principal Tag Value) (state : State Principal Value)
    (site : Site Principal Tag Value) (failure : Failure) : Option (State Principal Value) := do
  let value ← site.resolution?
  if runtime.capabilities.hasTag site.tag value then
    some (runtime.advance state value (.resolution state.visible.pc failure value))
  else none

def privateStep (_runtime : Runtime Principal Tag Value) (state : State Principal Value)
    (who : Principal) : PrivateCommand Value → State Principal Value
  | .prepare candidate value =>
      { state with candidates := state.candidates.prepare who candidate value }

/-- Commitment inclusion captures only the site's declared materialized reads.
An unavailable snapshot does not prevent binding, but later validation reports
unavailability and remains retryable until explicit resolution or expiry. -/
def acceptCommitment (runtime : Runtime Principal Tag Value) (state : State Principal Value)
    (site : Site Principal Tag Value) (visited : Nat)
    (handle : Handle Principal) : State Principal Value :=
  let snapshots := match state.bound.snapshot site.reads with
    | none => state.snapshots
    | some snapshot => state.snapshots ++ [(visited, snapshot)]
  let bound := match state.candidates.lookup handle with
    | .openable value => state.bound.write (runtime.code.operationField visited) value
    | .fresh | .unopenable => state.bound
  let effective := match state.candidates.lookup handle with
    | .openable value => state.effective.assign (runtime.code.operationField visited) value
    | .fresh | .unopenable => state.effective
  { state with
    visible := { state.visible with
      pc := state.visible.pc + 1
      enteredAt := state.visible.clock
      events := state.visible.events ++ [.accepted visited handle] }
    snapshots
    bound
    effective
    candidates := state.candidates.accept handle }

/-- Only current-site packets can affect application state. Wrong-type,
malformed, unavailable, unopenable, or guard-rejected openings are rejected and
remain retryable; they never select a source value or force resolution. -/
def handle (runtime : Runtime Principal Tag Value) (state : State Principal Value)
    (message : Message Principal (Payload Principal Value)) : Option (State Principal Value) := do
  let site ← runtime.current? state
  match site.kind, message.payload with
  | .commit owner mode, .commitment visited handle =>
      if visited = state.visible.pc && message.sender = owner && handle.1 = owner &&
          (accepted? state.visible.events visited).isNone then
        match mode with
        | .opaque => some (runtime.acceptCommitment state site visited handle)
        | .certifiedRecoverable =>
            match state.candidates.lookup handle, state.bound.snapshot site.reads,
                state.effective.snapshot site.reads with
            | .openable value, some boundSnapshot, some effectiveSnapshot =>
                if runtime.capabilities.hasTag site.tag value then
                  match runtime.capabilities.validate visited boundSnapshot
                      effectiveSnapshot value with
                  | .accept => some (runtime.acceptCommitment state site visited handle)
                  | .reject | .unavailable => none
                else none
            | _, _, _ => none
      else none
  | .reveal (.operation source) _, .opening visited handle raw =>
      if visited = state.visible.pc && message.sender = handle.1 &&
          accepted? state.visible.events source = some handle &&
          state.candidates.verify handle raw && runtime.capabilities.hasTag site.tag raw then
        match snapshot? state.snapshots source with
        | some boundSnapshot =>
            match state.effective.snapshot site.reads with
            | some effectiveSnapshot =>
                match runtime.capabilities.validate source boundSnapshot effectiveSnapshot raw with
                | .accept => some (runtime.advance state raw (.resolved visited raw))
                | .reject | .unavailable => none
            | none => none
        | none => none
      else none
  | _, _ => none

def originField (runtime : Runtime Principal Tag Value) : FieldOrigin → Field
  | .initial index => index
  | .operation index => runtime.code.operationField index

/-- A ready chance site samples and publishes atomically. Missing typed reads
stutter. The capability's support certificate prevents retry-resampling after a
wrong-typed draw. -/
noncomputable def chanceStep (runtime : Runtime Principal Tag Value)
    (state : State Principal Value) (site : Site Principal Tag Value) :
    FinDist (State Principal Value) :=
  match state.effective.snapshot site.reads with
  | none => FinDist.pure state
  | some snapshot =>
      match runtime.capabilities.sample state.visible.pc site.tag snapshot with
      | none => FinDist.pure state
      | some law => law.map fun value =>
          runtime.advance state value (.sampled state.visible.pc value)

/-- Initial disclosure is a runtime-owned publication. This helper cannot
disclose an operation field or a candidate opening. -/
def initialDisclosureStep (runtime : Runtime Principal Tag Value)
    (state : State Principal Value) (site : Site Principal Tag Value) (index : Nat) :
    State Principal Value :=
  match state.effective.lookup index with
  | some value =>
      if runtime.capabilities.hasTag site.tag value then
        runtime.advance state value (.disclosed state.visible.pc (.initial index) value)
      else state
  | none => state

/-- Explicit ideal recovery of an accepted operation commitment. It publishes
only the candidate's immutable openable value and applies the same typed guard
check against both binding-time and current effective declared contexts. Any
missing or invalid prerequisite stutters; recovery never invents a fallback. -/
def recoveryStep (runtime : Runtime Principal Tag Value)
    (state : State Principal Value) (site : Site Principal Tag Value) (source : Nat) :
    State Principal Value :=
  match accepted? state.visible.events source with
  | none => state
  | some handle =>
      match state.candidates.lookup handle, snapshot? state.snapshots source,
          state.effective.snapshot site.reads with
      | .openable value, some boundSnapshot, some effectiveSnapshot =>
          if runtime.capabilities.hasTag site.tag value then
            match runtime.capabilities.validate source boundSnapshot effectiveSnapshot value with
            | .accept => runtime.advance state value
                (.disclosed state.visible.pc (.operation source) value)
            | .reject | .unavailable => state
          else state
      | _, _, _ => state

noncomputable def environmentStep (runtime : Runtime Principal Tag Value)
    (state : State Principal Value) : EnvironmentCommand Value → FinDist (State Principal Value)
  | .tick _ =>
      let ticked := { state with visible :=
        { state.visible with clock := state.visible.clock + 1 } }
      match runtime.current? ticked with
      | none => FinDist.pure ticked
      | some site =>
          match site.kind with
          | .chance => runtime.chanceStep ticked site
          | .reveal (.initial index) _ =>
              FinDist.pure (runtime.initialDisclosureStep ticked site index)
          | .reveal (.operation source) .recovery =>
              if site.deadline ≤ ticked.visible.clock - ticked.visible.enteredAt then
                FinDist.pure (runtime.recoveryStep ticked site source)
              else FinDist.pure ticked
          | .commit _ _ | .reveal (.operation _) .manual =>
              if site.deadline ≤ ticked.visible.clock - ticked.visible.enteredAt then
                match runtime.resolve ticked site .expired with
                | some next => FinDist.pure next
                | none => FinDist.pure ticked
              else FinDist.pure ticked

def fieldOwner? (runtime : Runtime Principal Tag Value) (field : Field) : Option Principal :=
  match runtime.code.origin? field with
  | some (.initial index) => runtime.code.initial[index]?.bind (·.owner)
  | some (.operation index) =>
      runtime.code.sites[index]?.bind fun site => match site.kind with
        | .commit owner _ => some owner
        | _ => none
  | none => none

def observePlayer (runtime : Runtime Principal Tag Value) (state : State Principal Value)
    (who : Principal) : PlayerView Principal Tag Value :=
  { visible := state.visible
    initial := state.bound.filterMap fun entry =>
      match runtime.code.origin? entry.1 with
      | some (.initial index) => runtime.code.initial[index]?.bind (fun info =>
          if info.owner = some who then some (entry.1, info.tag, entry.2) else none)
      | _ => none
    owned := state.bound.filter fun entry => runtime.fieldOwner? entry.1 = some who
    prepared := fun candidate => state.candidates.lookup (who, candidate) }

noncomputable def application (runtime : Runtime Principal Tag Value) :
    MessageApplication Principal where
  Application := State Principal Value
  Payload := Payload Principal Value
  PrivateCommand := PrivateCommand Value
  EnvironmentCommand := EnvironmentCommand Value
  PlayerView := PlayerView Principal Tag Value
  EnvironmentView := EnvironmentView Principal Value
  privateStep := runtime.privateStep
  environmentStep := runtime.environmentStep
  handle := runtime.handle
  observePlayer := runtime.observePlayer
  observeEnvironment := (·.visible)

omit [DecidableEq Tag] [DecidableEq Value] in
/-- Candidate preparation does not alter public state. -/
@[simp] theorem privateStep_public (runtime : Runtime Principal Tag Value)
    (state : State Principal Value) (who : Principal) (command : PrivateCommand Value) :
    (runtime.privateStep state who command).visible = state.visible := by
  cases command
  rfl

omit [DecidableEq Tag] in
/-- Malformed traffic is rejected by application inclusion. -/
theorem handle_malformed (runtime : Runtime Principal Tag Value)
    (state : State Principal Value) (sender : Principal) (raw : Value) :
    runtime.handle state ⟨(sender, 0), .malformed raw⟩ = none := by
  simp [handle]

omit [DecidableEq Tag] in
/-- Environment observation contains exactly public protocol data; neither
setup values, bound values, snapshots, nor candidate meanings occur in it. -/
theorem observeEnvironment_eq (runtime : Runtime Principal Tag Value)
    (state : State Principal Value) :
    (runtime.application.observeEnvironment state) = state.visible := rfl

omit [DecidableEq Tag] [DecidableEq Value] in
/-- Private candidate preparation changes neither the public nor effective
protocol stores. -/
theorem privateStep_data (runtime : Runtime Principal Tag Value)
    (state : State Principal Value) (who : Principal) (command : PrivateCommand Value) :
    (runtime.privateStep state who command).visible = state.visible ∧
      (runtime.privateStep state who command).bound = state.bound ∧
      (runtime.privateStep state who command).effective = state.effective := by
  cases command
  exact ⟨rfl, rfl, rfl⟩

omit [DecidableEq Tag] [DecidableEq Value] in
/-- Preparing arbitrary later raw values cannot change a candidate whose
meaning is already fixed, including an accepted unopenable candidate. -/
theorem privateStep_lookup_of_fixed (runtime : Runtime Principal Tag Value)
    (state : State Principal Value) (who owner : Principal) (candidate queried : Nat)
    (value : Value)
    (hfixed : state.candidates.lookup (owner, queried) ≠ .fresh) :
    (runtime.privateStep state who (.prepare candidate value)).candidates.lookup
        (owner, queried) = state.candidates.lookup (owner, queried) :=
  state.candidates.lookup_prepare_eq_of_not_fresh (owner, queried) who candidate value hfixed

omit [DecidableEq Principal] [DecidableEq Tag] [DecidableEq Value] in
/-- Exact local chance law once the declared effective snapshot and typed
kernel are available. The counter advance and publication occur inside the
single mapped transition, so the sampled result cannot be retried. -/
theorem chanceStep_of_snapshot (runtime : Runtime Principal Tag Value)
    (state : State Principal Value) (site : Site Principal Tag Value)
    (snapshot : Store Value) (law : FinDist Value)
    (hsnapshot : state.effective.snapshot site.reads = some snapshot)
    (hlaw : runtime.capabilities.sample state.visible.pc site.tag snapshot = some law) :
    runtime.chanceStep state site = law.map (fun value =>
      runtime.advance state value (.sampled state.visible.pc value)) := by
  simp [chanceStep, hsnapshot, hlaw]

omit [DecidableEq Principal] [DecidableEq Tag] [DecidableEq Value] in
/-- Unavailable declared reads perform no draw and leave the state unchanged. -/
theorem chanceStep_unavailable (runtime : Runtime Principal Tag Value)
    (state : State Principal Value) (site : Site Principal Tag Value)
    (hsnapshot : state.effective.snapshot site.reads = none) :
    runtime.chanceStep state site = FinDist.pure state := by
  simp [chanceStep, hsnapshot]

omit [DecidableEq Principal] [DecidableEq Tag] [DecidableEq Value] in
/-- Every supported result of an available chance transition has advanced past
that site. A second tick therefore cannot invoke the same site's kernel. -/
theorem chanceStep_pc (runtime : Runtime Principal Tag Value)
    (state next : State Principal Value) (site : Site Principal Tag Value)
    (snapshot : Store Value) (law : FinDist Value)
    (hsnapshot : state.effective.snapshot site.reads = some snapshot)
    (hlaw : runtime.capabilities.sample state.visible.pc site.tag snapshot = some law)
    (hnext : next ∈ (runtime.chanceStep state site).support) :
    next.visible.pc = state.visible.pc + 1 := by
  rw [runtime.chanceStep_of_snapshot state site snapshot law hsnapshot hlaw,
    FinDist.support_map] at hnext
  obtain ⟨value, _hvalue, rfl⟩ := hnext
  rfl

omit [DecidableEq Principal] [DecidableEq Tag] [DecidableEq Value] in
/-- A ready recovery publishes the immutable accepted candidate value, never a
replacement. The current effective snapshot is checked separately from the
captured binding snapshot. -/
theorem recoveryStep_of_openable (runtime : Runtime Principal Tag Value)
    (state : State Principal Value) (site : Site Principal Tag Value)
    (source : Nat) (handle : Handle Principal) (value : Value)
    (boundSnapshot effectiveSnapshot : Store Value)
    (haccepted : accepted? state.visible.events source = some handle)
    (hvalue : state.candidates.lookup handle = .openable value)
    (hbound : snapshot? state.snapshots source = some boundSnapshot)
    (heffective : state.effective.snapshot site.reads = some effectiveSnapshot)
    (htag : runtime.capabilities.hasTag site.tag value = true)
    (hguard : runtime.capabilities.validate source boundSnapshot effectiveSnapshot value =
      .accept) :
    runtime.recoveryStep state site source = runtime.advance state value
      (.disclosed state.visible.pc (.operation source) value) := by
  simp [recoveryStep, haccepted, hvalue, hbound, heffective, htag, hguard]

end Runtime

end Interaction.OrderedProtocol
