/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedExpiry

/-! # Successful activation-relative expiry resolution

These laws connect public operational checks to the actual windowed handler.
They assume a consistent active instruction and the ordinary readiness and
fallback-evaluation facts required by that instruction. They neither advance
the clock nor submit or include a message.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

omit [DecidableEq P] in
private theorem lookup_address_eq (image : ApplicationImage P L) (address : Nat)
    (instruction : ApplicationInstruction P L)
    (hlookup : image.lookup address = some instruction) :
    instruction.address = address := by
  have hfound := List.find?_some hlookup
  simpa only [beq_iff_eq] using hfound

omit [DecidableEq P] in
private theorem activeAddress_eq (runtime : WindowedApplication P L)
    (state : State P L) (activation : Activation Nat)
    (hstate : runtime.Consistent state) (hactive : state.active = some activation) :
    runtime.image.activeAddress? state.base.memory = some activation.key := by
  have hcurrent := hstate.1
  rw [hactive] at hcurrent
  exact hcurrent.symm

private theorem handle_of_underlying (runtime : WindowedApplication P L)
    (state : State P L) (activation : Activation Nat)
    (hactive : state.active = some activation)
    (hcurrent : runtime.image.activeAddress? state.base.memory = some activation.key)
    (message : Message P (ApplicationImage.Payload P L))
    (haddress : message.payload.address? = some activation.key)
    (next : ApplicationImage.State P L)
    (hnext : (runtime.atOrigin activation.since).handle state.base message = some next) :
    runtime.handle state message = some (runtime.advanceTo state next) := by
  have hretimed : (runtime.atOrigin activation.since).activeAddress? state.base.memory =
      some activation.key := by
    simpa only [atOrigin, ApplicationImage.activeAddress?_withDeadlines] using hcurrent
  have hordered := (runtime.atOrigin activation.since).ordered_handle_eq state.base message
    activation.key haddress hretimed
  rw [hnext] at hordered
  unfold handle
  rw [hactive]
  simp only [Option.bind_eq_bind, Option.bind_some, hcurrent, ↓reduceIte, hordered,
    Option.pure_def]

/-- A ready binding fallback whose public expression evaluates after the
strict activation-relative deadline succeeds through the actual windowed
handler and installs the public binding disposition. -/
theorem handle_expireBinding_after_window (runtime : WindowedApplication P L)
    (state : State P L) (activation : Activation Nat)
    (hstate : runtime.Consistent state) (hactive : state.active = some activation)
    (code : BindingCode P L)
    (hcode : runtime.image.lookup activation.key = some (.bind code))
    (timeout : PublicFallbackCode L code.ty) (htimeout : code.timeout = some timeout)
    (hunbound : state.base.memory.accepted code.sourceField = none)
    (hnotDone : state.base.memory.done code.node = false)
    (hrequires : code.requires.all state.base.memory.done = true)
    (hoverdue : activation.since + runtime.windowOf activation.key < state.base.memory.clock)
    (value : L.Val code.ty)
    (hvalue : timeout.value.evalStore? state.base.memory.store = some value)
    (id : MessageId P) :
    runtime.handle state ⟨id, .expireBinding activation.key⟩ =
      some (runtime.advanceTo state (state.base.defaultBind code ⟨code.ty, value⟩)) := by
  have haddress : code.node = activation.key := by
    exact lookup_address_eq runtime.image activation.key (.bind code) hcode
  let retimedTimeout : PublicFallbackCode L code.ty :=
    { timeout with deadline := activation.since + runtime.windowOf code.node }
  let retimedCode : BindingCode P L := { code with timeout := some retimedTimeout }
  have hlookup : (runtime.atOrigin activation.since).lookup activation.key =
      some (.bind retimedCode) := by
    simp [atOrigin, hcode, ApplicationInstruction.withDeadlines, htimeout, retimedCode,
      retimedTimeout]
  have hoverdue' : retimedTimeout.deadline < state.base.memory.clock := by
    change activation.since + runtime.windowOf code.node < state.base.memory.clock
    rwa [haddress]
  have hnext := (runtime.atOrigin activation.since).handle_expireBinding_accepts state.base
    activation.key retimedCode hlookup id retimedTimeout rfl hunbound hnotDone hrequires
    hoverdue' value hvalue
  have hcurrent := activeAddress_eq runtime state activation hstate hactive
  simpa only [retimedCode, retimedTimeout, ApplicationImage.State.defaultBind] using
    handle_of_underlying runtime state activation hactive hcurrent
      ⟨id, .expireBinding activation.key⟩ rfl
      (state.base.defaultBind retimedCode ⟨retimedCode.ty, value⟩) hnext

/-- A ready public-choice fallback with available public reads and a passing
guard succeeds through the actual windowed handler after its strict deadline. -/
theorem handle_expireChoice_after_window (runtime : WindowedApplication P L)
    (state : State P L) (activation : Activation Nat)
    (hstate : runtime.Consistent state) (hactive : state.active = some activation)
    (code : PublicChoiceCode P L)
    (hcode : runtime.image.lookup activation.key = some (.publicChoice code))
    (timeout : PublicFallbackCode L code.guard.ty) (htimeout : code.timeout = some timeout)
    (hready : code.endpoint.ready state.base.memory.done = true)
    (hoverdue : activation.since + runtime.windowOf activation.key < state.base.memory.clock)
    (reads : ReadEnv L timeout.value.reads)
    (hreads : ReadEnv.ofStoreExec? state.base.memory.store timeout.value.reads = some reads)
    (hvalid : code.guard.validate state.base.memory.store (timeout.value.eval reads) = true)
    (id : MessageId P) :
    runtime.handle state ⟨id, .expireChoice activation.key⟩ =
      some (runtime.advanceTo state (state.base.publish code (timeout.value.eval reads))) := by
  have haddress : code.endpoint.publicationNode = activation.key := by
    exact lookup_address_eq runtime.image activation.key (.publicChoice code) hcode
  let retimedTimeout : PublicFallbackCode L code.guard.ty :=
    { timeout with deadline := activation.since + runtime.windowOf code.endpoint.publicationNode }
  let retimedCode : PublicChoiceCode P L := { code with timeout := some retimedTimeout }
  have hlookup : (runtime.atOrigin activation.since).lookup activation.key =
      some (.publicChoice retimedCode) := by
    simp [atOrigin, hcode, ApplicationInstruction.withDeadlines, htimeout, retimedCode,
      retimedTimeout]
  have hoverdue' : retimedTimeout.deadline < state.base.memory.clock := by
    change activation.since + runtime.windowOf code.endpoint.publicationNode <
      state.base.memory.clock
    rwa [haddress]
  have hnext := (runtime.atOrigin activation.since).handle_expireChoice_accepts state.base
    activation.key retimedCode hlookup id retimedTimeout rfl hready hoverdue' reads hreads hvalid
  have hcurrent := activeAddress_eq runtime state activation hstate hactive
  simpa only [retimedCode, retimedTimeout, ApplicationImage.State.publish,
    ApplicationImage.Memory.publish] using
    handle_of_underlying runtime state activation hactive hcurrent
      ⟨id, .expireChoice activation.key⟩ rfl
      (state.base.publish retimedCode (retimedTimeout.value.eval reads)) hnext

/-- Either accepted binding disposition can be permissionlessly expired after
the strict activation-relative deadline. The ordinary conditional readiness
predicate still rejects absent or ill-typed dispositions. -/
theorem handle_conditionalExpire_after_window (runtime : WindowedApplication P L)
    (state : State P L) (activation : Activation Nat)
    (hstate : runtime.Consistent state) (hactive : state.active = some activation)
    (code : ConditionalCode P L)
    (hcode : runtime.image.lookup activation.key = some (.conditional code))
    (hready : code.endpoint.readyDisposition (code.binding? state.base.memory)
      state.base.memory.done = true)
    (hoverdue : activation.since + runtime.windowOf activation.key < state.base.memory.clock)
    (id : MessageId P) :
    runtime.handle state ⟨id, .conditional activation.key .expire⟩ =
      some (runtime.advanceTo state (state.base.publishConditional code none)) := by
  have haddress : code.endpoint.publicationNode = activation.key := by
    exact lookup_address_eq runtime.image activation.key (.conditional code) hcode
  let retimedEndpoint := { code.endpoint with
    deadline := activation.since + runtime.windowOf code.endpoint.publicationNode }
  let retimedCode : ConditionalCode P L := { code with endpoint := retimedEndpoint }
  have hlookup : (runtime.atOrigin activation.since).lookup activation.key =
      some (.conditional retimedCode) := by
    simp [atOrigin, hcode, ApplicationInstruction.withDeadlines, retimedCode, retimedEndpoint]
  have hoverdue' : retimedCode.endpoint.deadline < state.base.memory.clock := by
    change activation.since + runtime.windowOf code.endpoint.publicationNode <
      state.base.memory.clock
    rwa [haddress]
  have hready' : retimedCode.endpoint.readyDisposition
      (retimedCode.binding? state.base.memory) state.base.memory.done = true := hready
  have hresolve : retimedCode.endpoint.resolveDisposition? state.base.memory.clock
      (state.base.verify retimedCode) (retimedCode.binding? state.base.memory)
      state.base.memory.done (retimedCode.canOpen state.base.memory.store) ⟨id, .expire⟩ =
      some none := by
    apply (retimedCode.endpoint.resolveDisposition_expire state.base.memory.clock
      (state.base.verify retimedCode) (retimedCode.binding? state.base.memory)
      state.base.memory.done (retimedCode.canOpen state.base.memory.store) id).2
    exact ⟨hready', hoverdue'⟩
  have hnext := (runtime.atOrigin activation.since).handle_conditional state.base
    activation.key retimedCode hlookup id
    (.expire : ConditionalPublication.Payload P (TypedValue L))
    (.expire : ConditionalPublication.Payload P (L.Val retimedCode.secretTy)) rfl
  rw [hresolve, Option.map_some] at hnext
  have hcurrent := activeAddress_eq runtime state activation hstate hactive
  simpa only [retimedCode, retimedEndpoint, ApplicationImage.State.publishConditional] using
    handle_of_underlying runtime state activation hactive hcurrent
      ⟨id, .conditional activation.key .expire⟩ rfl
      (state.base.publishConditional retimedCode none) hnext

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.handle_expireBinding_after_window' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_expireBinding_after_window

/-- info: 'Vegas.WindowedApplication.handle_expireChoice_after_window' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_expireChoice_after_window

/-- info: 'Vegas.WindowedApplication.handle_conditionalExpire_after_window' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_conditionalExpire_after_window
