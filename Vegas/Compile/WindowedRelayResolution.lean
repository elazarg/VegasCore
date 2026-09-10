/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors.
-/

import Vegas.Compile.WindowedExpiryResolution
import Interaction.MessageApplicationImmediateService

/-! # Actual relay submission and expiry inclusion -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

omit [DecidableEq P] in
private theorem lookup_address_eq (image : ApplicationImage P L) (address : Nat)
    (instruction : ApplicationInstruction P L)
    (hlookup : image.lookup address = some instruction) :
    instruction.address = address := by
  have hfound := List.find?_some hlookup
  simpa only [beq_iff_eq] using hfound

/-- Wrap one principal's policy with permissionless wait relaying. -/
def relayAt (runtime : WindowedApplication P L)
    (players : P → runtime.application.PlayerPolicy) (who : P) :
    P → runtime.application.PlayerPolicy := fun principal =>
  if principal = who then runtime.relayWhenWaiting (players principal)
  else players principal

private theorem relay_include_accepts (runtime : WindowedApplication P L)
    (players : P → runtime.application.PlayerPolicy) (who : P)
    (payload : ApplicationImage.Payload P L)
    (execution : runtime.application.PolicyExecution)
    (next : WindowedApplication.State P L)
    (hbase : players who (execution.principalHistory who)
      (MessageApplication.State.observe runtime.application execution.native who) =
        FinDist.pure .wait)
    (hdue : runtime.dueExpiry?
      (MessageApplication.State.observe runtime.application execution.native who).application =
        some payload)
    (hfresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none)
    (hhandle : runtime.handle execution.native.application
      ⟨(who, execution.native.pool.nextSerial who), payload⟩ = some next) :
    (runtime.application.runPolicies (runtime.relayAt players who)
      (runtime.application.includeLatestFrom who) [.player who, .environment] execution).map
        (fun out => (out.native.application, out.native.pool.ledger, out.native.receipts)) =
      FinDist.pure (next,
        execution.native.pool.ledger ++
          [⟨(who, execution.native.pool.nextSerial who), payload⟩],
        execution.native.receipts ++
          [((who, execution.native.pool.nextSerial who), true)]) := by
  apply runtime.application.submit_include_accepts
  · simp only [relayAt, ↓reduceIte]
    exact runtime.relayWhenWaiting_pure_wait _ _ _ payload hbase hdue
  · exact hfresh
  · exact hhandle

omit [DecidableEq P] in
private theorem due_of_binding (runtime : WindowedApplication P L)
    (state : WindowedApplication.State P L) (activation : Activation Nat)
    (hstate : runtime.Consistent state) (hactive : state.active = some activation)
    (code : BindingCode P L)
    (hcode : runtime.image.lookup activation.key = some (.bind code))
    (timeout : PublicFallbackCode L code.ty) (htimeout : code.timeout = some timeout)
    (hoverdue : activation.since + runtime.windowOf activation.key < state.base.memory.clock) :
    runtime.dueExpiry? (state.base.memory, state.active) =
      some (.expireBinding activation.key) := by
  have haddress : code.node = activation.key :=
    lookup_address_eq runtime.image activation.key (.bind code) hcode
  have hcurrent : runtime.image.activeAddress? state.base.memory = some activation.key := by
    rw [← hstate.1, hactive]
    rfl
  unfold dueExpiry?
  rw [hactive]
  simp only [Option.bind_eq_bind, Option.bind_some, hcurrent, hoverdue, and_self,
    ↓reduceIte, hcode, ApplicationInstruction.expiryPayload?, htimeout, Option.isSome_some,
    haddress]

omit [DecidableEq P] in
private theorem due_of_publicChoice (runtime : WindowedApplication P L)
    (state : WindowedApplication.State P L) (activation : Activation Nat)
    (hstate : runtime.Consistent state) (hactive : state.active = some activation)
    (code : PublicChoiceCode P L)
    (hcode : runtime.image.lookup activation.key = some (.publicChoice code))
    (timeout : PublicFallbackCode L code.guard.ty) (htimeout : code.timeout = some timeout)
    (hoverdue : activation.since + runtime.windowOf activation.key < state.base.memory.clock) :
    runtime.dueExpiry? (state.base.memory, state.active) =
      some (.expireChoice activation.key) := by
  have haddress : code.endpoint.publicationNode = activation.key :=
    lookup_address_eq runtime.image activation.key (.publicChoice code) hcode
  have hcurrent : runtime.image.activeAddress? state.base.memory = some activation.key := by
    rw [← hstate.1, hactive]
    rfl
  unfold dueExpiry?
  rw [hactive]
  simp only [Option.bind_eq_bind, Option.bind_some, hcurrent, hoverdue, and_self,
    ↓reduceIte, hcode, ApplicationInstruction.expiryPayload?, htimeout, Option.isSome_some,
    haddress]

omit [DecidableEq P] in
private theorem due_of_conditional (runtime : WindowedApplication P L)
    (state : WindowedApplication.State P L) (activation : Activation Nat)
    (hstate : runtime.Consistent state) (hactive : state.active = some activation)
    (code : ConditionalCode P L)
    (hcode : runtime.image.lookup activation.key = some (.conditional code))
    (hoverdue : activation.since + runtime.windowOf activation.key < state.base.memory.clock) :
    runtime.dueExpiry? (state.base.memory, state.active) =
      some (.conditional activation.key .expire) := by
  have haddress : code.endpoint.publicationNode = activation.key :=
    lookup_address_eq runtime.image activation.key (.conditional code) hcode
  have hcurrent : runtime.image.activeAddress? state.base.memory = some activation.key := by
    rw [← hstate.1, hactive]
    rfl
  unfold dueExpiry?
  rw [hactive]
  simp only [Option.bind_eq_bind, Option.bind_some, hcurrent, hoverdue, and_self,
    ↓reduceIte, hcode, ApplicationInstruction.expiryPayload?, haddress]

/-- A waiting arbitrary principal authors and includes a ready binding expiry
through the shared policy runner. -/
theorem relay_expireBinding_accepts (runtime : WindowedApplication P L)
    (players : P → runtime.application.PlayerPolicy) (who : P)
    (execution : runtime.application.PolicyExecution) (activation : Activation Nat)
    (hstate : runtime.Consistent execution.native.application)
    (hactive : execution.native.application.active = some activation)
    (code : BindingCode P L)
    (hcode : runtime.image.lookup activation.key = some (.bind code))
    (timeout : PublicFallbackCode L code.ty) (htimeout : code.timeout = some timeout)
    (hunbound : execution.native.application.base.memory.accepted code.sourceField = none)
    (hnotDone : execution.native.application.base.memory.done code.node = false)
    (hrequires : code.requires.all execution.native.application.base.memory.done = true)
    (hoverdue : activation.since + runtime.windowOf activation.key <
      execution.native.application.base.memory.clock)
    (value : L.Val code.ty)
    (hvalue : timeout.value.evalStore?
      execution.native.application.base.memory.store = some value)
    (hbase : players who (execution.principalHistory who)
      (MessageApplication.State.observe runtime.application execution.native who) =
        FinDist.pure .wait)
    (hfresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none) :
    (runtime.application.runPolicies (runtime.relayAt players who)
      (runtime.application.includeLatestFrom who) [.player who, .environment] execution).map
        (fun out => (out.native.application, out.native.pool.ledger, out.native.receipts)) =
      FinDist.pure (runtime.advanceTo execution.native.application
        (execution.native.application.base.defaultBind code ⟨code.ty, value⟩),
        execution.native.pool.ledger ++
          [⟨(who, execution.native.pool.nextSerial who), .expireBinding activation.key⟩],
        execution.native.receipts ++
          [((who, execution.native.pool.nextSerial who), true)]) := by
  apply runtime.relay_include_accepts players who (.expireBinding activation.key) execution
  · exact hbase
  · exact due_of_binding runtime execution.native.application activation hstate hactive
      code hcode timeout htimeout hoverdue
  · exact hfresh
  · exact runtime.handle_expireBinding_after_window execution.native.application activation
      hstate hactive code hcode timeout htimeout hunbound hnotDone hrequires hoverdue value hvalue _

/-- A waiting arbitrary principal authors and includes a ready public-choice
expiry through the shared policy runner. -/
theorem relay_expireChoice_accepts (runtime : WindowedApplication P L)
    (players : P → runtime.application.PlayerPolicy) (who : P)
    (execution : runtime.application.PolicyExecution) (activation : Activation Nat)
    (hstate : runtime.Consistent execution.native.application)
    (hactive : execution.native.application.active = some activation)
    (code : PublicChoiceCode P L)
    (hcode : runtime.image.lookup activation.key = some (.publicChoice code))
    (timeout : PublicFallbackCode L code.guard.ty) (htimeout : code.timeout = some timeout)
    (hready : code.endpoint.ready execution.native.application.base.memory.done = true)
    (hoverdue : activation.since + runtime.windowOf activation.key <
      execution.native.application.base.memory.clock)
    (reads : ReadEnv L timeout.value.reads)
    (hreads : ReadEnv.ofStoreExec? execution.native.application.base.memory.store
      timeout.value.reads = some reads)
    (hvalid : code.guard.validate execution.native.application.base.memory.store
      (timeout.value.eval reads) = true)
    (hbase : players who (execution.principalHistory who)
      (MessageApplication.State.observe runtime.application execution.native who) =
        FinDist.pure .wait)
    (hfresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none) :
    (runtime.application.runPolicies (runtime.relayAt players who)
      (runtime.application.includeLatestFrom who) [.player who, .environment] execution).map
        (fun out => (out.native.application, out.native.pool.ledger, out.native.receipts)) =
      FinDist.pure (runtime.advanceTo execution.native.application
        (execution.native.application.base.publish code (timeout.value.eval reads)),
        execution.native.pool.ledger ++
          [⟨(who, execution.native.pool.nextSerial who), .expireChoice activation.key⟩],
        execution.native.receipts ++
          [((who, execution.native.pool.nextSerial who), true)]) := by
  apply runtime.relay_include_accepts players who (.expireChoice activation.key) execution
  · exact hbase
  · exact due_of_publicChoice runtime execution.native.application activation hstate hactive
      code hcode timeout htimeout hoverdue
  · exact hfresh
  · exact runtime.handle_expireChoice_after_window execution.native.application activation
      hstate hactive code hcode timeout htimeout hready hoverdue reads hreads hvalid _

/-- A waiting arbitrary principal authors and includes a ready conditional
expiry through the shared policy runner. -/
theorem relay_conditionalExpire_accepts (runtime : WindowedApplication P L)
    (players : P → runtime.application.PlayerPolicy) (who : P)
    (execution : runtime.application.PolicyExecution) (activation : Activation Nat)
    (hstate : runtime.Consistent execution.native.application)
    (hactive : execution.native.application.active = some activation)
    (code : ConditionalCode P L)
    (hcode : runtime.image.lookup activation.key = some (.conditional code))
    (hready : code.endpoint.readyDisposition
      (code.binding? execution.native.application.base.memory)
      execution.native.application.base.memory.done = true)
    (hoverdue : activation.since + runtime.windowOf activation.key <
      execution.native.application.base.memory.clock)
    (hbase : players who (execution.principalHistory who)
      (MessageApplication.State.observe runtime.application execution.native who) =
        FinDist.pure .wait)
    (hfresh : execution.native.pool.lookup
      (who, execution.native.pool.nextSerial who) = none) :
    (runtime.application.runPolicies (runtime.relayAt players who)
      (runtime.application.includeLatestFrom who) [.player who, .environment] execution).map
        (fun out => (out.native.application, out.native.pool.ledger, out.native.receipts)) =
      FinDist.pure (runtime.advanceTo execution.native.application
        (execution.native.application.base.publishConditional code none),
        execution.native.pool.ledger ++ [⟨(who, execution.native.pool.nextSerial who),
          .conditional activation.key .expire⟩],
        execution.native.receipts ++
          [((who, execution.native.pool.nextSerial who), true)]) := by
  apply runtime.relay_include_accepts players who
    (.conditional activation.key .expire) execution
  · exact hbase
  · exact due_of_conditional runtime execution.native.application activation hstate hactive
      code hcode hoverdue
  · exact hfresh
  · exact runtime.handle_conditionalExpire_after_window execution.native.application activation
      hstate hactive code hcode hready hoverdue _

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.relay_expireBinding_accepts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.relay_expireBinding_accepts

/-- info: 'Vegas.WindowedApplication.relay_expireChoice_accepts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.relay_expireChoice_accepts

/-- info: 'Vegas.WindowedApplication.relay_conditionalExpire_accepts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.relay_conditionalExpire_accepts
