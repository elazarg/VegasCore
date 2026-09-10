/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedApplication

/-! # Strict response windows

An expiry request cannot resolve its active instruction at or before the end
of that instruction's activation-relative window. These are handler rejection
laws only; they do not assert that a request is delivered or that time advances.
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

private theorem expireBinding_before_deadline
    (image : ApplicationImage P L) (windowOf : Nat → Nat) (origin : Nat)
    (state : ApplicationImage.State P L) (address : Nat) (id : MessageId P)
    (hclock : state.memory.clock ≤ origin + windowOf address) :
    (image.withDeadlines (fun current => origin + windowOf current)).handle state
      ⟨id, .expireBinding address⟩ = none := by
  simp only [ApplicationImage.handle, ApplicationImage.lookup_withDeadlines]
  cases hlookup : image.lookup address with
  | none => rfl
  | some instruction =>
      have haddress := lookup_address_eq image address instruction hlookup
      cases instruction with
      | sample code | publicChoice code | conditional code => rfl
      | bind code =>
          change code.node = address at haddress
          cases htimeout : code.timeout with
          | none => simp [ApplicationInstruction.withDeadlines, BindingCode.resolveTimeout?,
              htimeout]
          | some timeout =>
              have hnotOverdue : ¬origin + windowOf code.node < state.memory.clock := by
                rw [haddress]
                omega
              simp [ApplicationInstruction.withDeadlines, BindingCode.resolveTimeout?,
                htimeout, hnotOverdue]

private theorem expireChoice_before_deadline
    (image : ApplicationImage P L) (windowOf : Nat → Nat) (origin : Nat)
    (state : ApplicationImage.State P L) (address : Nat) (id : MessageId P)
    (hclock : state.memory.clock ≤ origin + windowOf address) :
    (image.withDeadlines (fun current => origin + windowOf current)).handle state
      ⟨id, .expireChoice address⟩ = none := by
  simp only [ApplicationImage.handle, ApplicationImage.lookup_withDeadlines]
  cases hlookup : image.lookup address with
  | none => rfl
  | some instruction =>
      have haddress := lookup_address_eq image address instruction hlookup
      cases instruction with
      | sample code | bind code | conditional code => rfl
      | publicChoice code =>
          change code.endpoint.publicationNode = address at haddress
          cases htimeout : code.timeout with
          | none => simp [ApplicationInstruction.withDeadlines,
              PublicChoiceCode.resolveTimeout?, htimeout]
          | some timeout =>
              have hnotOverdue :
                  ¬origin + windowOf code.endpoint.publicationNode < state.memory.clock := by
                rw [haddress]
                omega
              simp [ApplicationInstruction.withDeadlines,
                PublicChoiceCode.resolveTimeout?, htimeout, hnotOverdue]

private theorem conditionalExpire_before_deadline
    (image : ApplicationImage P L) (windowOf : Nat → Nat) (origin : Nat)
    (state : ApplicationImage.State P L) (address : Nat) (id : MessageId P)
    (hclock : state.memory.clock ≤ origin + windowOf address) :
    (image.withDeadlines (fun current => origin + windowOf current)).handle state
      ⟨id, .conditional address .expire⟩ = none := by
  simp only [ApplicationImage.handle, ApplicationImage.lookup_withDeadlines]
  cases hlookup : image.lookup address with
  | none => rfl
  | some instruction =>
      have haddress := lookup_address_eq image address instruction hlookup
      cases instruction with
      | sample code | bind code | publicChoice code => rfl
      | conditional code =>
          change code.endpoint.publicationNode = address at haddress
          have hnotOverdue :
              ¬origin + windowOf code.endpoint.publicationNode < state.memory.clock := by
            rw [haddress]
            omega
          have hbinding :
              ({ code with endpoint :=
                  { code.endpoint with deadline :=
                      origin + windowOf code.endpoint.publicationNode } } :
                ConditionalCode P L).binding? state.memory =
                code.binding? state.memory := rfl
          cases haccepted : code.binding? state.memory with
          | none =>
              simp [ApplicationInstruction.withDeadlines, ConditionalCode.decode,
                ConditionalPublication.resolveDisposition?, hbinding, haccepted]
          | some disposition =>
              cases disposition with
              | «opaque» handle =>
                  simp [ApplicationInstruction.withDeadlines, ConditionalCode.decode,
                    ConditionalPublication.resolveDisposition?, hbinding, haccepted,
                    ConditionalPublication.resolve?, hnotOverdue]
              | publicDefault value =>
                  simp [ApplicationInstruction.withDeadlines, ConditionalCode.decode,
                    ConditionalPublication.resolveDisposition?, hbinding, haccepted,
                    ConditionalPublication.resolveDefault?, hnotOverdue]

private theorem ordered_handle_eq_none
    (image : ApplicationImage P L) (state : ApplicationImage.State P L)
    (message : Message P (ApplicationImage.Payload P L))
    (hhandle : image.handle state message = none) :
    image.orderedApplication.handle state message = none := by
  simp only [ApplicationImage.orderedApplication, MessageApplication.withAdmission]
  change (if image.admitsMessage state.memory message then image.handle state message else none) =
    none
  rw [hhandle]
  split <;> rfl

/-- A binding expiry is rejected throughout its strict activation window. -/
theorem handle_expireBinding_before_window
    (runtime : WindowedApplication P L) (state : State P L)
    (activation : Activation Nat) (hactive : state.active = some activation)
    (address : Nat) (id : MessageId P)
    (hclock : state.base.memory.clock ≤ activation.since + runtime.windowOf address) :
    runtime.handle state ⟨id, .expireBinding address⟩ = none := by
  unfold handle
  rw [hactive]
  simp only [Option.bind_eq_bind, Option.bind_some]
  split
  · have hnone :
        (runtime.atOrigin activation.since).orderedApplication.handle state.base
          ⟨id, .expireBinding address⟩ = none := by
      apply ordered_handle_eq_none
      exact expireBinding_before_deadline runtime.image runtime.windowOf activation.since
        state.base address id hclock
    rw [hnone]
    rfl
  · rfl

/-- A public-choice expiry is rejected throughout its strict activation window. -/
theorem handle_expireChoice_before_window
    (runtime : WindowedApplication P L) (state : State P L)
    (activation : Activation Nat) (hactive : state.active = some activation)
    (address : Nat) (id : MessageId P)
    (hclock : state.base.memory.clock ≤ activation.since + runtime.windowOf address) :
    runtime.handle state ⟨id, .expireChoice address⟩ = none := by
  unfold handle
  rw [hactive]
  simp only [Option.bind_eq_bind, Option.bind_some]
  split
  · have hnone :
        (runtime.atOrigin activation.since).orderedApplication.handle state.base
          ⟨id, .expireChoice address⟩ = none := by
      apply ordered_handle_eq_none
      exact expireChoice_before_deadline runtime.image runtime.windowOf activation.since
        state.base address id hclock
    rw [hnone]
    rfl
  · rfl

/-- A conditional-publication expiry is rejected throughout its strict
activation window, for either an opaque binding or a public default. -/
theorem handle_conditionalExpire_before_window
    (runtime : WindowedApplication P L) (state : State P L)
    (activation : Activation Nat) (hactive : state.active = some activation)
    (address : Nat) (id : MessageId P)
    (hclock : state.base.memory.clock ≤ activation.since + runtime.windowOf address) :
    runtime.handle state ⟨id, .conditional address .expire⟩ = none := by
  unfold handle
  rw [hactive]
  simp only [Option.bind_eq_bind, Option.bind_some]
  split
  · have hnone :
        (runtime.atOrigin activation.since).orderedApplication.handle state.base
          ⟨id, .conditional address .expire⟩ = none := by
      apply ordered_handle_eq_none
      exact conditionalExpire_before_deadline runtime.image runtime.windowOf activation.since
        state.base address id hclock
    rw [hnone]
    rfl
  · rfl

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.handle_expireBinding_before_window' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_expireBinding_before_window

/-- info: 'Vegas.WindowedApplication.handle_expireChoice_before_window' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_expireChoice_before_window

/-- info: 'Vegas.WindowedApplication.handle_conditionalExpire_before_window' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_conditionalExpire_before_window
