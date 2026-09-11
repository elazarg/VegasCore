/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationService
import Vegas.Compile.WindowedPolicyPrivacy

/-! # Focal-owned inclusion privacy -/

noncomputable section

namespace Vegas

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace ApplicationImage.State.AgreesFor

/-- At an instruction submitted by the retained principal, every packet has
matching handler behavior. A foreign opening is rejected by the conditional
owner check before its verifier can inspect another principal's snapshot. -/
theorem handle_of_submitter (image : ApplicationImage P L) {who : P}
    {left right : ApplicationImage.State P L} (h : left.AgreesFor who right)
    (instruction : ApplicationInstruction P L) (address : Nat)
    (hlookup : image.lookup address = some instruction)
    (hsubmitter : instruction.submitter = some who)
    (message : Message P (ApplicationImage.Payload P L))
    (haddress : message.payload.address? = some address) :
    Option.Rel (ApplicationImage.State.AgreesFor who)
      (image.handle left message) (image.handle right message) := by
  by_cases hauthor : message.sender = who
  · exact h.handle image message (fun _ => hauthor)
  · rcases message with ⟨id, payload⟩
    cases payload with
    | malformed data => exact .none
    | choice submitted value =>
        simp only [ApplicationImage.Payload.address?, Option.some.injEq] at haddress
        subst submitted
        exact h.handle image ⟨id, .choice address value⟩ (by
          intro hopen
          cases hopen)
    | expireChoice submitted =>
        simp only [ApplicationImage.Payload.address?, Option.some.injEq] at haddress
        subst submitted
        exact h.handle image ⟨id, .expireChoice address⟩ (by
          intro hopen
          cases hopen)
    | binding submitted handle =>
        simp only [ApplicationImage.Payload.address?, Option.some.injEq] at haddress
        subst submitted
        exact h.handle image ⟨id, .binding address handle⟩ (by
          intro hopen
          cases hopen)
    | expireBinding submitted =>
        simp only [ApplicationImage.Payload.address?, Option.some.injEq] at haddress
        subst submitted
        exact h.handle image ⟨id, .expireBinding address⟩ (by
          intro hopen
          cases hopen)
    | conditional submitted payload =>
        simp only [ApplicationImage.Payload.address?, Option.some.injEq] at haddress
        subst submitted
        cases payload with
        | decline | expire | cleartext _ | malformed =>
            exact h.handle image _ (by simp [ApplicationImage.Payload.OpensCommitment])
        | opening handle value =>
            cases instruction with
            | sample code =>
                simp [ApplicationImage.handle, hlookup]
            | bind code =>
                simp [ApplicationImage.handle, hlookup]
            | publicChoice code =>
                simp [ApplicationImage.handle, hlookup]
            | conditional code =>
                change id.1 ≠ who at hauthor
                simp only [ApplicationInstruction.submitter, Option.some.injEq] at hsubmitter
                simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                  Option.bind_some, ConditionalCode.decode]
                cases htyped : value.as? code.secretTy with
                | none =>
                    simp only [Option.map_none, Option.bind_none]
                    exact .none
                | some decoded =>
                    simp only [Option.map_some, Option.bind_some]
                    rw [h.memory]
                    have hreject (verify : IdealCommitments.Opening
                        (Principal := P) (Slot := Nat) (Value := L.Val code.secretTy) →
                        Bool) :
                        code.endpoint.resolveDisposition? right.memory.clock verify
                          (code.binding? right.memory) right.memory.done
                          (code.canOpen right.memory.store)
                          ⟨id, .opening handle decoded⟩ = none := by
                      cases code.binding? right.memory with
                      | none => rfl
                      | some disposition =>
                          cases disposition with
                          | «opaque» accepted =>
                              simp [ConditionalPublication.resolveDisposition?,
                                ConditionalPublication.resolve?, Message.sender,
                                hsubmitter, hauthor]
                          | publicDefault value =>
                              simp [ConditionalPublication.resolveDisposition?,
                                ConditionalPublication.resolveDefault?]
                    rw [hreject, hreject]
                    exact .none

end ApplicationImage.State.AgreesFor

namespace WindowedApplication

namespace State.AgreesFor

private theorem ordered_handle_of_active_submitter
    {who : P} {left right : State P L} (h : left.AgreesFor who right)
    (image : ApplicationImage P L) (instruction : ApplicationInstruction P L)
    (hactive : image.activeAddress? left.base.memory = some instruction.address)
    (hlookup : image.lookup instruction.address = some instruction)
    (hsubmitter : instruction.submitter = some who)
    (message : Message P (ApplicationImage.Payload P L)) :
    Option.Rel (ApplicationImage.State.AgreesFor who)
      (image.orderedApplication.handle left.base message)
      (image.orderedApplication.handle right.base message) := by
  simp only [ApplicationImage.orderedApplication, MessageApplication.withAdmission]
  change Option.Rel (ApplicationImage.State.AgreesFor who)
    (if image.admitsMessage left.base.memory message then image.handle left.base message else none)
    (if image.admitsMessage right.base.memory message then
      image.handle right.base message else none)
  rw [h.base.memory]
  split
  · rename_i hadmitted
    simp only [ApplicationImage.admitsMessage] at hadmitted
    split at hadmitted
    · contradiction
    · rename_i address haddress
      have hrequested := (image.admitsAddress_iff right.base.memory address).mp hadmitted
      rw [← h.base.memory, hactive] at hrequested
      have heq : address = instruction.address :=
        Option.some.inj hrequested.symm
      subst address
      exact h.base.handle_of_submitter image instruction instruction.address hlookup
        hsubmitter message haddress
  · exact .none

/-- The windowed ordered handler preserves focal agreement for every packet at
an active instruction submitted by the focal principal. -/
theorem handle_of_active_submitter {runtime : WindowedApplication P L} {who : P}
    {left right : State P L} (h : left.AgreesFor who right)
    (activation : Activation Nat) (instruction : ApplicationInstruction P L)
    (hactivation : left.active = some activation)
    (hkey : activation.key = instruction.address)
    (hactive : runtime.image.activeAddress? left.base.memory = some instruction.address)
    (hlookup : runtime.image.lookup instruction.address = some instruction)
    (hsubmitter : instruction.submitter = some who)
    (message : Message P (ApplicationImage.Payload P L)) :
    Option.Rel (State.AgreesFor who)
      (runtime.handle left message) (runtime.handle right message) := by
  have hrightActivation : right.active = some activation := by
    rw [← h.active]
    exact hactivation
  have hcurrent :
      runtime.image.activeAddress? right.base.memory = some activation.key := by
    rw [← h.base.memory, hkey]
    exact hactive
  have hcurrentLeft :
      runtime.image.activeAddress? left.base.memory = some activation.key := by
    rw [hkey]
    exact hactive
  simp only [WindowedApplication.handle, hactivation, hrightActivation,
    Option.bind_eq_bind, Option.bind_some, hcurrentLeft, hcurrent, if_pos]
  have hactiveAt :
      (runtime.atOrigin activation.since).activeAddress? left.base.memory =
        some instruction.address := by
    simpa only [atOrigin, ApplicationImage.activeAddress?_withDeadlines] using hactive
  let timed := instruction.withDeadlines
    (fun address => activation.since + runtime.windowOf address)
  have hlookupAt :
      (runtime.atOrigin activation.since).lookup timed.address = some timed := by
    simp only [atOrigin, ApplicationImage.lookup_withDeadlines, hlookup, Option.map_some,
      timed, ApplicationInstruction.withDeadlines_address]
  have hsubmitterAt : timed.submitter = some who := by
    cases instruction <;> exact hsubmitter
  have hrelated := h.ordered_handle_of_active_submitter
    (runtime.atOrigin activation.since) timed
      (by simpa only [timed, ApplicationInstruction.withDeadlines_address] using hactiveAt)
      hlookupAt hsubmitterAt message
  have hmap : ∀ (first second : Option (ApplicationImage.State P L)),
      Option.Rel (ApplicationImage.State.AgreesFor who) first second →
      Option.Rel (State.AgreesFor who)
        (first.bind fun next => some (runtime.advanceTo left next))
        (second.bind fun next => some (runtime.advanceTo right next)) := by
    intro first second hpair
    cases hpair with
    | none => exact .none
    | some hnext => exact .some (h.advanceTo runtime hnext)
  exact hmap _ _ hrelated

end State.AgreesFor

/-- Inclusion of an arbitrary selected packet preserves focal agreement while
the current instruction is submitted by the focal principal. -/
theorem includePending_agrees_of_active_submitter
    (runtime : WindowedApplication P L) (who : P)
    (left right : runtime.application.State)
    (hstate : left.application.AgreesFor who right.application)
    (hpool : left.pool = right.pool) (hreceipts : left.receipts = right.receipts)
    (activation : Activation Nat) (instruction : ApplicationInstruction P L)
    (hactivation : left.application.active = some activation)
    (hkey : activation.key = instruction.address)
    (hactive : runtime.image.activeAddress? left.application.base.memory =
      some instruction.address)
    (hlookup : runtime.image.lookup instruction.address = some instruction)
    (hsubmitter : instruction.submitter = some who) (id : MessageId P) :
    let nextLeft := runtime.application.includePending left id
    let nextRight := runtime.application.includePending right id
    nextLeft.application.AgreesFor who nextRight.application ∧
      nextLeft.pool = nextRight.pool ∧ nextLeft.receipts = nextRight.receipts := by
  cases hmessage : left.pool.lookup id with
  | none =>
      have hright : right.pool.lookup id = none := hpool ▸ hmessage
      rw [MessageApplication.includePending_missing _ _ _ hmessage,
        MessageApplication.includePending_missing _ _ _ hright]
      exact ⟨hstate, hpool, hreceipts⟩
  | some message =>
      have hright : right.pool.lookup id = some message := hpool ▸ hmessage
      have hrelated := hstate.handle_of_active_submitter activation instruction
        hactivation hkey hactive hlookup hsubmitter message
      cases hleftHandle : runtime.handle left.application message with
      | none =>
          rw [hleftHandle] at hrelated
          have hrightHandle : runtime.handle right.application message = none := by
            generalize runtime.handle right.application message = result at hrelated ⊢
            cases hrelated
            rfl
          rw [MessageApplication.includePending_reject _ _ _ _ hmessage hleftHandle,
            MessageApplication.includePending_reject _ _ _ _ hright hrightHandle]
          exact ⟨hstate, by rw [hpool], by rw [hreceipts]⟩
      | some nextLeft =>
          rw [hleftHandle] at hrelated
          cases hrightHandle : runtime.handle right.application message with
          | none => rw [hrightHandle] at hrelated; cases hrelated
          | some nextRight =>
              rw [hrightHandle] at hrelated
              have hnext : nextLeft.AgreesFor who nextRight := by
                cases hrelated
                assumption
              rw [MessageApplication.includePending_accept _ _ _ _ _ hmessage hleftHandle,
                MessageApplication.includePending_accept _ _ _ _ _ hright hrightHandle]
              exact ⟨hnext, by rw [hpool], by rw [hreceipts]⟩

namespace PolicyAgreement

/-- The actual inclusion step preserves the focal policy input at a
focal-owned active instruction, for every pending raw packet or replay. -/
theorem environmentPolicyStep_include_of_active_submitter
    {runtime : WindowedApplication P L} {who : P}
    {left right : runtime.application.PolicyExecution}
    (h : PolicyAgreement runtime who left right)
    (activation : Activation Nat) (instruction : ApplicationInstruction P L)
    (hactivation : left.native.application.active = some activation)
    (hkey : activation.key = instruction.address)
    (hactive : runtime.image.activeAddress? left.native.application.base.memory =
      some instruction.address)
    (hlookup : runtime.image.lookup instruction.address = some instruction)
    (hsubmitter : instruction.submitter = some who) (id : MessageId P)
    (nextLeft nextRight : runtime.application.PolicyExecution)
    (hleft : nextLeft ∈
      (runtime.application.environmentPolicyStep left (.include id)).support)
    (hright : nextRight ∈
      (runtime.application.environmentPolicyStep right (.include id)).support) :
    PolicyAgreement runtime who nextLeft nextRight := by
  obtain ⟨hstate, hpool, hreceipts⟩ :=
    runtime.includePending_agrees_of_active_submitter who left.native right.native
      h.state h.pool h.receipts activation instruction hactivation hkey hactive
        hlookup hsubmitter id
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hleft hright
  subst nextLeft
  subst nextRight
  exact ⟨hstate, hpool, hreceipts, h.history⟩

end PolicyAgreement

end WindowedApplication

end Vegas

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.environmentPolicyStep_include_of_active_submitter'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.WindowedApplication.PolicyAgreement.environmentPolicyStep_include_of_active_submitter
