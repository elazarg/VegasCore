/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImagePrivacy
import Vegas.Compile.WindowedApplication
import Interaction.MessageApplicationLaws

/-! # Owner-local privacy through windowed inclusion

Ordered admission and relative deadlines preserve the ideal application's
owner-local agreement. Opening packets authenticated as that owner and all
non-opening packets produce the same public receipts and observations in
agreeing states. The premise concerns the original author; a rebroadcaster
does not gain that identity. Other authors' opening packets require a separate
source-value, provenance, or completed-address argument.
-/

noncomputable section

namespace Vegas.WindowedApplication

open Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Public activation and the retained owner's ideal-service information agree. -/
structure State.AgreesFor (who : P) (left right : State P L) : Prop where
  base : left.base.AgreesFor who right.base
  active : left.active = right.active

namespace State.AgreesFor

variable {who : P} {left right : State P L}

private theorem ordered_handle (h : left.AgreesFor who right)
    (image : ApplicationImage P L) (message : Message P (ApplicationImage.Payload P L))
    (hauthor : message.payload.OpensCommitment → message.sender = who) :
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
  · exact h.base.handle image message hauthor
  · exact .none

omit [DecidableEq P] in
theorem advanceTo (h : left.AgreesFor who right) (runtime : WindowedApplication P L)
    {nextLeft nextRight : ApplicationImage.State P L}
    (hnext : nextLeft.AgreesFor who nextRight) :
    (runtime.advanceTo left nextLeft).AgreesFor who (runtime.advanceTo right nextRight) :=
  ⟨hnext, by simp only [WindowedApplication.advanceTo, h.active, hnext.memory]⟩

/-- The deadline-decorated ordered handlers match, including rejection and
metadata consistency checks. Only opening packets require focal authorship. -/
theorem handle (h : left.AgreesFor who right) (runtime : WindowedApplication P L)
    (message : Message P (ApplicationImage.Payload P L))
    (hauthor : message.payload.OpensCommitment → message.sender = who) :
    Option.Rel (State.AgreesFor who) (runtime.handle left message)
      (runtime.handle right message) := by
  simp only [WindowedApplication.handle, h.active, h.base.memory]
  cases hactivation : right.active with
  | none => exact .none
  | some activation =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      split
      · have hrelated := h.ordered_handle (runtime.atOrigin activation.since) message hauthor
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
      · exact .none

end State.AgreesFor

/-- Inclusion preserves owner-local private agreement, the actual ledger,
and all acceptance or rejection receipts. -/
theorem includePending_agrees (runtime : WindowedApplication P L)
    (who : P) (left right : runtime.application.State)
    (hstate : left.application.AgreesFor who right.application)
    (hpool : left.pool = right.pool) (hreceipts : left.receipts = right.receipts)
    (id : MessageId P)
    (hauthor : ∀ message, left.pool.lookup id = some message →
      message.payload.OpensCommitment → message.sender = who) :
    let nextLeft := runtime.application.includePending left id
    let nextRight := runtime.application.includePending right id
    nextLeft.application.AgreesFor who nextRight.application ∧
      nextLeft.pool = nextRight.pool ∧ nextLeft.receipts = nextRight.receipts := by
  cases hlookup : left.pool.lookup id with
  | none =>
      have hright : right.pool.lookup id = none := hpool ▸ hlookup
      rw [MessageApplication.includePending_missing _ _ _ hlookup,
        MessageApplication.includePending_missing _ _ _ hright]
      exact ⟨hstate, hpool, hreceipts⟩
  | some message =>
      have hright : right.pool.lookup id = some message := hpool ▸ hlookup
      have hrelated := hstate.handle runtime message (hauthor message hlookup)
      cases hleftHandle : runtime.handle left.application message with
      | none =>
          rw [hleftHandle] at hrelated
          have hrightHandle : runtime.handle right.application message = none := by
            generalize runtime.handle right.application message = result at hrelated ⊢
            cases hrelated
            rfl
          rw [MessageApplication.includePending_reject _ _ _ _ hlookup hleftHandle,
            MessageApplication.includePending_reject _ _ _ _ hright hrightHandle]
          exact ⟨hstate, by rw [hpool], by rw [hreceipts]⟩
      | some nextLeft =>
          rw [hleftHandle] at hrelated
          cases hrightHandle : runtime.handle right.application message with
          | none => rw [hrightHandle] at hrelated; cases hrelated
          | some nextRight =>
              rw [hrightHandle] at hrelated
              have hnext : nextLeft.AgreesFor who nextRight := by cases hrelated; assumption
              rw [MessageApplication.includePending_accept _ _ _ _ _ hlookup hleftHandle,
                MessageApplication.includePending_accept _ _ _ _ _ hright hrightHandle]
              exact ⟨hnext, by rw [hpool], by rw [hreceipts]⟩

/-- Every observer receives the same public inclusion result when any opening
packet is focal-authored; non-opening packets may come from other principals. -/
theorem includePending_observe_eq (runtime : WindowedApplication P L)
    (who : P) (left right : runtime.application.State)
    (hstate : left.application.AgreesFor who right.application)
    (hpool : left.pool = right.pool) (hreceipts : left.receipts = right.receipts)
    (id : MessageId P)
    (hauthor : ∀ message, left.pool.lookup id = some message →
      message.payload.OpensCommitment → message.sender = who)
    (observer : P) :
    MessageApplication.State.observe runtime.application
        (runtime.application.includePending left id) observer =
      MessageApplication.State.observe runtime.application
        (runtime.application.includePending right id) observer := by
  obtain ⟨hnext, hp, hr⟩ :=
    runtime.includePending_agrees who left right hstate hpool hreceipts id hauthor
  generalize runtime.application.includePending left id = nextLeft at hnext hp hr ⊢
  generalize runtime.application.includePending right id = nextRight at hnext hp hr ⊢
  simp only [MessageApplication.State.observe, application, hp, hr,
    hnext.base.memory, hnext.active]

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.includePending_observe_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.includePending_observe_eq
