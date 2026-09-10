/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationImageBindings

/-! # Owner-local agreement for ideal application states

The relation retains public memory and one principal's private preparations
and accepted snapshots. Other principals' private values may differ. It is
an invariant for comparing actual executions, not an observation projection:
the native interface still exposes only public memory.

Authenticated opening messages from the retained principal cannot distinguish
other private tables through acceptance receipts. Non-opening handlers also
preserve agreement for other authors, including opaque binding admission and
permissionless expiry. The full-run source information theorem must derive
this relation at paired reachable checkpoints and account for opponents'
generated opening messages.
-/

namespace Vegas.ApplicationImage

open EventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The raw packet forms whose acceptance can query a private commitment
snapshot. All other handlers use public state, including binding admission,
decline, and expiry. This predicate constrains a privacy comparison, not the
commands available to any player. -/
def Payload.OpensCommitment : Payload P L → Prop
  | .conditional _ (.opening _ _) => True
  | _ => False

/-- Public state and the private information relevant to one authenticated
principal agree. Unaccepted snapshots and other owners' snapshots are free. -/
structure State.AgreesFor (who : P) (left right : State P L) : Prop where
  memory : left.memory = right.memory
  prepared : ∀ slot, left.prepared.lookup (who, slot) = right.prepared.lookup (who, slot)
  frozen : ∀ field slot, left.memory.accepted field = some (.opaque (who, slot)) →
    left.frozen field = right.frozen field

namespace State.AgreesFor

variable {who : P} {left right : State P L}

omit [DecidableEq P] in
protected theorem refl (who : P) (state : State P L) : state.AgreesFor who state :=
  ⟨rfl, fun _ => rfl, fun _ _ _ => rfl⟩

omit [DecidableEq P] in
protected theorem symm (h : left.AgreesFor who right) : right.AgreesFor who left :=
  ⟨h.memory.symm, fun slot => (h.prepared slot).symm,
    fun field slot haccepted => (h.frozen field slot (h.memory.symm ▸ haccepted)).symm⟩

omit [DecidableEq P] in
protected theorem trans {last : State P L}
    (h : left.AgreesFor who right) (hnext : right.AgreesFor who last) :
    left.AgreesFor who last :=
  ⟨h.memory.trans hnext.memory, fun slot => (h.prepared slot).trans (hnext.prepared slot),
    fun field slot haccepted => (h.frozen field slot haccepted).trans
      (hnext.frozen field slot (h.memory ▸ haccepted))⟩

theorem register (h : left.AgreesFor who right) (slot : Nat) (value : TypedValue L) :
    (left.register who slot value).AgreesFor who (right.register who slot value) := by
  refine ⟨h.memory, ?_, h.frozen⟩
  intro key
  have hslot := h.prepared slot
  have hkey := h.prepared key
  change left.prepared.table who slot = right.prepared.table who slot at hslot
  simp only [State.register, IdealCommitments.sealValue, hslot]
  cases right.prepared.table who slot <;>
    simp only [IdealCommitments.lookup] at hkey ⊢
  · split
    · rfl
    · exact hkey
  · exact hkey

/-- Different private registrations by another principal preserve agreement;
neither the registered values nor even the chosen slots must coincide. -/
theorem register_other (h : left.AgreesFor who right) (actor : P) (hne : actor ≠ who)
    (leftSlot rightSlot : Nat) (leftValue rightValue : TypedValue L) :
    (left.register actor leftSlot leftValue).AgreesFor who
      (right.register actor rightSlot rightValue) := by
  refine ⟨h.memory, ?_, h.frozen⟩
  intro slot
  have hp := h.prepared slot
  simp only [State.register, IdealCommitments.sealValue]
  cases left.prepared.table actor leftSlot <;>
    cases right.prepared.table actor rightSlot <;>
    simpa only [IdealCommitments.lookup, Ne.symm hne, false_and, ↓reduceIte] using hp

omit [DecidableEq P] in
theorem bind (h : left.AgreesFor who right) (code : BindingCode P L)
    (handle : CommitmentHandle P Nat) :
    (left.bind code handle).AgreesFor who (right.bind code handle) := by
  refine ⟨by simp only [State.bind, h.memory], h.prepared, ?_⟩
  intro field slot haccepted
  by_cases hfield : field = code.sourceField
  · subst field
    have hhandle : handle = (who, slot) := by
      simpa only [State.bind, if_pos, Option.some.injEq, BindingDisposition.opaque.injEq]
        using haccepted
    simp only [State.bind, if_pos, hhandle]
    exact h.prepared slot
  · simp only [State.bind, if_neg hfield] at haccepted ⊢
    exact h.frozen field slot haccepted

omit [DecidableEq P] in
theorem defaultBind (h : left.AgreesFor who right) (code : BindingCode P L)
    (value : TypedValue L) :
    (left.defaultBind code value).AgreesFor who (right.defaultBind code value) := by
  refine ⟨by simp only [State.defaultBind, h.memory], h.prepared, ?_⟩
  intro field slot haccepted
  by_cases hfield : field = code.sourceField
  · simp only [State.defaultBind, if_pos hfield] at haccepted
    cases haccepted
  · exact h.frozen field slot (by simpa only [State.defaultBind, if_neg hfield] using haccepted)

omit [DecidableEq P] in
theorem publish (h : left.AgreesFor who right) (code : PublicChoiceCode P L)
    (value : L.Val code.guard.ty) :
    (left.publish code value).AgreesFor who (right.publish code value) :=
  ⟨by simp only [State.publish, h.memory], h.prepared, h.frozen⟩

omit [DecidableEq P] in
theorem publishConditional (h : left.AgreesFor who right) (code : ConditionalCode P L)
    (value : Option (L.Val code.secretTy)) :
    (left.publishConditional code value).AgreesFor who (right.publishConditional code value) :=
  ⟨by simp only [State.publishConditional, h.memory], h.prepared, h.frozen⟩

omit [DecidableEq P] in
theorem advance (h : left.AgreesFor who right) (clock : Nat) :
    (left.advance clock).AgreesFor who (right.advance clock) :=
  ⟨by simp only [State.advance, h.memory], h.prepared, h.frozen⟩

omit [DecidableEq P] in
theorem sample (h : left.AgreesFor who right) (code : SampleCode L)
    (value : L.Val code.dist.ty) :
    (left.sample code value).AgreesFor who (right.sample code value) :=
  ⟨by simp only [State.sample, h.memory], h.prepared, h.frozen⟩

/-- Conditional resolution agrees when any opening is authored by the retained
principal. Other packet forms need no authorship restriction. -/
theorem resolveDisposition (h : left.AgreesFor who right) (code : ConditionalCode P L)
    (id : MessageId P) (payload : ConditionalPublication.Payload P (L.Val code.secretTy))
    (hsender : ∀ handle value, payload = .opening handle value → id.1 = who) :
    code.endpoint.resolveDisposition? left.memory.clock (left.verify code)
        (code.binding? left.memory) left.memory.done (code.canOpen left.memory.store)
        ⟨id, payload⟩ =
      code.endpoint.resolveDisposition? right.memory.clock (right.verify code)
        (code.binding? right.memory) right.memory.done (code.canOpen right.memory.store)
        ⟨id, payload⟩ := by
  rw [h.memory]
  cases hbinding : code.binding? right.memory with
  | none => rfl
  | some disposition =>
      cases disposition with
      | publicDefault value => rfl
      | «opaque» handle =>
          by_cases howner : code.endpoint.owner = who
          · by_cases hcanonical : handle = (code.endpoint.owner, code.endpoint.sourceSlot)
            · have haccepted : left.memory.accepted code.sourceField =
                  some (.opaque (who, code.endpoint.sourceSlot)) := by
                rw [h.memory]
                have ha := (code.binding?_opaque_iff right.memory handle).mp hbinding
                simpa only [hcanonical, howner] using ha
              have hverify : left.verify code = right.verify code := by
                funext opening
                simp only [State.verify, h.frozen _ _ haccepted]
              rw [hverify]
            · simp [ConditionalPublication.resolveDisposition?, ConditionalPublication.resolve?,
                ConditionalPublication.ready, hcanonical]
          · cases payload with
            | opening handle value =>
                simp [ConditionalPublication.resolveDisposition?, ConditionalPublication.resolve?,
                  Message.sender, hsender handle value rfl, Ne.symm howner]
            | decline | expire | cleartext _ | malformed => rfl

/-- Matching raw messages have matching acceptance and related successors.
Only opening packets require focal authorship; other senders may submit any
non-opening packet. No source legality or typing premise is required. -/
theorem handle (h : left.AgreesFor who right) (image : ApplicationImage P L)
    (message : Message P (Payload P L))
    (hsender : message.payload.OpensCommitment → message.sender = who) :
    Option.Rel (State.AgreesFor who) (image.handle left message) (image.handle right message) := by
  rcases message with ⟨id, payload⟩
  cases payload with
  | malformed data => exact .none
  | choice address typed =>
      cases hlookup : image.lookup address with
      | none => simp only [ApplicationImage.handle, hlookup]; exact .none
      | some instruction =>
          cases instruction with
          | sample code | bind code | conditional code =>
              simp only [ApplicationImage.handle, hlookup]; exact .none
          | publicChoice code =>
              simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind, Option.bind_some]
              cases htyped : typed.as? code.guard.ty with
              | none => simp only [Option.bind_none]; exact .none
              | some value =>
                  simp only [Option.bind_some, h.memory]
                  cases code.endpoint.resolve? right.memory.done
                      (code.guard.validate right.memory.store) ⟨id, value⟩ with
                  | none => exact .none
                  | some accepted => exact .some (h.publish code accepted)
  | expireChoice address =>
      cases hlookup : image.lookup address with
      | none => simp only [ApplicationImage.handle, hlookup]; exact .none
      | some instruction =>
          cases instruction with
          | sample code | bind code | conditional code =>
              simp only [ApplicationImage.handle, hlookup]; exact .none
          | publicChoice code =>
              simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                Option.bind_some, h.memory]
              cases code.resolveTimeout? right.memory with
              | none => exact .none
              | some value => exact .some (h.publish code value)
  | binding address handle =>
      cases hlookup : image.lookup address with
      | none => simp only [ApplicationImage.handle, hlookup]; exact .none
      | some instruction =>
          cases instruction with
          | sample code | publicChoice code | conditional code =>
              simp only [ApplicationImage.handle, hlookup]; exact .none
          | bind code =>
              simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                Option.bind_some, h.memory]
              split
              · exact .some (h.bind code handle)
              · exact .none
  | expireBinding address =>
      cases hlookup : image.lookup address with
      | none => simp only [ApplicationImage.handle, hlookup]; exact .none
      | some instruction =>
          cases instruction with
          | sample code | publicChoice code | conditional code =>
              simp only [ApplicationImage.handle, hlookup]; exact .none
          | bind code =>
              simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind,
                Option.bind_some, h.memory]
              cases code.resolveTimeout? right.memory with
              | none => exact .none
              | some value => exact .some (h.defaultBind code ⟨code.ty, value⟩)
  | conditional address payload =>
      cases hlookup : image.lookup address with
      | none => simp only [ApplicationImage.handle, hlookup]; exact .none
      | some instruction =>
          cases instruction with
          | sample code | bind code | publicChoice code =>
              simp only [ApplicationImage.handle, hlookup]; exact .none
          | conditional code =>
              simp only [ApplicationImage.handle, hlookup, Option.bind_eq_bind, Option.bind_some]
              cases hdecode : code.decode payload with
              | none => simp only [Option.bind_none]; exact .none
              | some decoded =>
                  simp only [Option.bind_some]
                  have hauthor : ∀ handle value, decoded = .opening handle value → id.1 = who := by
                    intro handle value hopen
                    subst decoded
                    cases payload with
                    | opening _ _ => exact hsender trivial
                    | cleartext typed =>
                        cases ht : typed.as? code.secretTy <;>
                          simp [ConditionalCode.decode, ht] at hdecode
                    | decline | expire | malformed => cases hdecode
                  rw [h.resolveDisposition code id decoded hauthor]
                  cases code.endpoint.resolveDisposition? right.memory.clock (right.verify code)
                      (code.binding? right.memory) right.memory.done
                      (code.canOpen right.memory.store) ⟨id, decoded⟩ with
                  | none => exact .none
                  | some result => exact .some (h.publishConditional code result)

end State.AgreesFor

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.State.AgreesFor.handle' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.State.AgreesFor.handle
