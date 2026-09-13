/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedApplication
import Interaction.MessageInvariant
import Interaction.MessageApplicationPolicies

/-! # Partial disclosure in the receipt-bearing sealed runtime

Related states have equal public traffic, events, receipts, and slot occupancy.
Only designated handles must have equal private values. Honest registration
may change other values, and authenticated openings of designated handles
remain possible. Ownership validation prevents other senders from using an
opening as a private-value comparison oracle.
-/

noncomputable section

namespace Interaction.SealedProgram

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]
variable {program : SealedProgram Principal}

/-- An authenticated opening refers only to a handle whose value is allowed
to be compared. Unauthenticated guesses are rejected independently of values. -/
def OpeningKnown (known : CommitmentHandle Principal Nat → Prop)
    (message : Message Principal (Payload Principal Value)) : Prop :=
  match message.payload with
  | .opening _ handle _ => message.sender = handle.1 → known handle
  | _ => True

/-- Knowledge-indexed native-state agreement, including public rejection receipts. -/
structure KnowledgeRelated (program : SealedProgram Principal)
    (known : CommitmentHandle Principal Nat → Prop)
    (left right : (program.messageApplication (Value := Value)).State) : Prop where
  occupied : ∀ handle, (left.application.service.lookup handle).isSome =
    (right.application.service.lookup handle).isSome
  values : ∀ handle, known handle →
    left.application.service.lookup handle = right.application.service.lookup handle
  pool : left.pool = right.pool
  events : left.application.events = right.application.events
  receipts : left.receipts = right.receipts
  openings : left.pool.Satisfies (OpeningKnown known)

variable {known : CommitmentHandle Principal Nat → Prop}
variable {left right : (program.messageApplication (Value := Value)).State}

/-- Public commands agree exactly. Private registrations agree on their slot
and, when that handle is designated known, also on their value. -/
def CommandAgreement (program : SealedProgram Principal)
    (known : CommitmentHandle Principal Nat → Prop) (who : Principal) :
    (program.messageApplication (Value := Value)).PlayerCommand →
      (program.messageApplication (Value := Value)).PlayerCommand → Prop
  | .privateCommand left, .privateCommand right =>
      left.down.1 = right.down.1 ∧ (known (who, left.down.1) → left.down.2 = right.down.2)
  | left, right => left = right

theorem CommandAgreement.refl
    (command : (program.messageApplication (Value := Value)).PlayerCommand)
    (who : Principal) : CommandAgreement program known who command command := by
  cases command <;> simp [CommandAgreement]

theorem KnowledgeRelated.initial : KnowledgeRelated (Value := Value) program known
    (MessageApplication.State.initial _ ⟨IdealCommitments.empty, []⟩)
    (MessageApplication.State.initial _ ⟨IdealCommitments.empty, []⟩) :=
  ⟨fun _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, MessagePool.Satisfies.empty⟩

theorem KnowledgeRelated.observe_eq (related : KnowledgeRelated program known left right)
    (who : Principal) :
    MessageApplication.State.observe _ left who =
      MessageApplication.State.observe _ right who := by
  simp only [MessageApplication.State.observe, messageApplication,
    related.pool, related.events, related.receipts]

theorem KnowledgeRelated.environmentView_eq
    (related : KnowledgeRelated program known left right) :
    MessageApplication.State.environmentView _ left =
      MessageApplication.State.environmentView _ right := by
  simp only [MessageApplication.State.environmentView, messageApplication,
    related.pool, related.events, related.receipts]

/-- Both players register at the same slot; hidden values may differ. -/
theorem KnowledgeRelated.register (related : KnowledgeRelated program known left right)
    (owner : Principal) (slot : Nat) (leftValue rightValue : Value)
    (hvalue : known (owner, slot) → leftValue = rightValue) :
    KnowledgeRelated program known
      { left with application.service :=
        (left.application.service.sealValue owner slot leftValue).state }
      { right with application.service :=
        (right.application.service.sealValue owner slot rightValue).state } := by
  have hslot := related.occupied (owner, slot)
  unfold IdealCommitments.lookup at hslot
  unfold IdealCommitments.sealValue
  cases hl : left.application.service.table owner slot <;>
    cases hr : right.application.service.table owner slot <;>
    simp only [hl, hr, Option.isSome_none, Option.isSome_some] at hslot
  · refine ⟨?_, ?_, related.pool, related.events, related.receipts, related.openings⟩
    · intro handle
      by_cases hhandle : handle.1 = owner ∧ handle.2 = slot
      · simp only [IdealCommitments.lookup, if_pos hhandle, Option.isSome_some]
      · simp only [IdealCommitments.lookup, if_neg hhandle]
        exact related.occupied handle
    · intro handle hknown
      by_cases hhandle : handle.1 = owner ∧ handle.2 = slot
      · have heq : handle = (owner, slot) := Prod.ext hhandle.1 hhandle.2
        have hvalues := hvalue (heq ▸ hknown)
        simp only [IdealCommitments.lookup, if_pos hhandle, hvalues]
      · simp only [IdealCommitments.lookup, if_neg hhandle]
        exact related.values handle hknown
  · contradiction
  · contradiction
  · exact related

/-- Occupancy and authenticated known values determine the complete validator
result, including rejection. This is not an unrestricted verification oracle. -/
theorem KnowledgeRelated.validate_eq (related : KnowledgeRelated program known left right)
    (message : Message Principal (Payload Principal Value))
    (hknown : OpeningKnown known message) :
    program.validateMessage? left.application.service left.application.events message =
      program.validateMessage? right.application.service right.application.events message := by
  rw [related.events]
  cases message with
  | mk id payload =>
      cases payload with
      | commitment node handle =>
          cases hrule : program.rules[node]? with
          | none => simp only [validateMessage?, hrule]
          | some rule =>
              cases hkind : rule.kind <;> simp only [validateMessage?, hrule, hkind]
              rw [related.occupied handle]
      | opening node handle claimed =>
          cases hrule : program.rules[node]? with
          | none => simp only [validateMessage?, hrule]
          | some rule =>
              cases hkind : rule.kind with
              | commit owner | disabled => simp only [validateMessage?, hrule, hkind]
              | reveal owner source =>
                  by_cases howner : id.1 = owner
                  · by_cases hhandle : handle = (owner, source)
                    · have hsame := related.values handle
                        (hknown (howner.trans (congrArg Prod.fst hhandle).symm))
                      simp only [validateMessage?, hrule, hkind, IdealCommitments.verify, hsame]
                    · simp [validateMessage?, hrule, hkind, hhandle]
                  · simp [validateMessage?, hrule, hkind, Message.sender, howner]
      | cleartext node value | malformed => rfl

theorem KnowledgeRelated.submit (related : KnowledgeRelated program known left right)
    (owner : Principal) (payload : Payload Principal Value)
    (hknown : OpeningKnown known ⟨(owner, left.pool.nextSerial owner), payload⟩) :
    KnowledgeRelated program known
      { left with pool := (left.pool.submit owner payload).2 }
      { right with pool := (right.pool.submit owner payload).2 } :=
  ⟨related.occupied, related.values, by rw [related.pool], related.events,
    related.receipts, related.openings.submit owner payload hknown⟩

theorem KnowledgeRelated.replay (related : KnowledgeRelated program known left right)
    (owner : Principal) (id : MessageId Principal) :
    KnowledgeRelated program known
      { left with pool := (left.pool.replay owner id).state }
      { right with pool := (right.pool.replay owner id).state } :=
  ⟨related.occupied, related.values, by rw [related.pool], related.events,
    related.receipts, related.openings.replay owner id⟩

theorem KnowledgeRelated.deliver (related : KnowledgeRelated program known left right)
    (owner : Principal) (id : MessageId Principal) :
    KnowledgeRelated program known
      { left with pool := (left.pool.deliver owner id).state }
      { right with pool := (right.pool.deliver owner id).state } :=
  ⟨related.occupied, related.values, by rw [related.pool], related.events,
    related.receipts, related.openings.deliver owner id⟩

theorem KnowledgeRelated.includePending (related : KnowledgeRelated program known left right)
    (id : MessageId Principal) :
    KnowledgeRelated program known
      ((program.messageApplication).includePending left id)
      ((program.messageApplication).includePending right id) := by
  have hsafe := related.openings.includePending id
  unfold MessageApplication.includePending MessagePool.includeApplication
  cases hl : left.pool.includePending id with
  | mk message pool =>
      have hr : right.pool.includePending id = ⟨message, pool⟩ := by
        rw [← related.pool]
        exact hl
      simp only [hr]
      have hsafePool : pool.Satisfies (OpeningKnown known) := by
        simpa only [hl] using hsafe
      cases message with
      | none =>
          exact ⟨related.occupied, related.values, rfl, related.events,
            related.receipts, hsafePool⟩
      | some message =>
          have hlookup : left.pool.lookup id = some message := by
            have hm := congrArg (fun result => result.message) hl
            cases hlookup : left.pool.lookup id <;>
              simp_all [MessagePool.includePending, MessagePool.Result.invalid]
          have hknown := related.openings.1 message (List.mem_of_find?_eq_some hlookup)
          have hvalid := related.validate_eq message hknown
          simp only [messageApplication]
          rw [hvalid]
          cases program.validateMessage? right.application.service
              right.application.events message <;>
            exact ⟨related.occupied, related.values, rfl, by simp [related.events],
              by simp [related.receipts], hsafePool⟩

end Interaction.SealedProgram
