/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.BindingDisposition
import Interaction.ConditionalPublication

/-! # Conditional publication after a public binding default

Opaque references use the commitment publication kernel. A public default
uses an authenticated cleartext request checked against the recorded value,
without consulting a verifier or manufacturing a handle. Both retain the
owner's decline option and permissionless expiry after the strict deadline.

The application supplies the recorded disposition and the continuation guard.
This classifier does not establish the authority to install a default, its
source meaning, or a strategic comparison of the two public dispositions.
-/

namespace Interaction.ConditionalPublication

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

/-- Remaining publication prerequisites once a public default is recorded.
The caller supplies that recorded value separately to the resolver. -/
def defaultReady (site : ConditionalPublication Principal) (done : Nat → Bool) : Bool :=
  !done site.choiceNode && !done site.publicationNode && site.requires.all done

/-- A public default can be voluntarily published by its owner as cleartext.
The recorded value is authoritative, irrespective of private preparations. -/
def resolveDefault? [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat) (stored : Value)
    (done : Nat → Bool) (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value)) : Option (Option Value) :=
  if !site.defaultReady done then none else
  match message.payload with
  | .cleartext claimed =>
      if message.sender = site.owner ∧ claimed = stored ∧ canOpen claimed then
        some (some claimed)
      else none
  | .decline => if message.sender = site.owner then some none else none
  | .expire => if site.deadline < now then some none else none
  | .opening _ _ | .malformed => none

/-- Dispatch on the actual accepted disposition. Public defaults never enter
the opaque verifier. An unresolved binding permits neither form of publication. -/
def resolveDisposition? [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat)
    (verify : IdealCommitments.Opening
      (Principal := Principal) (Slot := Nat) (Value := Value) → Bool)
    (accepted : Option (BindingDisposition (CommitmentHandle Principal Nat) Value))
    (done : Nat → Bool) (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value)) : Option (Option Value) :=
  match accepted with
  | none => none
  | some (.opaque handle) => site.resolve? now verify (some handle) done canOpen message
  | some (.publicDefault value) => site.resolveDefault? now value done canOpen message

/-- Every voluntary disposition-backed request is independent of the absolute
expiry deadline. This covers owner decline as well as successful publication;
only the explicit expiry payload observes the deadline. -/
theorem resolveDisposition_withDeadline_eq
    [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (deadline now : Nat)
    (verify : IdealCommitments.Opening
      (Principal := Principal) (Slot := Nat) (Value := Value) → Bool)
    (accepted : Option (BindingDisposition (CommitmentHandle Principal Nat) Value))
    (done : Nat → Bool) (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value))
    (hindependent : match message.payload with | .expire => False | _ => True) :
    ({ site with deadline }).resolveDisposition? now verify accepted done canOpen message =
      site.resolveDisposition? now verify accepted done canOpen message := by
  obtain ⟨id, payload⟩ := message
  cases accepted with
  | none => rfl
  | some disposition =>
      cases disposition with
      | «opaque» handle =>
          cases payload <;> simp_all [resolveDisposition?, resolve?, ready]
      | publicDefault value =>
          cases payload <;> simp_all [resolveDisposition?, resolveDefault?, defaultReady]

/-- Publication readiness retains the canonical-handle check for an opaque
binding; a public default needs only the remaining public prerequisites. -/
def readyDisposition [DecidableEq Principal]
    (site : ConditionalPublication Principal)
    (accepted : Option (BindingDisposition (CommitmentHandle Principal Nat) Value))
    (done : Nat → Bool) : Bool :=
  match accepted with
  | none => false
  | some (.opaque handle) => site.ready (some handle) done
  | some (.publicDefault _) => site.defaultReady done

theorem resolveDefault_cleartext [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat) (stored claimed : Value)
    (done : Nat → Bool) (canOpen : Value → Bool) (id : MessageId Principal) :
    site.resolveDefault? now stored done canOpen ⟨id, .cleartext claimed⟩ =
        some (some claimed) ↔
      site.defaultReady done = true ∧ id.1 = site.owner ∧ claimed = stored ∧
        canOpen claimed = true := by
  simp [resolveDefault?, Message.sender]

theorem resolveDefault_decline [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat) (stored : Value)
    (done : Nat → Bool) (canOpen : Value → Bool) (id : MessageId Principal) :
    site.resolveDefault? now stored done canOpen ⟨id, .decline⟩ = some none ↔
      site.defaultReady done = true ∧ id.1 = site.owner := by
  simp [resolveDefault?, Message.sender]

theorem resolveDefault_expire [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat) (stored : Value)
    (done : Nat → Bool) (canOpen : Value → Bool) (id : MessageId Principal) :
    site.resolveDefault? now stored done canOpen ⟨id, .expire⟩ = some none ↔
      site.defaultReady done = true ∧ site.deadline < now := by
  simp [resolveDefault?]

/-- Permissionless expiry applies to either admitted binding disposition. -/
theorem resolveDisposition_expire [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat)
    (verify : IdealCommitments.Opening
      (Principal := Principal) (Slot := Nat) (Value := Value) → Bool)
    (accepted : Option (BindingDisposition (CommitmentHandle Principal Nat) Value))
    (done : Nat → Bool) (canOpen : Value → Bool) (id : MessageId Principal) :
    site.resolveDisposition? now verify accepted done canOpen ⟨id, .expire⟩ = some none ↔
      site.readyDisposition accepted done = true ∧ site.deadline < now := by
  cases accepted with
  | none => simp [resolveDisposition?, readyDisposition]
  | some disposition =>
      cases disposition with
      | «opaque» handle =>
          exact site.resolve_expire now verify (some handle) done canOpen ⟨id, .expire⟩ rfl
      | publicDefault value => exact site.resolveDefault_expire now value done canOpen id

/-- Every successful default publication occurs while its public node pair and
all declared prerequisites are ready. -/
theorem resolveDefault_success_inversion [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat) (stored : Value)
    (done : Nat → Bool) (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value)) (result : Option Value)
    (hresolve : site.resolveDefault? now stored done canOpen message = some result) :
    site.defaultReady done = true := by
  cases hready : site.defaultReady done <;>
    simp [resolveDefault?, hready] at hresolve ⊢

/-- Accepted value publication equals the recorded fallback and obeys the
continuation guard. Declines, including timeouts, make no opening claim. -/
theorem resolveDefault_some [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat) (stored value : Value)
    (done : Nat → Bool) (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value))
    (hresult : site.resolveDefault? now stored done canOpen message = some (some value)) :
    value = stored ∧ canOpen value = true ∧ message.sender = site.owner := by
  cases hpayload : message.payload with
  | cleartext claimed =>
      simp only [resolveDefault?, hpayload] at hresult
      split at hresult <;> try contradiction
      split at hresult <;> try contradiction
      rename_i haccepted
      cases hresult
      exact ⟨haccepted.2.1, haccepted.2.2, haccepted.1⟩
  | opening handle claimed => simp [resolveDefault?, hpayload] at hresult
  | decline => simp [resolveDefault?, hpayload] at hresult
  | expire => simp [resolveDefault?, hpayload] at hresult
  | malformed => simp [resolveDefault?, hpayload] at hresult

/-- Every successful disposition-backed resolution occurs while the common
public readiness condition holds, independently of how the binding was
established. -/
theorem resolveDisposition_success_inversion
    [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat)
    (verify : IdealCommitments.Opening
      (Principal := Principal) (Slot := Nat) (Value := Value) → Bool)
    (accepted : Option (BindingDisposition (CommitmentHandle Principal Nat) Value))
    (done : Nat → Bool) (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value)) (result : Option Value)
    (hresolve : site.resolveDisposition? now verify accepted done canOpen message =
      some result) :
    site.defaultReady done = true := by
  cases accepted with
  | none => simp [resolveDisposition?] at hresolve
  | some disposition =>
      cases disposition with
      | «opaque» handle =>
          have hready := site.resolve_success_inversion now verify (some handle) done
            canOpen message result hresolve
          simp only [ConditionalPublication.ready, defaultReady, Bool.and_eq_true] at hready ⊢
          exact ⟨⟨hready.1.1.2, hready.1.2⟩, hready.2⟩
      | publicDefault stored =>
          exact site.resolveDefault_success_inversion now stored done canOpen message
            result hresolve

/-- A value published from either disposition satisfies the application-level
continuation predicate. This deliberately says nothing about private
verification in the public-default branch. -/
theorem resolveDisposition_some_canOpen
    [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat)
    (verify : IdealCommitments.Opening
      (Principal := Principal) (Slot := Nat) (Value := Value) → Bool)
    (accepted : Option (BindingDisposition (CommitmentHandle Principal Nat) Value))
    (done : Nat → Bool) (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value)) (value : Value)
    (hresolve : site.resolveDisposition? now verify accepted done canOpen message =
      some (some value)) :
    canOpen value = true := by
  cases accepted with
  | none => simp [resolveDisposition?] at hresolve
  | some disposition =>
      cases disposition with
      | «opaque» handle =>
          exact site.resolve_some_canOpen now verify (some handle) done canOpen message
            value hresolve
      | publicDefault stored =>
          exact (site.resolveDefault_some now stored value done canOpen message hresolve).2.1

/-- A published value carries exactly the evidence appropriate to its recorded
binding disposition. Opaque publication has canonical verifier evidence;
public-default publication equals the recorded value and never fabricates a
private handle. Both voluntary publication forms are owner-authored. -/
theorem resolveDisposition_some_evidence
    [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat)
    (verify : IdealCommitments.Opening
      (Principal := Principal) (Slot := Nat) (Value := Value) → Bool)
    (accepted : Option (BindingDisposition (CommitmentHandle Principal Nat) Value))
    (done : Nat → Bool) (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value)) (value : Value)
    (hresolve : site.resolveDisposition? now verify accepted done canOpen message =
      some (some value)) :
    message.sender = site.owner ∧
      ((accepted = some (.opaque (site.owner, site.sourceSlot)) ∧
          verify ⟨(site.owner, site.sourceSlot), value⟩ = true) ∨
        accepted = some (.publicDefault value)) := by
  cases accepted with
  | none => simp [resolveDisposition?] at hresolve
  | some disposition =>
      cases disposition with
      | «opaque» handle =>
          change site.resolve? now verify (some handle) done canOpen message =
            some (some value) at hresolve
          have hready := site.resolve_success_inversion now verify (some handle) done
            canOpen message (some value) hresolve
          have hhandle : handle = (site.owner, site.sourceSlot) := by
            simp only [ConditionalPublication.ready, Bool.and_eq_true] at hready
            simpa only [beq_iff_eq, Option.some.injEq] using hready.1.1.1
          have hverified := site.resolve_some_verified now verify (some handle) done
            canOpen message value hresolve
          have howner : message.sender = site.owner := by
            cases hpayload : message.payload with
            | opening actual claimed =>
                simp only [ConditionalPublication.resolve?, hpayload] at hresolve
                split at hresolve <;> try contradiction
                split at hresolve <;> try contradiction
                rename_i hopen
                cases hresolve
                exact hopen.1
            | decline => simp [ConditionalPublication.resolve?, hpayload] at hresolve
            | expire => simp [ConditionalPublication.resolve?, hpayload] at hresolve
            | cleartext clear => simp [ConditionalPublication.resolve?, hpayload] at hresolve
            | malformed => simp [ConditionalPublication.resolve?, hpayload] at hresolve
          subst handle
          exact ⟨howner, Or.inl ⟨rfl, hverified⟩⟩
      | publicDefault stored =>
          obtain ⟨hvalue, _hcanOpen, howner⟩ :=
            site.resolveDefault_some now stored value done canOpen message hresolve
          subst stored
          exact ⟨howner, Or.inr rfl⟩

theorem resolveDefault_opening_rejects [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat) (stored claimed : Value)
    (done : Nat → Bool) (canOpen : Value → Bool) (id : MessageId Principal)
    (handle : CommitmentHandle Principal Nat) :
    site.resolveDefault? now stored done canOpen ⟨id, .opening handle claimed⟩ = none := by
  simp [resolveDefault?]

/-- Completion prevents publication, decline, and expiry from resolving the
same endpoint again, including requests with different identities. -/
theorem resolveDefault_after_completion [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat) (stored : Value)
    (done : Nat → Bool) (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value))
    (hcomplete : done site.choiceNode = true ∨ done site.publicationNode = true) :
    site.resolveDefault? now stored done canOpen message = none := by
  rcases hcomplete with hcomplete | hcomplete <;>
    simp [resolveDefault?, defaultReady, hcomplete]

/-- Either completed publication node prevents every further resolution,
independently of the accepted binding disposition. -/
theorem resolveDisposition_after_completion [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat)
    (verify : IdealCommitments.Opening
      (Principal := Principal) (Slot := Nat) (Value := Value) → Bool)
    (accepted : Option (BindingDisposition (CommitmentHandle Principal Nat) Value))
    (done : Nat → Bool) (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value))
    (hcomplete : done site.choiceNode = true ∨ done site.publicationNode = true) :
    site.resolveDisposition? now verify accepted done canOpen message = none := by
  cases accepted with
  | none => rfl
  | some disposition =>
      cases disposition with
      | «opaque» handle =>
          rcases hcomplete with hcomplete | hcomplete <;>
            simp [resolveDisposition?, resolve?, ready, hcomplete]
      | publicDefault value =>
          exact site.resolveDefault_after_completion now value done canOpen message hcomplete

/-- A default's resolution is independent of the private verifier on every
payload, including malformed messages and attempted opaque openings. -/
theorem resolveDisposition_default_verifier_independent
    [DecidableEq Principal] [DecidableEq Value]
    (site : ConditionalPublication Principal) (now : Nat) (stored : Value)
    (first second : IdealCommitments.Opening
      (Principal := Principal) (Slot := Nat) (Value := Value) → Bool)
    (done : Nat → Bool) (canOpen : Value → Bool)
    (message : Message Principal (Payload Principal Value)) :
    site.resolveDisposition? now first (some (.publicDefault stored)) done canOpen message =
      site.resolveDisposition? now second (some (.publicDefault stored)) done canOpen message := rfl

end Interaction.ConditionalPublication

/-- info: 'Interaction.ConditionalPublication.resolveDefault_some' depends on axioms:
[propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ConditionalPublication.resolveDefault_some

/-- info: 'Interaction.ConditionalPublication.resolveDisposition_withDeadline_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ConditionalPublication.resolveDisposition_withDeadline_eq

/-- info: 'Interaction.ConditionalPublication.resolveDisposition_success_inversion' depends on axioms:
[propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ConditionalPublication.resolveDisposition_success_inversion

/-- info: 'Interaction.ConditionalPublication.resolveDisposition_some_evidence' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ConditionalPublication.resolveDisposition_some_evidence
