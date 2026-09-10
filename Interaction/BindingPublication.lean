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
