/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.CommitmentCandidates
import Interaction.SealedResolution

/-! # Acceptance-bound candidates in the resolving message runtime

The same sealed program and relative deadlines are hosted with an immutable
candidate catalog. Candidate identifiers are independent of program sites.
An owner may prepare several candidates, and a site accepts the first eligible
submitted handle. An unprepared handle is accepted as permanently unopenable;
its failed opening resolves through the ordinary deadline and default rules.

Acceptance atomically fixes the candidate's global verification meaning, so a
later preparation cannot change what the same handle means at another site.
Public acceptance does not test openability. Openings authenticate the rule
owner and refer to the source site's actual accepted handle.

This is an ideal functionality, not a cryptographic implementation. The shared
runner supplies player histories, public pending traffic, receipts, replay,
delivery, inclusion, and clocks. Neither player nor environment observations
expose the catalog. Service-dependent strategic refinement is a separate proof.

A pending handle may be privately prepared until its first acceptance. A
realization in which commitment contents are fixed at submission must establish
an embedding into this more permissive behavior; exact trace equivalence is
not asserted. The service also enforces owner-scoped candidate identities.
Authenticating a message sender alone does not establish that a concrete
commitment representation implements that owner-scoped interpretation.
-/

namespace Interaction.SealedProgram

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

/-- Authenticate and apply one message against independently prepared
candidates. Commitment acceptance updates the private catalog as well as
producing its public event. Malformed packets remain available but are rejected. -/
def candidateMessage? [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (Event Principal Value))
    (message : Message Principal (Payload Principal Value)) :
    Option (CommitmentCandidates Principal Nat Value × Event Principal Value) :=
  match message.payload with
  | .commitment node handle =>
      match program.rules[node]? with
      | some rule =>
          match rule.kind with
          | .commit owner =>
              if message.sender = owner ∧ handle.1 = owner ∧
                  done events node = false ∧ prerequisitesDone events rule = true then
                some (candidates.accept handle, .accepted node handle)
              else none
          | _ => none
      | none => none
  | .opening node handle claimed =>
      match program.rules[node]? with
      | some rule =>
          match rule.kind with
          | .reveal owner source =>
              if message.sender = owner ∧ handle.1 = owner ∧
                  done events node = false ∧ prerequisitesDone events rule = true ∧
                  accepted? events source = some handle ∧
                  candidates.verify handle claimed = true then
                some (candidates, .opened node claimed)
              else none
          | _ => none
      | none => none
  | .cleartext _ _ => none
  | .malformed => none

/-- Candidate acceptance depends on public authorization and readiness alone,
not on whether the selected candidate can be opened. -/
theorem candidateMessage?_commit [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (Event Principal Value)) (sender owner : Principal)
    (serial node : Nat) (handle : CommitmentHandle Principal Nat) (requires : List Nat)
    (hrule : program.rules[node]? = some ⟨.commit owner, requires⟩) :
    program.candidateMessage? candidates events ⟨(sender, serial), .commitment node handle⟩ =
      if sender = owner ∧ handle.1 = owner ∧ done events node = false ∧
          requires.all (done events) = true then
        some (candidates.accept handle, .accepted node handle)
      else none := by
  simp only [candidateMessage?, hrule, Message.sender, prerequisitesDone]

/-- Two catalogs, possibly disagreeing about every candidate's value and
openability, give the same public result for a commitment submission. -/
theorem candidateMessage?_commit_public_eq [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (left right : CommitmentCandidates Principal Nat Value)
    (events : List (Event Principal Value)) (sender : Principal)
    (serial node : Nat) (handle : CommitmentHandle Principal Nat) :
    (program.candidateMessage? left events ⟨(sender, serial), .commitment node handle⟩).map
        Prod.snd =
      (program.candidateMessage? right events ⟨(sender, serial), .commitment node handle⟩).map
        Prod.snd := by
  simp only [candidateMessage?]
  cases hrule : program.rules[node]? with
  | none => rfl
  | some rule =>
      cases hkind : rule.kind <;> simp only [hkind]
      split <;> rfl

/-- The selected handle is authenticated at the rule owner's opening
endpoint. An outsider cannot use its opening result to query another owner. -/
theorem candidateMessage?_opening_other_owner [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (Event Principal Value)) (sender : Principal)
    (serial node : Nat) (handle : CommitmentHandle Principal Nat) (claimed : Value)
    (howner : sender ≠ handle.1) :
    program.candidateMessage? candidates events
      ⟨(sender, serial), .opening node handle claimed⟩ = none := by
  simp only [candidateMessage?]
  cases hrule : program.rules[node]? with
  | none => rfl
  | some rule =>
      cases hkind : rule.kind with
      | commit | disabled => simp only [hkind]
      | reveal owner source =>
          simp only [hkind]
          apply if_neg
          intro h
          exact howner (h.1.trans h.2.1.symm)

/-- Successful candidate application either fixes a selected handle or checks
an opening without changing the catalog. -/
theorem candidateMessage?_effect [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal)
    (candidates : CommitmentCandidates Principal Nat Value)
    (events : List (SealedProgram.Event Principal Value))
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (result : CommitmentCandidates Principal Nat Value ×
      SealedProgram.Event Principal Value)
    (hresult : program.candidateMessage? candidates events message = some result) :
    (∃ node handle,
      message.payload = .commitment node handle ∧
        result = (candidates.accept handle, .accepted node handle)) ∨
    (∃ node handle claimed,
      message.payload = .opening node handle claimed ∧
        result = (candidates, .opened node claimed)) := by
  unfold SealedProgram.candidateMessage? at hresult
  cases hpayload : message.payload with
  | commitment node handle =>
      simp only [hpayload] at hresult
      cases hrule : program.rules[node]? with
      | none => simp only [hrule] at hresult; contradiction
      | some rule =>
          simp only [hrule] at hresult
          cases hkind : rule.kind with
          | commit owner =>
              simp only [hkind] at hresult
              split at hresult
              · cases hresult
                exact Or.inl ⟨node, handle, rfl, rfl⟩
              · contradiction
          | reveal | disabled => simp only [hkind] at hresult; contradiction
  | opening node handle claimed =>
      simp only [hpayload] at hresult
      cases hrule : program.rules[node]? with
      | none => simp only [hrule] at hresult; contradiction
      | some rule =>
          simp only [hrule] at hresult
          cases hkind : rule.kind with
          | reveal owner source =>
              simp only [hkind] at hresult
              split at hresult
              · cases hresult
                exact Or.inr ⟨node, handle, claimed, rfl, rfl⟩
              · contradiction
          | commit | disabled => simp only [hkind] at hresult; contradiction
  | cleartext node value => simp only [hpayload] at hresult; contradiction
  | malformed => simp only [hpayload] at hresult; contradiction

end Interaction.SealedProgram

namespace Interaction.SealedResolution

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

/-- Candidate preparation starts empty, with exactly the same public
readiness timestamps and clock as the registered-site interpretation. -/
def candidateInitial (runtime : SealedResolution Principal Value) :
    ApplicationState Principal Value (CommitmentCandidates Principal Nat Value) :=
  ⟨CommitmentCandidates.empty, runtime.refresh false {}⟩

/-- Apply an authenticated candidate message and refresh the same public
deadline state. A timed-out node cannot subsequently accept a message. -/
def candidateHandle [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value (CommitmentCandidates Principal Nat Value))
    (message : Message Principal (SealedProgram.Payload Principal Value)) :
    Option (ApplicationState Principal Value (CommitmentCandidates Principal Nat Value)) := do
  if message.payload.node?.any state.visible.timeouts.contains then none
  else
    let result ← (runtime.program.discharge state.visible.timeouts).candidateMessage?
      state.service state.visible.events message
    some ⟨result.1, runtime.refresh false
      { state.visible with events := state.visible.events ++ [result.2] }⟩

/-- Restricting admission may reject more messages, but every successful
application retains exactly the authenticated candidate transition. This
condition concerns successful effects, not the information disclosed by rejection. -/
def CandidateHandlerSound [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (applyMessage : ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value) →
      Message Principal (SealedProgram.Payload Principal Value) →
      Option (ApplicationState Principal Value (CommitmentCandidates Principal Nat Value))) :
    Prop :=
  ∀ state message next, applyMessage state message = some next →
    runtime.candidateHandle state message = some next

theorem candidateHandle_sound [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value) :
    runtime.CandidateHandlerSound runtime.candidateHandle := fun _ _ _ h => h

/-- Candidate preparation and the ordinary resolution runner, parameterized
only by message admission. Every instance has the same policy interface. -/
noncomputable abbrev candidateHost [DecidableEq Principal]
    (runtime : SealedResolution Principal Value)
    (applyMessage : ApplicationState Principal Value
      (CommitmentCandidates Principal Nat Value) →
      Message Principal (SealedProgram.Payload Principal Value) →
      Option (ApplicationState Principal Value (CommitmentCandidates Principal Nat Value))) :
    MessageApplication Principal :=
  runtime.host (Service := CommitmentCandidates Principal Nat Value)
    (fun state owner slot value => state.prepare owner slot value) applyMessage

/-- The candidate service with authenticated, otherwise unrestricted openings. -/
noncomputable def candidateApplication [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value) : MessageApplication Principal :=
  runtime.host (Service := CommitmentCandidates Principal Nat Value)
    (fun state owner slot value => state.prepare owner slot value) runtime.candidateHandle

end Interaction.SealedResolution
