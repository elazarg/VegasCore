/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidateResolution
import Interaction.SealedResolutionAccepted

/-! # The prepared-message embedding of the two commitment hosts

The candidate host agrees with the registered-site host on prepared canonical
commitment submissions. This is a restriction on the messages used by the
embedding, not a restriction on the candidate runtime or its deviators.
Canonical acceptance provenance supplies the corresponding opening check.
-/

namespace Interaction.SealedProgram

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

/-- A submitted commitment names its sender's source-site handle and that
handle already has an opening. Other packets impose no preparation condition. -/
def PreparedSubmission (service : IdealCommitments Principal Nat Value)
    (message : Message Principal (Payload Principal Value)) : Prop :=
  ∀ node handle, message.payload = .commitment node handle →
    handle = (message.sender, node) ∧ (service.lookup handle).isSome = true

theorem PreparedSubmission.sealValue [DecidableEq Principal]
    {service : IdealCommitments Principal Nat Value}
    {message : Message Principal (Payload Principal Value)}
    (h : PreparedSubmission service message) (owner : Principal) (slot : Nat) (value : Value) :
    PreparedSubmission (service.sealValue owner slot value).state message := by
  intro node handle hpayload
  obtain ⟨hhandle, hprepared⟩ := h node handle hpayload
  refine ⟨hhandle, ?_⟩
  cases hlookup : service.lookup handle with
  | none => simp [hlookup] at hprepared
  | some stored =>
      rw [IdealCommitments.lookup_sealValue_of_eq_some service owner slot value
        handle stored hlookup]
      rfl

/-- On prepared source-site submissions, both validators have exactly the
same result. Accepted-handle provenance handles arbitrary opening attempts. -/
theorem candidateMessage?_prepared [DecidableEq Principal] [DecidableEq Value]
    (program : SealedProgram Principal) (service : IdealCommitments Principal Nat Value)
    (events : List (Event Principal Value))
    (hcanonical : ∀ node handle, accepted? events node = some handle → handle.2 = node)
    (message : Message Principal (Payload Principal Value))
    (hprepared : PreparedSubmission service message) :
    program.candidateMessage? service.candidates events message =
      (program.validateMessage? service events message).map (fun event =>
        (service.candidates, event)) := by
  cases hpayload : message.payload with
  | commitment node handle =>
      obtain ⟨hhandle, hoccupied⟩ := hprepared node handle hpayload
      simp only [candidateMessage?, validateMessage?, hpayload]
      cases hrule : program.rules[node]? with
      | none => rfl
      | some rule =>
          cases hkind : rule.kind with
          | reveal | disabled => simp only [hkind, Option.map_none]
          | commit owner =>
              simp only [hkind]
              have hchecks :
                  (message.sender = owner ∧ handle.1 = owner ∧ done events node = false ∧
                    prerequisitesDone events rule = true) ↔
                  (message.sender = owner ∧ handle = (owner, node) ∧
                    done events node = false ∧ prerequisitesDone events rule = true ∧
                    (service.lookup handle).isSome = true) := by
                constructor
                · rintro ⟨hsender, _, hdone, hready⟩
                  exact ⟨hsender, hhandle.trans (Prod.ext hsender rfl),
                    hdone, hready, hoccupied⟩
                · rintro ⟨hsender, hcanonicalHandle, hdone, hready, _⟩
                  exact ⟨hsender, congrArg Prod.fst hcanonicalHandle, hdone, hready⟩
              simp only [hchecks]
              split
              · simp [service.candidates_accept handle hoccupied]
              · rfl
  | opening node handle claimed =>
      simp only [candidateMessage?, validateMessage?, hpayload]
      cases hrule : program.rules[node]? with
      | none => rfl
      | some rule =>
          cases hkind : rule.kind with
          | commit | disabled => simp only [hkind, Option.map_none]
          | reveal owner source =>
              simp only [hkind]
              have hchecks :
                  (message.sender = owner ∧ handle.1 = owner ∧ done events node = false ∧
                    prerequisitesDone events rule = true ∧ accepted? events source = some handle ∧
                    service.candidates.verify handle claimed = true) ↔
                  (message.sender = owner ∧ handle = (owner, source) ∧
                    done events node = false ∧ prerequisitesDone events rule = true ∧
                    accepted? events source = some handle ∧
                    service.verify ⟨handle, claimed⟩ = true) := by
                rw [service.candidates_verify]
                constructor
                · rintro ⟨hsender, howner, hdone, hready, haccepted, hverify⟩
                  exact ⟨hsender, Prod.ext howner (hcanonical source handle haccepted),
                    hdone, hready, haccepted, hverify⟩
                · rintro ⟨hsender, hhandle, hrest⟩
                  exact ⟨hsender, congrArg Prod.fst hhandle, hrest⟩
              simp only [hchecks]
              split <;> rfl
  | cleartext | malformed => simp [candidateMessage?, validateMessage?, hpayload]

end Interaction.SealedProgram

namespace Interaction.SealedResolution

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

/-- Retype the private table, retaining every public event, timeout and clock. -/
def candidateState (state : ApplicationState Principal Value) :
    ApplicationState Principal Value (CommitmentCandidates Principal Nat Value) :=
  ⟨state.service.candidates, state.visible⟩

/-- Exact application-handler agreement for prepared source-site messages.
Resolution and all rejection receipts are preserved, not just valid openings. -/
theorem candidateHandle_prepared [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value) (state : ApplicationState Principal Value)
    (hinvariant : AcceptedBinding runtime state)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hprepared : SealedProgram.PreparedSubmission state.service message) :
    runtime.candidateHandle (candidateState state) message =
      (runtime.handle state message).map candidateState := by
  have hcanonical : ∀ node handle, SealedProgram.accepted? state.visible.events node = some handle →
      handle.2 = node := by
    intro node handle haccepted
    obtain ⟨owner, value, rule, hrule, hkind, hhandle, hlookup⟩ :=
      hinvariant.accepted node handle (SealedProgram.accepted_mem_of_accepted?_eq_some haccepted)
    exact congrArg Prod.snd hhandle
  simp only [candidateHandle, handle, validateMessage?, candidateState]
  split
  · rfl
  · rw [SealedProgram.candidateMessage?_prepared _ _ _ hcanonical message hprepared]
    cases (runtime.program.discharge state.visible.timeouts).validateMessage?
      state.service state.visible.events message <;> rfl

end Interaction.SealedResolution
