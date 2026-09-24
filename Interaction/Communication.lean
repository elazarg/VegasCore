/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.Information

/-! # Communication and transferable evidence

Claims and verifiable evidence are different semantic capabilities. A player
may make any claim, but may disclose evidence only when it already possesses
that evidence or has received it. Delivery changes observations, not the
underlying game state. No packet, ledger, fee, or commitment encoding appears
in this interface.

The transcript records semantic communications. It is not a player's scratch
memory: each player observes exactly its own transmissions and the messages
delivered to it. Public delivery and private delivery remain distinct.
-/

noncomputable section

namespace Interaction

namespace Communication

variable {Player Claim Evidence : Type}

inductive Audience (Player : Type) where
  | broadcast
  | direct (recipient : Player)
  deriving DecidableEq

inductive Content (Claim Evidence : Type) where
  | claim (text : Claim)
  | evidence (fact : Evidence)
  deriving DecidableEq

structure Message (Player Claim Evidence : Type) where
  sender : Player
  audience : Audience Player
  content : Content Claim Evidence
  deriving DecidableEq

def Message.Visible (message : Message Player Claim Evidence) (who : Player) : Prop :=
  message.sender = who ∨ message.audience = .broadcast ∨ message.audience = .direct who

abbrev Transcript (Player Claim Evidence : Type) := List (Message Player Claim Evidence)

open Classical in
def Transcript.observe (transcript : Transcript Player Claim Evidence) (who : Player) :
    Transcript Player Claim Evidence :=
  transcript.filter (fun message => message.Visible who)

@[simp] theorem Transcript.mem_observe (transcript : Transcript Player Claim Evidence)
    (who : Player) (message : Message Player Claim Evidence) :
    message ∈ transcript.observe who ↔ message ∈ transcript ∧ message.Visible who := by
  classical
  simp [observe]

@[simp] theorem Transcript.observe_append (left right : Transcript Player Claim Evidence)
    (who : Player) :
    (left ++ right).observe who = left.observe who ++ right.observe who := by
  classical
  simp [observe]

theorem Transcript.observe_append_invisible
    (transcript : Transcript Player Claim Evidence) (message : Message Player Claim Evidence)
    (who : Player) (hidden : ¬ message.Visible who) :
    (transcript ++ [message]).observe who = transcript.observe who := by
  classical
  simp [observe, hidden]

/-- Evidence already delivered to this player, including its own transmissions. -/
def Transcript.HasEvidence (transcript : Transcript Player Claim Evidence)
    (who : Player) (fact : Evidence) : Prop :=
  ∃ message ∈ transcript.observe who, message.content = .evidence fact

theorem Transcript.hasEvidence_append_left
    (left right : Transcript Player Claim Evidence) (who : Player) (fact : Evidence)
    (known : left.HasEvidence who fact) : (left ++ right).HasEvidence who fact := by
  obtain ⟨message, present, same⟩ := known
  exact ⟨message, by simp only [observe_append, List.mem_append]; exact Or.inl present, same⟩

theorem Transcript.hasEvidence_singleton
    (message : Message Player Claim Evidence) (who : Player) (fact : Evidence)
    (visible : message.Visible who) (same : message.content = .evidence fact) :
    Transcript.HasEvidence [message] who fact :=
  ⟨message, (mem_observe _ _ _).mpr ⟨by simp, visible⟩, same⟩

/-- A claim never supplies verifiable evidence, even if its text is true. -/
theorem Transcript.no_evidence_of_claims (transcript : Transcript Player Claim Evidence)
    (claims : ∀ message ∈ transcript, ∃ text, message.content = .claim text)
    (who : Player) (fact : Evidence) : ¬ transcript.HasEvidence who fact := by
  rintro ⟨message, present, same⟩
  obtain ⟨text, claimed⟩ := claims message ((mem_observe _ _ _).mp present).1
  rw [claimed] at same
  cases same

end Communication

open Communication

/-- Possession is an information-local capability. Soundness is an obligation
of the evidence service, rather than a restriction on which claims may be made. -/
structure EvidenceModel (Player : Type) (World : Type*) where
  Evidence : Type
  View : Player → Type*
  observe : (who : Player) → World → View who
  possesses : (who : Player) → View who → Evidence → Prop
  valid : World → Evidence → Prop
  sound : ∀ who world fact, possesses who (observe who world) fact → valid world fact

namespace EvidenceModel

variable {Player Claim : Type} {World : Type*} (model : EvidenceModel Player World)

/-- Received evidence is transferable. There is no analogous rule turning a
received claim into evidence. -/
def CanDisclose (world : World) (transcript : Transcript Player Claim model.Evidence)
    (who : Player) (fact : model.Evidence) : Prop :=
  model.possesses who (model.observe who world) fact ∨ transcript.HasEvidence who fact

def Admissible (world : World) (transcript : Transcript Player Claim model.Evidence)
    (message : Message Player Claim model.Evidence) : Prop :=
  match message.content with
  | .claim _ => True
  | .evidence fact => model.CanDisclose world transcript message.sender fact

def Sound (world : World) (transcript : Transcript Player Claim model.Evidence) : Prop :=
  ∀ message ∈ transcript, ∀ fact, message.content = .evidence fact → model.valid world fact

theorem sound_nil (world : World) : model.Sound world ([] : Transcript Player Claim _) := by
  simp [Sound]

theorem valid_of_hasEvidence (world : World) (transcript : Transcript Player Claim model.Evidence)
    (sound : model.Sound world transcript) (who : Player) (fact : model.Evidence)
    (known : transcript.HasEvidence who fact) : model.valid world fact := by
  obtain ⟨message, present, same⟩ := known
  exact sound message ((Transcript.mem_observe _ _ _).mp present).1 fact same

theorem valid_of_canDisclose (world : World)
    (transcript : Transcript Player Claim model.Evidence)
    (sound : model.Sound world transcript) (who : Player) (fact : model.Evidence)
    (allowed : model.CanDisclose world transcript who fact) : model.valid world fact := by
  rcases allowed with own | received
  · exact model.sound who world fact own
  · exact model.valid_of_hasEvidence world transcript sound who fact received

theorem sound_append_message (world : World)
    (transcript : Transcript Player Claim model.Evidence)
    (sound : model.Sound world transcript) (message : Message Player Claim model.Evidence)
    (allowed : model.Admissible world transcript message) :
    model.Sound world (transcript ++ [message]) := by
  intro other present fact same
  rcases List.mem_append.mp present with old | fresh
  · exact sound other old fact same
  · have equal : other = message := by simpa using fresh
    subst other
    have known : model.CanDisclose world transcript message.sender fact := by
      simpa only [Admissible, same] using allowed
    exact model.valid_of_canDisclose world transcript sound message.sender fact known

/-- Existing certificates remain sound across any world change that preserves
their propositions. A game adapter must prove this persistence condition. -/
theorem sound_mono (before after : World)
    (transcript : Transcript Player Claim model.Evidence)
    (sound : model.Sound before transcript)
    (persists : ∀ fact, model.valid before fact → model.valid after fact) :
    model.Sound after transcript :=
  fun message present fact same => persists fact (sound message present fact same)

/-- A received certificate fixes a fact at every world and sound transcript
compatible with the receiver's observation. This is the information-set
property needed before reasoning about any assessment's beliefs. -/
theorem valid_at_same_observation (world : World)
    (transcript : Transcript Player Claim model.Evidence)
    (sound : model.Sound world transcript) (who : Player)
    (observed : Transcript Player Claim model.Evidence)
    (same : transcript.observe who = observed) (fact : model.Evidence)
    (known : ∃ message ∈ observed, message.content = .evidence fact) :
    model.valid world fact := by
  apply model.valid_of_hasEvidence world transcript sound who fact
  simpa only [Transcript.HasEvidence, same] using known

end EvidenceModel
end Interaction
