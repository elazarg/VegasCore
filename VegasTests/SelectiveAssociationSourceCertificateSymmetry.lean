/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceSymmetry
import VegasTests.SelectiveAssociationNamedEvidence

/-! # Certificate behavior under the hidden-bit permutation

An earlier unauthenticated claim is kept literally unchanged. At the binding
response, the permutation changes only Alice's hidden choice and the value in
her certificate request. If that response supplies no genuine certificate,
its transmitted packet is unchanged as well.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Vegas.SourceProgram Interaction GameTheory.Math.Probability

theorem flipBinding_success (binding : PublicationResult Bool) (bit : Bool) :
    flipBinding binding = .success bit ↔ binding = .success (!bit) := by
  cases binding <;> simp [flipBinding]

theorem mayForward_of_no_certificates {Claim : Type} (state : State) (who : Player)
    (known : List (Message Player (Packet Claim)))
    (empty : ∀ message ∈ known, message.payload.evidence = ∅) (fact : NamedFact) :
    state.mayForward who known fact ↔ state.owns who fact := by
  constructor
  · rintro (owned | ⟨message, member, carried⟩)
    · exact owned
    · rw [empty message member] at carried
      exact False.elim (Finset.notMem_empty fact carried)
  · exact Or.inl

theorem owned_flip (binding : PublicationResult Bool) (visit : Option Event) (clock : Nat)
    (fact : NamedFact) :
    (State.mk (CorePath.alice (flipBinding binding)) visit clock).owns alice fact ↔
      (State.mk (CorePath.alice binding) visit clock).owns alice (flipFact fact) := by
  rw [owns_alice, owns_alice]
  by_cases name : fact.1 = 0
  · simp only [flipFact, name, ↓reduceIte, true_and, flipBinding_success]
  · simp only [flipFact, name, ↓reduceIte, and_false, false_and]

theorem requested_flip {Claim : Type} (submission : Submission Claim) (fact : NamedFact) :
    fact ∈ (flipSubmission submission).evidence.toFinset ↔
      flipFact fact ∈ submission.evidence.toFinset := by
  cases evidence : submission.evidence with
  | none => simp [flipSubmission, evidence]
  | some requested =>
      simp only [flipSubmission, evidence, Option.map_some, Option.toFinset_some,
        Finset.mem_singleton]
      constructor
      · intro same
        rw [same, flipFact_involutive]
      · intro same
        rw [← same, flipFact_involutive]

theorem certificates_flip {Claim : Type} (binding : PublicationResult Bool)
    (visit : Option Event) (clock : Nat) (known : List (Message Player (Packet Claim)))
    (empty : ∀ message ∈ known, message.payload.evidence = ∅)
    (submission : Submission Claim) (fact : NamedFact) :
    fact ∈ certificates (State.mk (CorePath.alice (flipBinding binding)) visit clock)
        alice known (flipSubmission submission) ↔
      flipFact fact ∈ certificates (State.mk (CorePath.alice binding) visit clock)
        alice known submission := by
  classical
  have name : (flipFact fact).1 = fact.1 := by simp only [flipFact]; split <;> rfl
  simp only [certificates, Finset.mem_union, Finset.mem_filter,
    mayForward_of_no_certificates _ _ known empty, requested_flip, owned_flip]
  by_cases opening : submission.kind = .open
  · simp only [flipSubmission, opening, ↓reduceIte, Finset.mem_filter, Finset.mem_univ,
      true_and, name]
  · simp only [flipSubmission, opening, ↓reduceIte, Finset.notMem_empty, or_false]

theorem certificates_flip_empty {Claim : Type} (binding : PublicationResult Bool)
    (visit : Option Event) (clock : Nat) (known : List (Message Player (Packet Claim)))
    (empty : ∀ message ∈ known, message.payload.evidence = ∅)
    (submission : Submission Claim)
    (uncertified : certificates (State.mk (CorePath.alice binding) visit clock)
      alice known submission = ∅) :
    certificates (State.mk (CorePath.alice (flipBinding binding)) visit clock)
      alice known (flipSubmission submission) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro fact certified
  have certified := (certificates_flip binding visit clock known empty submission fact).mp certified
  rw [uncertified] at certified
  exact Finset.notMem_empty _ certified

theorem packet_flip_of_uncertified {Claim : Type} (binding : PublicationResult Bool)
    (visit : Option Event) (clock : Nat) (known : List (Message Player (Packet Claim)))
    (empty : ∀ message ∈ known, message.payload.evidence = ∅)
    (submission : Submission Claim)
    (uncertified : certificates (State.mk (CorePath.alice binding) visit clock)
      alice known submission = ∅) :
    packet (State.mk (CorePath.alice (flipBinding binding)) visit clock)
        alice known (flipSubmission submission) =
      packet (State.mk (CorePath.alice binding) visit clock) alice known submission := by
  unfold packet
  rw [certificates_flip_empty binding visit clock known empty submission uncertified, uncertified]
  rfl

theorem certificates_of_initialCore {Claim : Type} (state : State)
    (core : state.core = initialCore) (who : Player)
    (known : List (Message Player (Packet Claim)))
    (empty : ∀ message ∈ known, message.payload.evidence = ∅)
    (submission : Submission Claim) : certificates state who known submission = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro fact certified
  have valid := (packetEvidence Claim).issued state who known submission
    (fun message member carried present => by
      change carried ∈ message.payload.evidence.toList at present
      rw [empty message member] at present
      simp only [Finset.toList_empty, List.not_mem_nil] at present)
    fact (Finset.mem_toList.mpr certified)
  change state.core.evidenceHolds sourceProgram fact.toSource at valid
  rw [core] at valid
  exact initial_no_evidence fact.toSource valid

theorem submit_alice_shape {Claim : Type} (clock : Nat) (submission : Submission Claim) :
    submit ⟨initialCore, some 0, clock⟩ alice submission =
      if submission.address = some 0 ∧ submission.kind = .bind then
        ⟨CorePath.alice submission.binding, some 0, clock⟩ else ⟨initialCore, some 0, clock⟩ := by
  have stage : coreStage initialCore = 0 := rfl
  cases address : submission.address with
  | none => simp [submit, address]
  | some event =>
      by_cases same : event = 0
      · subst event
        by_cases kind : submission.kind = .bind <;>
          simp [submit, address, kind, stage, eventOwner, bindingOwner, CorePath.initial_advance]
      · simp [submit, address, same]

theorem submit_alice_flip_public {Claim : Type} (clock : Nat) (submission : Submission Claim) :
    publicView (submit ⟨initialCore, some 0, clock⟩ alice (flipSubmission submission)) =
      publicView (submit ⟨initialCore, some 0, clock⟩ alice submission) := by
  rw [submit_alice_shape, submit_alice_shape]
  change publicView (if submission.address = some 0 ∧ submission.kind = .bind then _ else _) = _
  split <;> rfl

theorem packet_post_flip_of_uncertified {Claim : Type} (clock : Nat)
    (known : List (Message Player (Packet Claim)))
    (empty : ∀ message ∈ known, message.payload.evidence = ∅)
    (submission : Submission Claim)
    (uncertified : certificates (submit ⟨initialCore, some 0, clock⟩ alice submission)
      alice known submission = ∅) :
    packet (submit ⟨initialCore, some 0, clock⟩ alice (flipSubmission submission))
        alice known (flipSubmission submission) =
      packet (submit ⟨initialCore, some 0, clock⟩ alice submission) alice known submission := by
  rw [submit_alice_shape] at uncertified ⊢
  rw [submit_alice_shape]
  change packet (if submission.address = some 0 ∧ submission.kind = .bind then _ else _) _ _ _ = _
  by_cases accepted : submission.address = some 0 ∧ submission.kind = .bind
  · simp only [ite_eq_left accepted] at uncertified ⊢
    exact packet_flip_of_uncertified submission.binding (some 0) clock
      known empty submission uncertified
  · simp only [ite_eq_right accepted] at uncertified ⊢
    unfold packet
    rw [certificates_of_initialCore _ rfl alice known empty,
      certificates_of_initialCore _ rfl alice known empty]
    rfl

theorem certificates_congr_owned {Claim : Type} (first second : State) (who : Player)
    (known : List (Message Player (Packet Claim))) (submission : Submission Claim)
    (owned : ∀ fact, first.owns who fact ↔ second.owns who fact) :
    certificates first who known submission = certificates second who known submission := by
  classical
  simp only [certificates, State.mayForward, owned]

theorem submit_carol_shape {Claim : Type} (binding : PublicationResult Bool)
    (clock : Nat) (submission : Submission Claim) :
    submit ⟨CorePath.alice binding, some 1, clock⟩ carol submission =
      if submission.address = some 1 ∧ submission.kind = .bind then
        ⟨CorePath.carol binding submission.binding, some 1, clock⟩
      else ⟨CorePath.alice binding, some 1, clock⟩ := by
  have stage : coreStage (CorePath.alice binding) = 1 := rfl
  cases address : submission.address with
  | none => simp [submit, address]
  | some event =>
      by_cases same : event = 1
      · subst event
        by_cases kind : submission.kind = .bind <;>
          simp [submit, address, kind, stage, eventOwner, bindingOwner, CorePath.alice_advance]
      · simp [submit, address, same]

theorem packet_carol_independent {Claim : Type} (first second : PublicationResult Bool)
    (clock : Nat) (known : List (Message Player (Packet Claim))) (submission : Submission Claim) :
    packet (submit ⟨CorePath.alice first, some 1, clock⟩ carol submission)
        carol known submission =
      packet (submit ⟨CorePath.alice second, some 1, clock⟩ carol submission)
        carol known submission := by
  rw [submit_carol_shape, submit_carol_shape]
  unfold packet
  congr 1
  apply certificates_congr_owned
  intro fact
  split
  · exact carol_owns_independent first second submission.binding (some 1) clock fact
  · simp only [owns_alice, show carol ≠ alice by decide, false_and]

end VegasTests.SelectiveAssociation.NamedSource
