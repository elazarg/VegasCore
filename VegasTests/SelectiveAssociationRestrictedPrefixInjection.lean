/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedPrefixAcceptance
import VegasTests.SelectiveAssociationRestrictedPrefixEvidence

/-! # The concrete hidden-candidate injection before each guess

The map changes Alice's two raw responses and keeps the other responses
literally fixed. Legal native histories supply the accepted-handle and evidence
conditions used by the operational symmetry lemmas. The resulting tuples have
the same guessing input and the opposite successful Alice binding.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted.PrefixSymmetry

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

theorem carol_related_of_accepted (players : Profile model.behavioralSignature)
    (responses : Prefix.CarolResponses)
    (supported : responses ∈ (Prefix.carolLaw (menu.decodeProfile (FinDist.pure nativeInitial)
      nativeHorizon scheduler players)).support)
    (selected : Handle nativeGraph) (owner : selected.1 = alice)
    (associated : (Prefix.carolInput responses).application.accepted aliceBindingRef.field =
      some selected) :
    Related selected (Prefix.carolInput responses)
      (Prefix.carolInput (flipCarol selected responses)) := by
  obtain ⟨trace⟩ := Prefix.alice_legal players _
    (Prefix.carol_support_prelude _ responses supported)
  have related := related_aliceSubmitted selected owner responses
  apply related_carolInput selected responses
  apply related_alice_inclusion selected _ _ related
  · exact responded_audit _ trace alice rfl responses.aliceBinding
  · exact alice_before_inclusion_empty responses
  · rw [← carolInput_accepted]
    exact associated

theorem carol_flip_facts (players : Profile model.behavioralSignature)
    (responses : Prefix.CarolResponses)
    (supported : responses ∈ (Prefix.carolLaw (menu.decodeProfile (FinDist.pure nativeInitial)
      nativeHorizon scheduler players)).support)
    (selected : Handle nativeGraph) (owner : selected.1 = alice)
    (associated : (Prefix.carolInput responses).application.accepted aliceBindingRef.field =
      some selected)
    (fixed : (Prefix.carolInput responses).application.candidates.lookup selected =
      .openable ⟨.bool, true⟩)
    (uncertified : publicGuess ((Prefix.carolInput responses).observe app carol) = false) :
    Related selected (Prefix.carolInput responses)
        (Prefix.carolInput (flipCarol selected responses)) ∧
      ((Prefix.carolInput (flipCarol selected responses)).recall carol,
          (Prefix.carolInput (flipCarol selected responses)).observe app carol) =
        ((Prefix.carolInput responses).recall carol,
          (Prefix.carolInput responses).observe app carol) := by
  obtain ⟨trace⟩ := Prefix.carol_legal players responses supported
  have related := carol_related_of_accepted players responses supported selected owner associated
  have unpublished := Prefix.uncertified_ledger _ trace selected associated fixed carol uncertified
  exact ⟨related, related_guesser_input selected owner _ _ related carol (Or.inr rfl)
    (Prefix.no_certificate_observed _ trace selected unpublished carol)⟩

theorem carolInput_granted (responses : Prefix.CarolResponses) :
    (Prefix.carolInput responses).application.serviceGrant = some carolBinding := by
  simp only [Prefix.carolInput, Prefix.environmentResult_grant, activate, granted]

theorem carol_alice_present (responses : Prefix.CarolResponses)
    (trace : arena.Trace (Prefix.carolControl responses)) :
    ((Prefix.carolInput responses).application.config.store aliceBindingRef.field).isSome = true :=
  ((Prefix.carolInput responses).application.config.output_available aliceBinding).mpr
    (earlier_completed carolBinding aliceBinding (by decide) _ trace rfl
      (carolInput_granted responses))

theorem bob_flip_facts (players : Profile model.behavioralSignature)
    (responses : Prefix.BobResponses)
    (supported : responses ∈ (Prefix.bobLaw (menu.decodeProfile (FinDist.pure nativeInitial)
      nativeHorizon scheduler players)).support)
    (selected : Handle nativeGraph) (owner : selected.1 = alice)
    (associated : (Prefix.bobInput responses).application.accepted aliceBindingRef.field =
      some selected)
    (fixed : (Prefix.bobInput responses).application.candidates.lookup selected =
      .openable ⟨.bool, true⟩)
    (uncertified : publicGuess ((Prefix.bobInput responses).observe app bob) = false) :
    ((Prefix.carolInput (flipCarol selected responses.beforeCarol)).recall carol,
        (Prefix.carolInput (flipCarol selected responses.beforeCarol)).observe app carol) =
      ((Prefix.carolInput responses.beforeCarol).recall carol,
        (Prefix.carolInput responses.beforeCarol).observe app carol) ∧
    Related selected (Prefix.bobInput responses)
        (Prefix.bobInput (flipBob selected responses)) ∧
      ((Prefix.bobInput (flipBob selected responses)).recall bob,
          (Prefix.bobInput (flipBob selected responses)).observe app bob) =
        ((Prefix.bobInput responses).recall bob,
          (Prefix.bobInput responses).observe app bob) := by
  have carolSupport := Prefix.bob_support_carol _ responses supported
  obtain ⟨carolTrace⟩ := Prefix.carol_legal players responses.beforeCarol carolSupport
  obtain ⟨bobTrace⟩ := Prefix.bob_legal players responses supported
  have acceptedBefore : (Prefix.carolInput responses.beforeCarol).application.accepted
      aliceBindingRef.field = some selected :=
    (afterCarol_accepted (Prefix.carolInput responses.beforeCarol) responses.carolBinding
      (carol_alice_present responses.beforeCarol carolTrace)).symm.trans associated
  have carolRelated := carol_related_of_accepted players responses.beforeCarol carolSupport
    selected owner acceptedBefore
  have unpublished := Prefix.uncertified_ledger _ bobTrace selected associated fixed bob uncertified
  have unpublishedBefore : ∀ sent ∈ (Prefix.carolInput responses.beforeCarol).network.ledger,
      ∀ fact, sent.payload.evidence = some fact → fact.handle ≠ selected :=
    fun sent member => unpublished sent (Prefix.bob_ledger_subset responses member)
  have unobserved := Prefix.no_certificate_observed _ carolTrace selected unpublishedBefore carol
  have unknown := Prefix.no_foreign_certificate_known _ carolTrace selected unpublishedBefore
    carol (owner ▸ (by decide : alice ≠ carol))
  have sameCarol := related_guesser_input selected owner _ _ carolRelated carol (Or.inr rfl)
    unobserved
  have submitted := related_carolSubmitted selected owner responses carolRelated unobserved unknown
  have included := related_carol_inclusion selected owner _ _ submitted
    (responded_audit _ carolTrace carol rfl responses.carolBinding)
  have bobRelated := related_bobInput selected responses included
  exact ⟨sameCarol, bobRelated,
    related_guesser_input selected owner _ _ bobRelated bob (Or.inl rfl)
      (Prefix.no_certificate_observed _ bobTrace selected unpublished bob)⟩

end VegasTests.SelectiveAssociation.Restricted.PrefixSymmetry
