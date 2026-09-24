/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceOpeningOptimality

/-! # Payoffs of complete source opening continuations

At each opening response, every continuation policy is bounded by ordinary
opening. The bounds hold separately at every compatible concrete history;
they therefore do not require positive posterior probability at that history.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory.Math.Probability

theorem finish_alice_payoff_le {Claim : Type}
    (players : Player → (application Claim).Policy)
    (control : (application Claim).Control) (a c b : PublicationResult Bool)
    (core : control.execution.application.core = CorePath.bob a c b)
    (visited : control.execution.application.visit = some 3)
    (active : control.actor = some alice)
    (remaining : control.remaining = (afterResponse 3).length)
    (position : control.execution.environmentRecall.length = (beforeResponse 3).length + 1)
    (carolOpens : OpensAt players 4) (bobOpens : OpensAt players 5) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim) players
      (some control)).expect (fun state => utility (protocolResults state) alice) ≤
        utility ⟨a, b, c⟩ alice := by
  rw [← FinDist.expect_map (protocolResults (Claim := Claim)) _
      (fun result => utility result alice),
    finish_alice_results players control a c b core visited active remaining position
      carolOpens bobOpens, FinDist.expect_map]
  apply FinDist.expect_le_of_forall
  intro response _
  cases selectedDisclosure 3 response
  · simpa using (utility_alice_bounds ⟨a, b, c⟩).1
  · exact le_rfl

theorem finish_carol_payoff_le {Claim : Type}
    (players : Player → (application Claim).Policy)
    (control : (application Claim).Control) (a c b : PublicationResult Bool) (first : Bool)
    (core : control.execution.application.core = CorePath.openedAlice a c b first)
    (visited : control.execution.application.visit = some 4)
    (active : control.actor = some carol)
    (remaining : control.remaining = (afterResponse 4).length)
    (position : control.execution.environmentRecall.length = (beforeResponse 4).length + 1)
    (bobOpens : OpensAt players 5) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim) players
      (some control)).expect (fun state => utility (protocolResults state) carol) ≤
        utility ⟨if first then a else .failure, b, c⟩ carol := by
  rw [← FinDist.expect_map (protocolResults (Claim := Claim)) _
      (fun result => utility result carol),
    finish_carol_results players control a c b first core visited active remaining position
      bobOpens, FinDist.expect_map]
  apply FinDist.expect_le_of_forall
  intro response _
  cases selectedDisclosure 4 response
  · simpa using (utility_carol_bounds ⟨if first then a else .failure, b, c⟩).1
  · exact le_rfl

theorem finish_bob_payoff_le {Claim : Type}
    (players : Player → (application Claim).Policy)
    (control : (application Claim).Control) (a c b : PublicationResult Bool) (first second : Bool)
    (core : control.execution.application.core = CorePath.openedCarol a c b first second)
    (visited : control.execution.application.visit = some 5)
    (active : control.actor = some bob)
    (remaining : control.remaining = (afterResponse 5).length)
    (position : control.execution.environmentRecall.length = (beforeResponse 5).length + 1) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim) players
      (some control)).expect (fun state => utility (protocolResults state) bob) ≤
        utility ⟨if first then a else .failure, b, if second then c else .failure⟩ bob := by
  rw [← FinDist.expect_map (protocolResults (Claim := Claim)) _
      (fun result => utility result bob),
    finish_bob_results players control a c b first second core visited active remaining position,
    FinDist.expect_map]
  apply FinDist.expect_le_of_forall
  intro response _
  cases selectedDisclosure 5 response
  · simpa using (utility_bob_bounds
      ⟨if first then a else .failure, b, if second then c else .failure⟩).1
  · exact le_rfl

theorem finish_alice_opening_law {Claim : Type}
    (players : Player → (application Claim).Policy)
    (control : (application Claim).Control) (a c b : PublicationResult Bool)
    (core : control.execution.application.core = CorePath.bob a c b)
    (visited : control.execution.application.visit = some 3)
    (active : control.actor = some alice)
    (remaining : control.remaining = (afterResponse 3).length)
    (position : control.execution.environmentRecall.length = (beforeResponse 3).length + 1)
    (aliceOpens : OpensAt players 3) (carolOpens : OpensAt players 4)
    (bobOpens : OpensAt players 5) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim) players
      (some control)).map protocolResults = FinDist.pure ⟨a, b, c⟩ := by
  rw [finish_alice_results players control a c b core visited active remaining position
    carolOpens bobOpens]
  apply FinDist.eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨response, responseMem, rfl⟩ := FinDist.support_map .. ▸ supported
  simp only [aliceOpens _ _ visited response responseMem, ↓reduceIte, Set.mem_singleton_iff]

theorem finish_carol_opening_law {Claim : Type}
    (players : Player → (application Claim).Policy)
    (control : (application Claim).Control) (a c b : PublicationResult Bool) (first : Bool)
    (core : control.execution.application.core = CorePath.openedAlice a c b first)
    (visited : control.execution.application.visit = some 4)
    (active : control.actor = some carol)
    (remaining : control.remaining = (afterResponse 4).length)
    (position : control.execution.environmentRecall.length = (beforeResponse 4).length + 1)
    (carolOpens : OpensAt players 4) (bobOpens : OpensAt players 5) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim) players
      (some control)).map protocolResults =
        FinDist.pure ⟨if first then a else .failure, b, c⟩ := by
  rw [finish_carol_results players control a c b first core visited active remaining position
    bobOpens]
  apply FinDist.eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨response, responseMem, rfl⟩ := FinDist.support_map .. ▸ supported
  simp only [carolOpens _ _ visited response responseMem, ↓reduceIte, Set.mem_singleton_iff]

theorem finish_bob_opening_law {Claim : Type}
    (players : Player → (application Claim).Policy)
    (control : (application Claim).Control) (a c b : PublicationResult Bool) (first second : Bool)
    (core : control.execution.application.core = CorePath.openedCarol a c b first second)
    (visited : control.execution.application.visit = some 5)
    (active : control.actor = some bob)
    (remaining : control.remaining = (afterResponse 5).length)
    (position : control.execution.environmentRecall.length = (beforeResponse 5).length + 1)
    (bobOpens : OpensAt players 5) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim) players
      (some control)).map protocolResults =
        FinDist.pure ⟨if first then a else .failure, b, if second then c else .failure⟩ := by
  rw [finish_bob_results players control a c b first second core visited active remaining position]
  apply FinDist.eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨response, responseMem, rfl⟩ := FinDist.support_map .. ▸ supported
  simp only [bobOpens _ _ visited response responseMem, ↓reduceIte, Set.mem_singleton_iff]

end VegasTests.SelectiveAssociation.NamedSource
