/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourcePublicGuess

/-! # Alice cannot separate the prescribed source guesses

This is a whole-policy bound. Alice can send arbitrary earlier traffic, choose
either binding or failure, and change every later response. The two prescribed
guessers still choose the same bit, and Alice can only reduce her payoff by
withholding her ordinary opening.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory.Math.Probability

theorem remainingVisit_serials {Claim : Type} (event : Event)
    (execution : (application Claim).Execution) (serials : execution.network.SerialsBeforeNext) :
    (remainingVisit event execution).network.SerialsBeforeNext := by
  rw [remainingVisit_network]
  exact effect_serials execution _ serials

theorem visitInput_serials {Claim : Type} (event : Event)
    (execution : (application Claim).Execution) (serials : execution.network.SerialsBeforeNext) :
    (visitInput event execution).network.SerialsBeforeNext :=
  effect_serials _ _ (effect_serials execution _ serials)

theorem respond_serials {Claim : Type} (execution : (application Claim).Execution)
    (who : Player) (response : (application Claim).Action)
    (serials : execution.network.SerialsBeforeNext) :
    (execution.respond (application Claim) who response).network.SerialsBeforeNext :=
  ((application Claim).serialsBeforeNextInvariant (scheduler Claim)).respond
    execution who response serials

theorem opensAt_of_policy {Claim : Type} (defaultClaim : Claim)
    (players : Player → (application Claim).Policy) (event : Event) (opening : 3 ≤ event.val)
    (same : players (eventOwner event) = policy Claim defaultClaim (eventOwner event)) :
    OpensAt players event := by
  intro past view visited response supported
  rw [same] at supported
  exact policy_discloses Claim defaultClaim event opening past view visited response supported

theorem prescribed_guessers_bind_same {Claim : Type} (defaultClaim : Claim)
    (players : Player → (application Claim).Policy)
    (carolPolicy : players carol = policy Claim defaultClaim carol)
    (bobPolicy : players bob = policy Claim defaultClaim bob)
    (execution final : (application Claim).Execution) (a : PublicationResult Bool)
    (core : execution.application.core = CorePath.alice a)
    (serials : execution.network.SerialsBeforeNext)
    (supported : final ∈ (runInstructions players (visit 1 ++ visit 2) execution).support) :
    final.application.core = CorePath.bob a
      (.success (publicGuess (execution.observe (application Claim) carol)))
      (.success (publicGuess (execution.observe (application Claim) carol))) := by
  rw [runInstructions_visit] at supported
  obtain ⟨carolResponse, carolMem, restMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  rw [show eventOwner 1 = carol from rfl, carolPolicy] at carolMem
  have carolSelected := policy_selected_guess Claim defaultClaim 1 (Or.inl rfl) _ _
    (visitInput_visit 1 execution) carolResponse carolMem
  have sameGuess := carol_prescribed_publicGuess Claim defaultClaim (visitInput 1 execution)
    (visitInput_serials 1 execution serials) rfl carolResponse carolMem
  have carolCore := carol_binding_response (visitInput 1 execution) carolResponse rfl a core
  rw [← List.append_nil (visit 2), runInstructions_visit] at restMem
  obtain ⟨bobResponse, bobMem, finalMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ restMem)
  rw [show eventOwner 2 = bob from rfl, bobPolicy] at bobMem
  let afterCarol := remainingVisit 1
    ((visitInput 1 execution).respond (application Claim) carol carolResponse)
  have bobSelected := policy_selected_guess Claim defaultClaim 2 (Or.inr rfl)
    ((visitInput 2 afterCarol).recall bob)
    ((visitInput 2 afterCarol).observe (application Claim) bob) rfl bobResponse bobMem
  cases FinDist.mem_support_pure.mp finalMem
  have bobCore := bob_binding_response (visitInput 2 afterCarol) bobResponse rfl a _ carolCore
  change (remainingVisit 2 ((visitInput 2 afterCarol).respond
    (application Claim) bob bobResponse)).application.core = _
  rw [bobCore, carolSelected, bobSelected]
  change CorePath.bob a
    (.success (publicGuess ((visitInput 1 execution).observe (application Claim) carol)))
    (.success (publicGuess ((visitInput 2 (remainingVisit 1
      ((visitInput 1 execution).respond (application Claim) carol carolResponse))).observe
        (application Claim) bob))) = _
  rw [sameGuess]
  rfl

theorem alice_after_binding_payoff_le {Claim : Type} (defaultClaim : Claim)
    (players : Player → (application Claim).Policy)
    (carolPolicy : players carol = policy Claim defaultClaim carol)
    (bobPolicy : players bob = policy Claim defaultClaim bob)
    (execution final : (application Claim).Execution) (a : PublicationResult Bool)
    (core : execution.application.core = CorePath.alice a)
    (serials : execution.network.SerialsBeforeNext)
    (supported : final ∈ (runInstructions players
      (visit 1 ++ visit 2 ++ visit 3 ++ visit 4 ++ visit 5) execution).support) :
    utility (results final.application) alice ≤ 0 := by
  rw [List.append_assoc (visit 1 ++ visit 2),
    List.append_assoc (visit 1 ++ visit 2), runInstructions_append] at supported
  obtain ⟨afterGuesses, guessesMem, openingMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  let guess := publicGuess (execution.observe (application Claim) carol)
  have boundCore := prescribed_guessers_bind_same defaultClaim players
    carolPolicy bobPolicy execution afterGuesses a core serials guessesMem
  have others : ∀ event : Event, 3 ≤ event.val → eventOwner event ≠ alice →
      OpensAt players event := by
    intro event late other
    fin_cases event <;> norm_num at late
    · exact False.elim (other rfl)
    · exact opensAt_of_policy defaultClaim players 4 (by decide) carolPolicy
    · exact opensAt_of_policy defaultClaim players 5 (by decide) bobPolicy
  have bound := opening_deviation_bound players alice others afterGuesses final
    a (.success guess) (.success guess) boundCore openingMem
  have zero : utility ⟨a, .success guess, .success guess⟩ alice ≤ 0 := by
    cases a <;> simp [utility_alice]
  exact bound.trans zero

theorem alice_after_binding_payoff_eq (Claim : Type) (defaultClaim : Claim)
    (execution final : (application Claim).Execution) (bit : Bool)
    (core : execution.application.core = CorePath.alice (.success bit))
    (serials : execution.network.SerialsBeforeNext)
    (supported : final ∈ (runInstructions (policy Claim defaultClaim)
      (visit 1 ++ visit 2 ++ visit 3 ++ visit 4 ++ visit 5) execution).support) :
    utility (results final.application) alice = 0 := by
  rw [List.append_assoc (visit 1 ++ visit 2),
    List.append_assoc (visit 1 ++ visit 2), runInstructions_append] at supported
  obtain ⟨afterGuesses, guessesMem, openingMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  let guess := publicGuess (execution.observe (application Claim) carol)
  have boundCore := prescribed_guessers_bind_same defaultClaim
    (policy Claim defaultClaim) rfl rfl execution afterGuesses (.success bit)
    core serials guessesMem
  rw [prescribed_opening_results Claim defaultClaim afterGuesses final (.success bit)
    (.success guess) (.success guess) boundCore openingMem]
  simp [utility_alice]

theorem alice_binding_response_payoff_le {Claim : Type} (defaultClaim : Claim)
    (players : Player → (application Claim).Policy)
    (carolPolicy : players carol = policy Claim defaultClaim carol)
    (bobPolicy : players bob = policy Claim defaultClaim bob)
    (execution final : (application Claim).Execution) (response : (application Claim).Action)
    (core : execution.application.core = initialCore)
    (visited : execution.application.visit = some 0)
    (serials : execution.network.SerialsBeforeNext)
    (supported : final ∈ (runInstructions players (afterResponse 0)
      (execution.respond (application Claim) alice response)).support) :
    utility (results final.application) alice ≤ 0 := by
  rw [runInstructions_afterResponse] at supported
  exact alice_after_binding_payoff_le defaultClaim players carolPolicy bobPolicy _ final
    (selectedBinding 0 response) (alice_binding_response execution response visited core)
    (remainingVisit_serials 0 _ (respond_serials execution alice response serials)) supported

theorem finish_alice_binding_payoff_le {Claim : Type} (defaultClaim : Claim)
    (players : Player → (application Claim).Policy)
    (carolPolicy : players carol = policy Claim defaultClaim carol)
    (bobPolicy : players bob = policy Claim defaultClaim bob)
    (control : (application Claim).Control)
    (core : control.execution.application.core = initialCore)
    (visited : control.execution.application.visit = some 0)
    (serials : control.execution.network.SerialsBeforeNext)
    (active : control.actor = some alice)
    (remaining : control.remaining = (afterResponse 0).length)
    (position : control.execution.environmentRecall.length = (beforeResponse 0).length + 1) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim) players
      (some control)).expect (fun state => utility (protocolResults state) alice) ≤ 0 := by
  rw [finish_response_law players 0 control active remaining position,
    FinDist.expect_map, FinDist.expect_bind]
  apply FinDist.expect_le_of_forall
  intro response _
  apply FinDist.expect_le_of_forall
  intro final supported
  exact alice_binding_response_payoff_le defaultClaim players carolPolicy bobPolicy
    control.execution final response core visited serials supported

end VegasTests.SelectiveAssociation.NamedSource
