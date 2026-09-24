/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceOpeningTails

/-! # Complete source outcomes after each current opening response

Each statement starts at the actual pending player response. It retains any
response by that player and all its later communication, with ordinary
opening by the other players. Calendar recording and timeouts are executed.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory.Math.Probability

def protocolResults {Claim : Type} (state : (application Claim).ProtocolState) : Results :=
  state.elim ⟨.failure, .failure, .failure⟩ (fun control => results control.execution.application)

theorem alice_response_results {Claim : Type} (players : Player → (application Claim).Policy)
    (execution final : (application Claim).Execution) (response : (application Claim).Action)
    (a c b : PublicationResult Bool) (core : execution.application.core = CorePath.bob a c b)
    (visited : execution.application.visit = some 3)
    (carolOpens : OpensAt players 4) (bobOpens : OpensAt players 5)
    (supported : final ∈ (runInstructions players (afterResponse 3)
      (execution.respond (application Claim) alice response)).support) :
    results final.application = ⟨if selectedDisclosure 3 response then a else .failure, b, c⟩ := by
  rw [runInstructions_afterResponse] at supported
  change final ∈ (runInstructions players (visit 4 ++ visit 5)
    (remainingVisit 3 (execution.respond (application Claim) alice response))).support at supported
  have afterCore := alice_opening_response execution response visited a c b core
  obtain ⟨second, third, result, secondOpens, thirdOpens⟩ := carol_opening_results players
    _ final a c b (selectedDisclosure 3 response) afterCore supported
  simpa only [secondOpens carolOpens, thirdOpens bobOpens, ↓reduceIte] using result

theorem carol_response_results {Claim : Type} (players : Player → (application Claim).Policy)
    (execution final : (application Claim).Execution) (response : (application Claim).Action)
    (a c b : PublicationResult Bool) (first : Bool)
    (core : execution.application.core = CorePath.openedAlice a c b first)
    (visited : execution.application.visit = some 4) (bobOpens : OpensAt players 5)
    (supported : final ∈ (runInstructions players (afterResponse 4)
      (execution.respond (application Claim) carol response)).support) :
    results final.application = ⟨if first then a else .failure, b,
      if selectedDisclosure 4 response then c else .failure⟩ := by
  rw [runInstructions_afterResponse] at supported
  change final ∈ (runInstructions players (visit 5)
    (remainingVisit 4 (execution.respond (application Claim) carol response))).support at supported
  have afterCore := carol_opening_response execution response visited a c b first core
  obtain ⟨third, result, thirdOpens⟩ := bob_opening_results players _ final a c b first
    (selectedDisclosure 4 response) afterCore supported
  simpa only [thirdOpens bobOpens, ↓reduceIte] using result

theorem bob_response_results {Claim : Type} (players : Player → (application Claim).Policy)
    (execution final : (application Claim).Execution) (response : (application Claim).Action)
    (a c b : PublicationResult Bool) (first second : Bool)
    (core : execution.application.core = CorePath.openedCarol a c b first second)
    (visited : execution.application.visit = some 5)
    (supported : final ∈ (runInstructions players (afterResponse 5)
      (execution.respond (application Claim) bob response)).support) :
    results final.application = ⟨if first then a else .failure,
      if selectedDisclosure 5 response then b else .failure, if second then c else .failure⟩ := by
  rw [runInstructions_afterResponse] at supported
  change final ∈ (FinDist.pure
    (remainingVisit 5 (execution.respond (application Claim) bob response))).support at supported
  cases FinDist.mem_support_pure.mp supported
  exact final_results _ a c b first second (selectedDisclosure 5 response)
    (bob_opening_response execution response visited a c b first second core)

theorem finish_alice_results {Claim : Type} (players : Player → (application Claim).Policy)
    (control : (application Claim).Control) (a c b : PublicationResult Bool)
    (core : control.execution.application.core = CorePath.bob a c b)
    (visited : control.execution.application.visit = some 3)
    (active : control.actor = some alice)
    (remaining : control.remaining = (afterResponse 3).length)
    (position : control.execution.environmentRecall.length = (beforeResponse 3).length + 1)
    (carolOpens : OpensAt players 4) (bobOpens : OpensAt players 5) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim) players
      (some control)).map protocolResults =
        (players alice (control.execution.recall alice)
          (control.execution.observe (application Claim) alice)).map
            (fun response => (⟨if selectedDisclosure 3 response then a else .failure,
              b, c⟩ : Results)) := by
  rw [finish_response_law players 3 control active remaining position,
    FinDist.map_comp, FinDist.map_bind, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro response _
  apply FinDist.eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨final, finalMem, rfl⟩ := FinDist.support_map .. ▸ supported
  exact alice_response_results players control.execution final response a c b core
    visited carolOpens bobOpens finalMem

theorem finish_carol_results {Claim : Type} (players : Player → (application Claim).Policy)
    (control : (application Claim).Control) (a c b : PublicationResult Bool) (first : Bool)
    (core : control.execution.application.core = CorePath.openedAlice a c b first)
    (visited : control.execution.application.visit = some 4)
    (active : control.actor = some carol)
    (remaining : control.remaining = (afterResponse 4).length)
    (position : control.execution.environmentRecall.length = (beforeResponse 4).length + 1)
    (bobOpens : OpensAt players 5) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim) players
      (some control)).map protocolResults =
        (players carol (control.execution.recall carol)
          (control.execution.observe (application Claim) carol)).map
            (fun response => (⟨if first then a else .failure, b,
              if selectedDisclosure 4 response then c else .failure⟩ : Results)) := by
  rw [finish_response_law players 4 control active remaining position,
    FinDist.map_comp, FinDist.map_bind, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro response _
  apply FinDist.eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨final, finalMem, rfl⟩ := FinDist.support_map .. ▸ supported
  exact carol_response_results players control.execution final response a c b first core
    visited bobOpens finalMem

theorem finish_bob_results {Claim : Type} (players : Player → (application Claim).Policy)
    (control : (application Claim).Control) (a c b : PublicationResult Bool) (first second : Bool)
    (core : control.execution.application.core = CorePath.openedCarol a c b first second)
    (visited : control.execution.application.visit = some 5)
    (active : control.actor = some bob)
    (remaining : control.remaining = (afterResponse 5).length)
    (position : control.execution.environmentRecall.length = (beforeResponse 5).length + 1) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim) players
      (some control)).map protocolResults =
        (players bob (control.execution.recall bob)
          (control.execution.observe (application Claim) bob)).map
            (fun response => (⟨if first then a else .failure,
              if selectedDisclosure 5 response then b else .failure,
              if second then c else .failure⟩ : Results)) := by
  rw [finish_response_law players 5 control active remaining position,
    FinDist.map_comp, FinDist.map_bind, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro response _
  apply FinDist.eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨final, finalMem, rfl⟩ := FinDist.support_map .. ▸ supported
  exact bob_response_results players control.execution final response a c b first second core
    visited finalMem

end VegasTests.SelectiveAssociation.NamedSource
