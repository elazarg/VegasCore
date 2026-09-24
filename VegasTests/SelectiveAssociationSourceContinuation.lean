/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceEvaluation
import VegasTests.SelectiveAssociationPayoffs

/-! # Ordinary source openings and their complete service continuations -/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Vegas.SourceProgram Interaction GameTheory.Math.Probability

def visitInput {Claim : Type} (event : Event) (execution : (application Claim).Execution) :
    (application Claim).Execution :=
  effect (effect execution (.application (.grant event))) (.activate (eventOwner event))

private theorem visit_player_response {Claim : Type}
    (players : Player → (application Claim).Policy)
    (who : Player) (rest : List Instruction) (execution : (application Claim).Execution) :
    runInstructions players (.player who :: rest) execution =
      (players who ((effect execution (.activate who)).recall who)
        ((effect execution (.activate who)).observe (application Claim) who)).bind
          (fun response => runInstructions players rest
            ((effect execution (.activate who)).respond (application Claim) who response)) := by
  simp only [runInstructions, instruction, ReactiveApplication.dispatch, effect_law,
    FinDist.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume,
    ReactiveApplication.invoke, FinDist.bind_map]

theorem runInstructions_visit {Claim : Type} (players : Player → (application Claim).Policy)
    (event : Event) (rest : List Instruction) (execution : (application Claim).Execution) :
    runInstructions players (visit event ++ rest) execution =
      (players (eventOwner event) ((visitInput event execution).recall (eventOwner event))
        ((visitInput event execution).observe (application Claim) (eventOwner event))).bind
          (fun response => runInstructions players rest
            (remainingVisit event ((visitInput event execution).respond
              (application Claim) (eventOwner event) response))) := by
  simp only [visit, List.append_assoc, List.cons_append, List.nil_append]
  rw [runInstructions_application, visit_player_response]
  apply FinDist.bind_congr
  intro response _
  rw [runInstructions_record, runInstructions_ticks, runInstructions_application]
  rfl

theorem visitInput_core {Claim : Type} (event : Event) (execution : (application Claim).Execution) :
    (visitInput event execution).application.core = execution.application.core := rfl

theorem visitInput_visit {Claim : Type} (event : Event)
    (execution : (application Claim).Execution) :
    (visitInput event execution).application.visit = some event := rfl

def selectedDisclosure {Claim : Type} (event : Event)
    (response : (application Claim).Action) : Bool :=
  match response.transmission with
  | some (.submit submission) =>
      submission.address = some event ∧ submission.kind = .open
  | _ => false

theorem opening_response_core {Claim : Type} (event : Event)
    (execution : (application Claim).Execution) (response : (application Claim).Action)
    (visited : execution.application.visit = some event)
    (stage : (coreStage execution.application.core).val = event.val)
    (opening : 3 ≤ event.val) (next : Bool → SourceCore)
    (advances : ∀ binding disclose,
      coreAdvance execution.application.core binding disclose = next disclose)
    (nextStage : ∀ disclose, (coreStage (next disclose)).val ≠ event.val) :
    (remainingVisit event (execution.respond (application Claim) (eventOwner event)
      response)).application.core = next (selectedDisclosure event response) := by
  classical
  rw [remainingVisit_core, respond_application]
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => simpa only [selectedDisclosure, stage, ↓reduceIte] using advances .failure false
  | some transmission =>
      cases transmission with
      | replay =>
          simpa only [selectedDisclosure, stage, ↓reduceIte] using advances .failure false
      | submit submission =>
          cases address : submission.address with
          | none => simp [submit, visited, address, selectedDisclosure, stage, advances]
          | some target =>
              by_cases same : target = event
              · subst target
                cases kind : submission.kind <;>
                  simp [submit, visited, address, kind, selectedDisclosure, stage,
                    Nat.not_lt.mpr opening, opening, advances, nextStage]
              · simp [submit, visited, address, same, selectedDisclosure, stage, advances]

theorem alice_opening_response {Claim : Type}
    (execution : (application Claim).Execution) (response : (application Claim).Action)
    (visited : execution.application.visit = some 3) (a c b : PublicationResult Bool)
    (core : execution.application.core = CorePath.bob a c b) :
    (remainingVisit 3 (execution.respond (application Claim) alice response)).application.core =
      CorePath.openedAlice a c b (selectedDisclosure 3 response) := by
  apply opening_response_core 3 execution response visited
    (by rw [core]; rfl) (by decide) (CorePath.openedAlice a c b)
  · intro unused disclose
    rw [core, CorePath.bob_advance]
  · intro disclose
    change (4 : Nat) ≠ 3
    decide

theorem carol_opening_response {Claim : Type}
    (execution : (application Claim).Execution) (response : (application Claim).Action)
    (visited : execution.application.visit = some 4) (a c b : PublicationResult Bool)
    (first : Bool) (core : execution.application.core = CorePath.openedAlice a c b first) :
    (remainingVisit 4 (execution.respond (application Claim) carol response)).application.core =
      CorePath.openedCarol a c b first (selectedDisclosure 4 response) := by
  apply opening_response_core 4 execution response visited
    (by rw [core]; rfl) (by decide) (CorePath.openedCarol a c b first)
  · intro unused disclose
    rw [core, CorePath.aliceOpening_advance]
  · intro disclose
    change (5 : Nat) ≠ 4
    decide

theorem bob_opening_response {Claim : Type}
    (execution : (application Claim).Execution) (response : (application Claim).Action)
    (visited : execution.application.visit = some 5) (a c b : PublicationResult Bool)
    (first second : Bool)
    (core : execution.application.core = CorePath.openedCarol a c b first second) :
    (remainingVisit 5 (execution.respond (application Claim) bob response)).application.core =
      CorePath.final a c b first second (selectedDisclosure 5 response) := by
  apply opening_response_core 5 execution response visited
    (by rw [core]; rfl) (by decide) (CorePath.final a c b first second)
  · intro unused disclose
    rw [core, CorePath.carolOpening_advance]
  · intro disclose
    change (6 : Nat) ≠ 5
    decide

theorem final_results (state : State) (a c b : PublicationResult Bool)
    (first second third : Bool) (core : state.core = CorePath.final a c b first second third) :
    results state = ⟨if first then a else .failure, if third then b else .failure,
      if second then c else .failure⟩ := by
  simp only [results, core]
  cases a <;> cases c <;> cases b <;>
    cases first <;> cases second <;> cases third <;> rfl

theorem policy_discloses (Claim : Type) (defaultClaim : Claim) (event : Event)
    (opening : 3 ≤ event.val) (past : List (application Claim).PlayerEntry)
    (view : (application Claim).PlayerView) (visited : view.application.visit = some event)
    (response : (application Claim).Action)
    (supported : response ∈ (policy Claim defaultClaim (eventOwner event) past view).support) :
    selectedDisclosure event response = true := by
  have nonzero : event.val ≠ 0 := by omega
  simp only [policy, visited, ↓reduceIte, nonzero, FinDist.mem_support_pure] at supported
  subst response
  simp [selectedDisclosure, playing, Nat.not_lt.mpr opening]

def OpensAt {Claim : Type} (players : Player → (application Claim).Policy)
    (event : Event) : Prop :=
  ∀ past view, view.application.visit = some event →
    ∀ response ∈ (players (eventOwner event) past view).support,
      selectedDisclosure event response = true

theorem policy_opensAt (Claim : Type) (defaultClaim : Claim) (event : Event)
    (opening : 3 ≤ event.val) : OpensAt (policy Claim defaultClaim) event :=
  fun past view visited response supported =>
    policy_discloses Claim defaultClaim event opening past view visited response supported

theorem opening_visit_core {Claim : Type} (players : Player → (application Claim).Policy)
    (event : Event) (execution final : (application Claim).Execution)
    (stage : (coreStage execution.application.core).val = event.val)
    (opening : 3 ≤ event.val) (next : Bool → SourceCore)
    (advances : ∀ binding disclose,
      coreAdvance execution.application.core binding disclose = next disclose)
    (nextStage : ∀ disclose, (coreStage (next disclose)).val ≠ event.val)
    (supported : final ∈ (runInstructions players (visit event) execution).support) :
    ∃ disclose, final.application.core = next disclose ∧
      (OpensAt players event → disclose = true) := by
  rw [← List.append_nil (visit event), runInstructions_visit] at supported
  obtain ⟨response, responseMem, resultMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  cases FinDist.mem_support_pure.mp resultMem
  exact ⟨selectedDisclosure event response,
    opening_response_core event (visitInput event execution) response
      rfl stage opening next advances nextStage,
    fun opens => opens _ _ rfl response responseMem⟩

/-- Every continuation uses the actual optional ordinary disclosures. If a
player follows an opening policy at its visit, its corresponding flag is true. -/
theorem opening_results {Claim : Type} (players : Player → (application Claim).Policy)
    (execution final : (application Claim).Execution) (a c b : PublicationResult Bool)
    (core : execution.application.core = CorePath.bob a c b)
    (supported : final ∈ (runInstructions players
      (visit 3 ++ visit 4 ++ visit 5) execution).support) :
    ∃ first second third,
      results final.application = ⟨if first then a else .failure,
        if third then b else .failure, if second then c else .failure⟩ ∧
      (OpensAt players 3 → first = true) ∧
      (OpensAt players 4 → second = true) ∧
      (OpensAt players 5 → third = true) := by
  rw [List.append_assoc, runInstructions_append] at supported
  obtain ⟨firstState, firstMem, afterFirst⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨first, firstCore, firstOpens⟩ := opening_visit_core players 3 execution firstState
    (by rw [core]; rfl) (by decide) (CorePath.openedAlice a c b)
    (by intro unused disclose; rw [core, CorePath.bob_advance])
    (by intro disclose; change (4 : Nat) ≠ 3; decide) firstMem
  rw [runInstructions_append] at afterFirst
  obtain ⟨secondState, secondMem, afterSecond⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ afterFirst)
  obtain ⟨second, secondCore, secondOpens⟩ := opening_visit_core players 4 firstState secondState
    (by rw [firstCore]; rfl) (by decide) (CorePath.openedCarol a c b first)
    (by intro unused disclose; rw [firstCore, CorePath.aliceOpening_advance])
    (by intro disclose; change (5 : Nat) ≠ 4; decide) secondMem
  obtain ⟨third, finalCore, thirdOpens⟩ := opening_visit_core players 5 secondState final
    (by rw [secondCore]; rfl) (by decide) (CorePath.final a c b first second)
    (by intro unused disclose; rw [secondCore, CorePath.carolOpening_advance])
    (by intro disclose; change (6 : Nat) ≠ 5; decide) afterSecond
  exact ⟨first, second, third, final_results _ a c b first second third finalCore,
    firstOpens, secondOpens, thirdOpens⟩

theorem prescribed_opening_results (Claim : Type) (defaultClaim : Claim)
    (execution final : (application Claim).Execution) (a c b : PublicationResult Bool)
    (core : execution.application.core = CorePath.bob a c b)
    (supported : final ∈ (runInstructions (policy Claim defaultClaim)
      (visit 3 ++ visit 4 ++ visit 5) execution).support) :
    results final.application = ⟨a, b, c⟩ := by
  obtain ⟨first, second, third, result, firstOpens, secondOpens, thirdOpens⟩ :=
    opening_results (policy Claim defaultClaim) execution final a c b core supported
  simpa only [firstOpens (policy_opensAt Claim defaultClaim 3 (by decide)),
    secondOpens (policy_opensAt Claim defaultClaim 4 (by decide)),
    thirdOpens (policy_opensAt Claim defaultClaim 5 (by decide)), ↓reduceIte] using result

theorem prescribed_opening_law (Claim : Type) (defaultClaim : Claim)
    (execution : (application Claim).Execution) (a c b : PublicationResult Bool)
    (core : execution.application.core = CorePath.bob a c b) :
    (runInstructions (policy Claim defaultClaim) (visit 3 ++ visit 4 ++ visit 5) execution).map
      (fun final => results final.application) = FinDist.pure ⟨a, b, c⟩ := by
  apply FinDist.eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨final, finalMem, rfl⟩ := FinDist.support_map .. ▸ supported
  exact prescribed_opening_results Claim defaultClaim execution final a c b core finalMem

/-- An arbitrary whole continuation policy can only withhold its owner's
result when the other two players follow their ordinary opening policies. -/
theorem opening_deviation_bound {Claim : Type} (players : Player → (application Claim).Policy)
    (who : Player)
    (others : ∀ event : Event, 3 ≤ event.val → eventOwner event ≠ who → OpensAt players event)
    (execution final : (application Claim).Execution) (a c b : PublicationResult Bool)
    (core : execution.application.core = CorePath.bob a c b)
    (supported : final ∈ (runInstructions players
      (visit 3 ++ visit 4 ++ visit 5) execution).support) :
    utility (results final.application) who ≤ utility ⟨a, b, c⟩ who := by
  obtain ⟨first, second, third, result, firstOpens, secondOpens, thirdOpens⟩ :=
    opening_results players execution final a c b core supported
  fin_cases who
  · have secondEq := secondOpens (others 4 (by decide) (by decide))
    have thirdEq := thirdOpens (others 5 (by decide) (by decide))
    rw [result, secondEq, thirdEq]
    cases first
    · simpa using (utility_alice_bounds ⟨a, b, c⟩).1
    · exact le_rfl
  · have firstEq := firstOpens (others 3 (by decide) (by decide))
    have secondEq := secondOpens (others 4 (by decide) (by decide))
    rw [result, firstEq, secondEq]
    cases third
    · simpa using (utility_bob_bounds ⟨a, b, c⟩).1
    · exact le_rfl
  · have firstEq := firstOpens (others 3 (by decide) (by decide))
    have thirdEq := thirdOpens (others 5 (by decide) (by decide))
    rw [result, firstEq, thirdEq]
    cases second
    · simpa using (utility_carol_bounds ⟨a, b, c⟩).1
    · exact le_rfl

theorem opening_deviation_expect_le {Claim : Type}
    (players : Player → (application Claim).Policy) (who : Player)
    (others : ∀ event : Event, 3 ≤ event.val → eventOwner event ≠ who → OpensAt players event)
    (execution : (application Claim).Execution) (a c b : PublicationResult Bool)
    (core : execution.application.core = CorePath.bob a c b) :
    (runInstructions players (visit 3 ++ visit 4 ++ visit 5) execution).expect
        (fun final => utility (results final.application) who) ≤ utility ⟨a, b, c⟩ who := by
  apply FinDist.expect_le_of_forall
  intro final supported
  exact opening_deviation_bound players who others execution final a c b core supported

end VegasTests.SelectiveAssociation.NamedSource
