/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceOpeningPayoffs

/-! # Complete source continuations from the guessing responses

The selected binding is determined by the full current response. All later
responses are retained, including silence and forwarding. The other guesser's
binding can be arbitrary: it has no effect on this guesser's utility.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory.Math.Probability

theorem binding_response_core {Claim : Type} (event : Event)
    (execution : (application Claim).Execution) (response : (application Claim).Action)
    (visited : execution.application.visit = some event)
    (stage : (coreStage execution.application.core).val = event.val)
    (binding : event.val < 3) (next : PublicationResult Bool → SourceCore)
    (advances : ∀ value disclose,
      coreAdvance execution.application.core value disclose = next value)
    (nextStage : ∀ value, (coreStage (next value)).val ≠ event.val) :
    (remainingVisit event (execution.respond (application Claim) (eventOwner event)
      response)).application.core = next (selectedBinding event response) := by
  classical
  rw [remainingVisit_core, respond_application]
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => simpa only [selectedBinding, stage, ↓reduceIte] using advances .failure false
  | some transmission =>
      cases transmission with
      | replay =>
          simpa only [selectedBinding, stage, ↓reduceIte] using advances .failure false
      | submit submission =>
          cases address : submission.address with
          | none => simp [submit, visited, address, selectedBinding, stage, advances]
          | some target =>
              by_cases same : target = event
              · subst target
                cases kind : submission.kind <;>
                  simp [submit, visited, address, kind, selectedBinding, stage,
                    Nat.not_le.mpr binding, binding, advances, nextStage]
              · simp [submit, visited, address, same, selectedBinding, stage, advances]

theorem alice_binding_response {Claim : Type}
    (execution : (application Claim).Execution) (response : (application Claim).Action)
    (visited : execution.application.visit = some 0)
    (core : execution.application.core = initialCore) :
    (remainingVisit 0 (execution.respond (application Claim) alice response)).application.core =
      CorePath.alice (selectedBinding 0 response) := by
  apply binding_response_core 0 execution response visited
    (by rw [core]; rfl) (by decide) CorePath.alice
  · intro value disclose
    rw [core, CorePath.initial_advance]
  · intro value
    change (1 : Nat) ≠ 0
    decide

theorem carol_binding_response {Claim : Type}
    (execution : (application Claim).Execution) (response : (application Claim).Action)
    (visited : execution.application.visit = some 1) (a : PublicationResult Bool)
    (core : execution.application.core = CorePath.alice a) :
    (remainingVisit 1 (execution.respond (application Claim) carol response)).application.core =
      CorePath.carol a (selectedBinding 1 response) := by
  apply binding_response_core 1 execution response visited
    (by rw [core]; rfl) (by decide) (CorePath.carol a)
  · intro value disclose
    rw [core, CorePath.alice_advance]
  · intro value
    change (2 : Nat) ≠ 1
    decide

theorem bob_binding_response {Claim : Type}
    (execution : (application Claim).Execution) (response : (application Claim).Action)
    (visited : execution.application.visit = some 2) (a c : PublicationResult Bool)
    (core : execution.application.core = CorePath.carol a c) :
    (remainingVisit 2 (execution.respond (application Claim) bob response)).application.core =
      CorePath.bob a c (selectedBinding 2 response) := by
  apply binding_response_core 2 execution response visited
    (by rw [core]; rfl) (by decide) (CorePath.bob a c)
  · intro value disclose
    rw [core, CorePath.carol_advance]
  · intro value
    change (3 : Nat) ≠ 2
    decide

theorem bob_binding_visit {Claim : Type} (players : Player → (application Claim).Policy)
    (execution final : (application Claim).Execution) (a c : PublicationResult Bool)
    (core : execution.application.core = CorePath.carol a c)
    (supported : final ∈ (runInstructions players (visit 2) execution).support) :
    ∃ b, final.application.core = CorePath.bob a c b := by
  rw [← List.append_nil (visit 2), runInstructions_visit] at supported
  obtain ⟨response, _, resultMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  cases FinDist.mem_support_pure.mp resultMem
  exact ⟨selectedBinding 2 response,
    bob_binding_response (visitInput 2 execution) response rfl a c core⟩

theorem bob_binding_response_results {Claim : Type}
    (players : Player → (application Claim).Policy)
    (execution final : (application Claim).Execution) (response : (application Claim).Action)
    (a c : PublicationResult Bool) (core : execution.application.core = CorePath.carol a c)
    (visited : execution.application.visit = some 2)
    (supported : final ∈ (runInstructions players (afterResponse 2)
      (execution.respond (application Claim) bob response)).support) :
    ∃ first second third,
      results final.application = ⟨if first then a else .failure,
        if third then selectedBinding 2 response else .failure,
        if second then c else .failure⟩ ∧
      (OpensAt players 3 → first = true) ∧
      (OpensAt players 4 → second = true) ∧
      (OpensAt players 5 → third = true) := by
  rw [runInstructions_afterResponse] at supported
  exact opening_results players _ final a c (selectedBinding 2 response)
    (bob_binding_response execution response visited a c core) supported

theorem carol_binding_response_results {Claim : Type}
    (players : Player → (application Claim).Policy)
    (execution final : (application Claim).Execution) (response : (application Claim).Action)
    (a : PublicationResult Bool) (core : execution.application.core = CorePath.alice a)
    (visited : execution.application.visit = some 1)
    (supported : final ∈ (runInstructions players (afterResponse 1)
      (execution.respond (application Claim) carol response)).support) :
    ∃ b first second third,
      results final.application = ⟨if first then a else .failure,
        if third then b else .failure, if second then selectedBinding 1 response else .failure⟩ ∧
      (OpensAt players 3 → first = true) ∧
      (OpensAt players 4 → second = true) ∧
      (OpensAt players 5 → third = true) := by
  rw [runInstructions_afterResponse] at supported
  change final ∈ (runInstructions players (visit 2 ++ (visit 3 ++ visit 4 ++ visit 5))
    (remainingVisit 1 (execution.respond (application Claim) carol response))).support at supported
  rw [runInstructions_append] at supported
  obtain ⟨afterBob, bobMem, restMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨b, bobCore⟩ := bob_binding_visit players _ afterBob a (selectedBinding 1 response)
    (carol_binding_response execution response visited a core) bobMem
  obtain ⟨first, second, third, result, firstOpens, secondOpens, thirdOpens⟩ :=
    opening_results players afterBob final a (selectedBinding 1 response) b bobCore restMem
  exact ⟨b, first, second, third, result, firstOpens, secondOpens, thirdOpens⟩

end VegasTests.SelectiveAssociation.NamedSource
