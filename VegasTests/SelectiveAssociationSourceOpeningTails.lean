/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceContinuation

/-! # Source opening continuations after earlier publication choices -/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory.Math.Probability

theorem bob_opening_results {Claim : Type} (players : Player → (application Claim).Policy)
    (execution final : (application Claim).Execution) (a c b : PublicationResult Bool)
    (first second : Bool)
    (core : execution.application.core = CorePath.openedCarol a c b first second)
    (supported : final ∈ (runInstructions players (visit 5) execution).support) :
    ∃ third, results final.application = ⟨if first then a else .failure,
        if third then b else .failure, if second then c else .failure⟩ ∧
      (OpensAt players 5 → third = true) := by
  obtain ⟨third, finalCore, opens⟩ := opening_visit_core players 5 execution final
    (by rw [core]; rfl) (by decide) (CorePath.final a c b first second)
    (by intro unused disclose; rw [core, CorePath.carolOpening_advance])
    (by intro disclose; change (6 : Nat) ≠ 5; decide) supported
  exact ⟨third, final_results _ a c b first second third finalCore, opens⟩

theorem carol_opening_results {Claim : Type} (players : Player → (application Claim).Policy)
    (execution final : (application Claim).Execution) (a c b : PublicationResult Bool)
    (first : Bool) (core : execution.application.core = CorePath.openedAlice a c b first)
    (supported : final ∈ (runInstructions players (visit 4 ++ visit 5) execution).support) :
    ∃ second third, results final.application = ⟨if first then a else .failure,
        if third then b else .failure, if second then c else .failure⟩ ∧
      (OpensAt players 4 → second = true) ∧ (OpensAt players 5 → third = true) := by
  rw [runInstructions_append] at supported
  obtain ⟨middle, middleMem, finalMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨second, middleCore, secondOpens⟩ := opening_visit_core players 4 execution middle
    (by rw [core]; rfl) (by decide) (CorePath.openedCarol a c b first)
    (by intro unused disclose; rw [core, CorePath.aliceOpening_advance])
    (by intro disclose; change (5 : Nat) ≠ 4; decide) middleMem
  obtain ⟨third, result, thirdOpens⟩ :=
    bob_opening_results players middle final a c b first second middleCore finalMem
  exact ⟨second, third, result, secondOpens, thirdOpens⟩

/-- The evaluator after an actual pending response is exactly the remaining
calendar. The equality retains the whole final protocol state. -/
theorem finish_response_law {Claim : Type} (players : Player → (application Claim).Policy)
    (event : Event) (control : (application Claim).Control)
    (active : control.actor = some (eventOwner event))
    (remaining : control.remaining = (afterResponse event).length)
    (position : control.execution.environmentRecall.length = (beforeResponse event).length + 1) :
    (application Claim).finish (FinDist.pure initial) horizon (scheduler Claim) players
        (some control) =
      ((players (eventOwner event) (control.execution.recall (eventOwner event))
        (control.execution.observe (application Claim) (eventOwner event))).bind
          (fun response => runInstructions players (afterResponse event)
            (control.execution.respond (application Claim) (eventOwner event) response))).map
              (application Claim).finished := by
  simp only [ReactiveApplication.finish, active, ReactiveApplication.resume,
    ReactiveApplication.invoke, FinDist.bind_map, remaining]
  congr 1
  apply FinDist.bind_congr
  intro response _
  apply segment_rounds players (beforeResponse event ++ [.player (eventOwner event)])
    (afterResponse event) []
  · simpa only [List.append_nil, List.append_assoc, List.singleton_append] using
      response_split event
  · rw [(application Claim).respond_environmentRecall]
    simpa only [List.length_append, List.length_singleton] using position

end VegasTests.SelectiveAssociation.NamedSource
