/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceGuessEquilibrium

/-! # Canonical source bindings at every legal opening decision

Uniform full-menu reachability classifies every legal history. None of these
facts assumes support under the proposed equilibrium or its limiting beliefs.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory GameTheory.Protocol GameTheory.Math.Probability

theorem beforeResponse_core {Claim : Type} (players : Player → (application Claim).Policy)
    (event : Event) (execution : (application Claim).Execution)
    (supported : execution ∈
      (runInstructions players (beforeResponse event) (root Claim)).support) :
    ∃ earlier ∈ (runInstructions players (before event.val) (root Claim)).support,
      execution.application.core = earlier.application.core := by
  rw [beforeResponse, runInstructions_append] at supported
  obtain ⟨earlier, earlierMem, moved⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  rw [runInstructions_application, runInstructions_nil, FinDist.mem_support_pure] at moved
  cases moved
  exact ⟨earlier, earlierMem, rfl⟩

theorem before_bob_core {Claim : Type} (players : Player → (application Claim).Policy)
    (execution : (application Claim).Execution)
    (supported : execution ∈ (runInstructions players (before 2) (root Claim)).support) :
    ∃ a c, execution.application.core = CorePath.carol a c := by
  have granted : effect execution (.application (.grant 2)) ∈
      (runInstructions players (beforeResponse 2) (root Claim)).support := by
    rw [beforeResponse, runInstructions_append, FinDist.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨execution, supported, ?_⟩
    rw [runInstructions_application, runInstructions_nil]
    exact FinDist.mem_support_pure.mpr rfl
  have activated : effect (effect execution (.application (.grant 2))) (.activate bob) ∈
      ((runInstructions players (beforeResponse 2) (root Claim)).map
        (fun current => effect current (.activate bob))).support := by
    rw [FinDist.support_map]
    exact ⟨_, granted, rfl⟩
  rw [bob_prefix_law, FinDist.support_map] at activated
  obtain ⟨sample, _, same⟩ := activated
  have core := congrArg (fun current : (application Claim).Execution =>
    current.application.core) same
  rw [bobInput_core] at core
  exact ⟨_, _, core.symm⟩

theorem before_aliceOpening_core {Claim : Type} (players : Player → (application Claim).Policy)
    (execution : (application Claim).Execution)
    (supported : execution ∈ (runInstructions players (before 3) (root Claim)).support) :
    ∃ a c b, execution.application.core = CorePath.bob a c b := by
  rw [show before 3 = before 2 ++ visit 2 from rfl, runInstructions_append] at supported
  obtain ⟨earlier, earlierMem, moved⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨a, c, core⟩ := before_bob_core players earlier earlierMem
  obtain ⟨b, result⟩ := bob_binding_visit players earlier execution a c core moved
  exact ⟨a, c, b, result⟩

theorem before_carolOpening_core {Claim : Type} (players : Player → (application Claim).Policy)
    (execution : (application Claim).Execution)
    (supported : execution ∈ (runInstructions players (before 4) (root Claim)).support) :
    ∃ a c b first, execution.application.core = CorePath.openedAlice a c b first := by
  rw [show before 4 = before 3 ++ visit 3 from rfl, runInstructions_append] at supported
  obtain ⟨earlier, earlierMem, moved⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨a, c, b, core⟩ := before_aliceOpening_core players earlier earlierMem
  obtain ⟨first, result, _⟩ := opening_visit_core players 3 earlier execution
    (by rw [core]; rfl) (by decide) (CorePath.openedAlice a c b)
    (by intro unused disclose; rw [core, CorePath.bob_advance])
    (by intro disclose; change (4 : Nat) ≠ 3; decide) moved
  exact ⟨a, c, b, first, result⟩

theorem before_bobOpening_core {Claim : Type} (players : Player → (application Claim).Policy)
    (execution : (application Claim).Execution)
    (supported : execution ∈ (runInstructions players (before 5) (root Claim)).support) :
    ∃ a c b first second,
      execution.application.core = CorePath.openedCarol a c b first second := by
  rw [show before 5 = before 4 ++ visit 4 from rfl, runInstructions_append] at supported
  obtain ⟨earlier, earlierMem, moved⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨a, c, b, first, core⟩ := before_carolOpening_core players earlier earlierMem
  obtain ⟨second, result, _⟩ := opening_visit_core players 4 earlier execution
    (by rw [core]; rfl) (by decide) (CorePath.openedCarol a c b first)
    (by intro unused disclose; rw [core, CorePath.aliceOpening_advance])
    (by intro disclose; change (5 : Nat) ≠ 4; decide) moved
  exact ⟨a, c, b, first, second, result⟩

theorem decision_before_core (Claim : Type) [Fintype Claim] (event : Event)
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (active : control.actor = some (eventOwner event))
    (granted : control.execution.application.visit = some event) :
    ∃ earlier ∈ (runInstructions (menu Claim).uniformResponses
        (before event.val) (root Claim)).support,
      control.execution.application.core = earlier.application.core := by
  obtain ⟨prior, priorMem, same⟩ := decision_predecessor Claim event control trace active granted
  obtain ⟨earlier, earlierMem, core⟩ :=
    beforeResponse_core (menu Claim).uniformResponses event prior priorMem
  exact ⟨earlier, earlierMem, (congrArg (fun current : (application Claim).Execution =>
    current.application.core) same).trans core⟩

theorem alice_opening_decision_core (Claim : Type) [Fintype Claim]
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (active : control.actor = some alice)
    (granted : control.execution.application.visit = some 3) :
    ∃ a c b, control.execution.application.core = CorePath.bob a c b := by
  obtain ⟨earlier, earlierMem, same⟩ := decision_before_core Claim 3 control trace active granted
  obtain ⟨a, c, b, core⟩ :=
    before_aliceOpening_core (menu Claim).uniformResponses earlier earlierMem
  exact ⟨a, c, b, same.trans core⟩

theorem carol_opening_decision_core (Claim : Type) [Fintype Claim]
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (active : control.actor = some carol)
    (granted : control.execution.application.visit = some 4) :
    ∃ a c b first, control.execution.application.core = CorePath.openedAlice a c b first := by
  obtain ⟨earlier, earlierMem, same⟩ := decision_before_core Claim 4 control trace active granted
  obtain ⟨a, c, b, first, core⟩ :=
    before_carolOpening_core (menu Claim).uniformResponses earlier earlierMem
  exact ⟨a, c, b, first, same.trans core⟩

theorem bob_opening_decision_core (Claim : Type) [Fintype Claim]
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (active : control.actor = some bob)
    (granted : control.execution.application.visit = some 5) :
    ∃ a c b first second,
      control.execution.application.core = CorePath.openedCarol a c b first second := by
  obtain ⟨earlier, earlierMem, same⟩ := decision_before_core Claim 5 control trace active granted
  obtain ⟨a, c, b, first, second, core⟩ :=
    before_bobOpening_core (menu Claim).uniformResponses earlier earlierMem
  exact ⟨a, c, b, first, second, same.trans core⟩

end VegasTests.SelectiveAssociation.NamedSource
