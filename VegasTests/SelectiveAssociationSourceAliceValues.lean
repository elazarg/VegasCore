/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceAlicePayoffs
import VegasTests.SelectiveAssociationSourcePreludeControls

/-! # Alice's prescribed value and arbitrary ambient deviations -/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory.Math.Probability

theorem policy_alice_binding_success (Claim : Type) (defaultClaim : Claim)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (visited : view.application.visit = some 0) (response : (application Claim).Action)
    (supported : response ∈ (policy Claim defaultClaim alice past view).support) :
    ∃ bit, selectedBinding 0 response = .success bit := by
  change response ∈ (policy Claim defaultClaim (eventOwner 0) past view).support at supported
  simp only [policy, visited, ↓reduceIte, Fin.val_zero] at supported
  obtain ⟨bit, _, rfl⟩ := FinDist.support_map .. ▸ supported
  exact ⟨bit, by simp [selectedBinding, playing]⟩

theorem alice_binding_response_payoff_eq (Claim : Type) (defaultClaim : Claim)
    (execution final : (application Claim).Execution) (response : (application Claim).Action)
    (core : execution.application.core = initialCore)
    (visited : execution.application.visit = some 0)
    (serials : execution.network.SerialsBeforeNext)
    (responseMem : response ∈ (policy Claim defaultClaim alice (execution.recall alice)
      (execution.observe (application Claim) alice)).support)
    (supported : final ∈ (runInstructions (policy Claim defaultClaim) (afterResponse 0)
      (execution.respond (application Claim) alice response)).support) :
    utility (results final.application) alice = 0 := by
  obtain ⟨bit, selected⟩ := policy_alice_binding_success Claim defaultClaim _ _ visited
    response responseMem
  rw [runInstructions_afterResponse] at supported
  have boundCore := alice_binding_response execution response visited core
  rw [selected] at boundCore
  exact alice_after_binding_payoff_eq Claim defaultClaim _ final bit boundCore
    (remainingVisit_serials 0 _ (respond_serials execution alice response serials)) supported

theorem finish_alice_prescribed_binding (Claim : Type) (defaultClaim : Claim)
    (control : (application Claim).Control)
    (core : control.execution.application.core = initialCore)
    (visited : control.execution.application.visit = some 0)
    (serials : control.execution.network.SerialsBeforeNext)
    (active : control.actor = some alice)
    (remaining : control.remaining = (afterResponse 0).length)
    (position : control.execution.environmentRecall.length = (beforeResponse 0).length + 1) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim)
      (policy Claim defaultClaim) (some control)).expect
        (fun state => utility (protocolResults state) alice) = 0 := by
  rw [finish_response_law (policy Claim defaultClaim) 0 control active remaining position,
    FinDist.expect_map, FinDist.expect_bind]
  calc
    _ = (policy Claim defaultClaim alice (control.execution.recall alice)
        (control.execution.observe (application Claim) alice)).expect (fun _ => 0) := by
      apply FinDist.expect_congr
      intro response responseMem
      calc
        _ = (runInstructions (policy Claim defaultClaim) (afterResponse 0)
            (control.execution.respond (application Claim) alice response)).expect
              (fun _ => 0) := by
          apply FinDist.expect_congr
          intro final supported
          exact alice_binding_response_payoff_eq Claim defaultClaim control.execution final
            response core visited serials responseMem supported
        _ = _ := FinDist.expect_const ..
    _ = _ := FinDist.expect_const ..

theorem alice_protected_calendar_payoff_le {Claim : Type} (defaultClaim : Claim)
    (players : Player → (application Claim).Policy)
    (carolPolicy : players carol = policy Claim defaultClaim carol)
    (bobPolicy : players bob = policy Claim defaultClaim bob)
    (execution final : (application Claim).Execution)
    (core : execution.application.core = initialCore)
    (serials : execution.network.SerialsBeforeNext)
    (supported : final ∈ (runInstructions players
      ((List.finRange 6).flatMap visit) execution).support) :
    utility (results final.application) alice ≤ 0 := by
  change final ∈ (runInstructions players
    (visit 0 ++ (visit 1 ++ visit 2 ++ visit 3 ++ visit 4 ++ visit 5)) execution).support
      at supported
  rw [runInstructions_visit] at supported
  obtain ⟨response, _, restMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  exact alice_after_binding_payoff_le defaultClaim players carolPolicy bobPolicy _ final
    (selectedBinding 0 response) (alice_binding_response (visitInput 0 execution) response rfl core)
    (remainingVisit_serials 0 _ (respond_serials _ alice response
      (visitInput_serials 0 execution serials))) restMem

theorem alice_protected_calendar_payoff_eq (Claim : Type) (defaultClaim : Claim)
    (execution final : (application Claim).Execution)
    (core : execution.application.core = initialCore)
    (serials : execution.network.SerialsBeforeNext)
    (supported : final ∈ (runInstructions (policy Claim defaultClaim)
      ((List.finRange 6).flatMap visit) execution).support) :
    utility (results final.application) alice = 0 := by
  change final ∈ (runInstructions (policy Claim defaultClaim)
    (visit 0 ++ (visit 1 ++ visit 2 ++ visit 3 ++ visit 4 ++ visit 5)) execution).support
      at supported
  rw [runInstructions_visit] at supported
  obtain ⟨response, responseMem, restMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨bit, selected⟩ := policy_alice_binding_success Claim defaultClaim _ _ rfl
    response responseMem
  have boundCore := alice_binding_response (visitInput 0 execution) response rfl core
  rw [selected] at boundCore
  exact alice_after_binding_payoff_eq Claim defaultClaim _ final bit boundCore
    (remainingVisit_serials 0 _ (respond_serials _ alice response
      (visitInput_serials 0 execution serials))) restMem

theorem prelude_serials {Claim : Type} (first second : (application Claim).Action) :
    (prelude first second).network.SerialsBeforeNext :=
  respond_serials _ bob second (effect_serials _ _
    (respond_serials _ alice first (effect_serials _ _ MessageNetwork.SerialsBeforeNext.empty)))

theorem alice_ambient_response_payoff_le {Claim : Type} (defaultClaim : Claim)
    (players : Player → (application Claim).Policy)
    (carolPolicy : players carol = policy Claim defaultClaim carol)
    (bobPolicy : players bob = policy Claim defaultClaim bob)
    (first : (application Claim).Action) (final : (application Claim).Execution)
    (supported : final ∈ (runInstructions players (calendar.drop 1)
      (firstResponse first)).support) :
    utility (results final.application) alice ≤ 0 := by
  change final ∈ (runInstructions players
    (.player bob :: ((List.finRange 6).flatMap visit)) (firstResponse first)).support at supported
  rw [runInstructions_player] at supported
  obtain ⟨second, _, restMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  exact alice_protected_calendar_payoff_le defaultClaim players carolPolicy bobPolicy
    (prelude first second) final (prelude_core first second) (prelude_serials first second) restMem

theorem alice_ambient_response_payoff_eq (Claim : Type) (defaultClaim : Claim)
    (first : (application Claim).Action) (final : (application Claim).Execution)
    (supported : final ∈ (runInstructions (policy Claim defaultClaim) (calendar.drop 1)
      (firstResponse first)).support) :
    utility (results final.application) alice = 0 := by
  change final ∈ (runInstructions (policy Claim defaultClaim)
    (.player bob :: ((List.finRange 6).flatMap visit)) (firstResponse first)).support at supported
  rw [runInstructions_player] at supported
  obtain ⟨second, _, restMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  exact alice_protected_calendar_payoff_eq Claim defaultClaim
    (prelude first second) final (prelude_core first second) (prelude_serials first second) restMem

theorem finish_alice_ambient_payoff_le {Claim : Type} (defaultClaim : Claim)
    (players : Player → (application Claim).Policy)
    (carolPolicy : players carol = policy Claim defaultClaim carol)
    (bobPolicy : players bob = policy Claim defaultClaim bob)
    (control : (application Claim).Control) (active : control.actor = some alice)
    (remaining : control.remaining = horizon - 1)
    (execution : control.execution = effect (root Claim) (.activate alice)) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim) players
      (some control)).expect (fun state => utility (protocolResults state) alice) ≤ 0 := by
  rw [finish_ambient_law players 1 (by decide) alice control active remaining
    (by rw [execution]; rfl), FinDist.expect_map, FinDist.expect_bind]
  apply FinDist.expect_le_of_forall
  intro response _
  apply FinDist.expect_le_of_forall
  intro final supported
  rw [execution] at supported
  exact alice_ambient_response_payoff_le defaultClaim players carolPolicy bobPolicy
    response final supported

theorem finish_alice_prescribed_ambient (Claim : Type) (defaultClaim : Claim)
    (control : (application Claim).Control) (active : control.actor = some alice)
    (remaining : control.remaining = horizon - 1)
    (execution : control.execution = effect (root Claim) (.activate alice)) :
    ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim)
      (policy Claim defaultClaim) (some control)).expect
        (fun state => utility (protocolResults state) alice) = 0 := by
  rw [finish_ambient_law (policy Claim defaultClaim) 1 (by decide) alice control active remaining
    (by rw [execution]; rfl), FinDist.expect_map, FinDist.expect_bind]
  calc
    _ = (policy Claim defaultClaim alice (control.execution.recall alice)
        (control.execution.observe (application Claim) alice)).expect (fun _ => 0) := by
      apply FinDist.expect_congr
      intro response _
      calc
        _ = (runInstructions (policy Claim defaultClaim) (calendar.drop 1)
            (control.execution.respond (application Claim) alice response)).expect
              (fun _ => 0) := by
          apply FinDist.expect_congr
          intro final supported
          rw [execution] at supported
          exact alice_ambient_response_payoff_eq Claim defaultClaim response final supported
        _ = _ := FinDist.expect_const ..
    _ = _ := FinDist.expect_const ..

end VegasTests.SelectiveAssociation.NamedSource
