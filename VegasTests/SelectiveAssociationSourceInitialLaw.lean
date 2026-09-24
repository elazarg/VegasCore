/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceAlicePayoffs
import VegasTests.SelectiveAssociationSourceGuessEquilibrium

/-! # The initialized public-result law of prescribed source play -/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

theorem prescribed_after_binding_results (Claim : Type) (defaultClaim : Claim)
    (execution : (application Claim).Execution) (a : PublicationResult Bool)
    (core : execution.application.core = CorePath.alice a)
    (serials : execution.network.SerialsBeforeNext) :
    (runInstructions (policy Claim defaultClaim)
      (visit 1 ++ visit 2 ++ visit 3 ++ visit 4 ++ visit 5) execution).map
        (fun final => results final.application) =
      FinDist.pure ⟨a, .success (publicGuess (execution.observe (application Claim) carol)),
        .success (publicGuess (execution.observe (application Claim) carol))⟩ := by
  apply FinDist.eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨final, finalMem, rfl⟩ := FinDist.support_map .. ▸ supported
  rw [List.append_assoc (visit 1 ++ visit 2),
    List.append_assoc (visit 1 ++ visit 2), runInstructions_append] at finalMem
  obtain ⟨afterGuesses, guessesMem, openingMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ finalMem)
  have afterCore := prescribed_guessers_bind_same defaultClaim (policy Claim defaultClaim)
    rfl rfl execution afterGuesses a core serials guessesMem
  exact prescribed_opening_results Claim defaultClaim afterGuesses final a _ _ afterCore openingMem

theorem prescribed_binding_results (Claim : Type) (defaultClaim : Claim)
    (first second : (application Claim).Action) (bit : Bool) :
    (runInstructions (policy Claim defaultClaim) (afterResponse 0)
      ((aliceInput first second).respond (application Claim) alice
        (playing Claim defaultClaim 0 (.success bit)))).map
          (fun final => results final.application) =
      FinDist.pure ⟨.success bit, .success false, .success false⟩ := by
  rw [runInstructions_afterResponse]
  have core := alice_binding_response (aliceInput first second)
    (playing Claim defaultClaim 0 (.success bit)) (aliceInput_visit first second)
    (aliceInput_core first second)
  have selected : selectedBinding 0 (playing Claim defaultClaim 0 (.success bit)) =
      .success bit := by simp [selectedBinding, playing]
  rw [selected] at core
  have serials := remainingVisit_serials 0
    ((aliceInput first second).respond (application Claim) alice
      (playing Claim defaultClaim 0 (.success bit)))
    (respond_serials (aliceInput first second) alice
      (playing Claim defaultClaim 0 (.success bit)) (aliceInput_serials first second))
  change (runInstructions (policy Claim defaultClaim)
    (visit 1 ++ visit 2 ++ visit 3 ++ visit 4 ++ visit 5) _).map
      (fun final => results final.application) = _
  rw [prescribed_after_binding_results Claim defaultClaim _ (.success bit) core serials]
  have preserved := playing_binding_publicGuess defaultClaim 0 (by decide) (aliceInput first second)
    (aliceInput_serials first second) (.success bit) alice carol
  rw [show eventOwner 0 = alice from rfl] at preserved
  rw [preserved]
  have prior : publicGuess ((aliceInput first second).observe (application Claim) alice) =
      false := by
    simp only [publicGuess, ReactiveApplication.Execution.observe, MessageNetwork.observe,
      aliceInput_ledger, List.flatMap_nil]
    rfl
  rw [prior]

theorem prescribed_calendar_law (Claim : Type) (defaultClaim : Claim) :
    runInstructions (policy Claim defaultClaim) calendar (root Claim) =
      (FinDist.uniformOfFintype (α := Bool)).bind (fun bit =>
        runInstructions (policy Claim defaultClaim) (afterResponse 0)
          ((aliceInput ⟨none⟩ ⟨none⟩).respond (application Claim) alice
            (playing Claim defaultClaim 0 (.success bit)))) := by
  change runInstructions (policy Claim defaultClaim)
    (.player alice :: .player bob :: .application (.grant 0) :: .player alice :: afterResponse 0)
      (root Claim) = _
  rw [runInstructions_player]
  change ((FinDist.pure (⟨none⟩ : (application Claim).Action)).bind _) = _
  rw [FinDist.pure_bind, runInstructions_player]
  change ((FinDist.pure (⟨none⟩ : (application Claim).Action)).bind _) = _
  rw [FinDist.pure_bind, runInstructions_application, runInstructions_player]
  change (((FinDist.uniformOfFintype (α := Bool)).map
    (fun bit => playing Claim defaultClaim 0 (.success bit))).bind _) = _
  rw [FinDist.bind_map]
  rfl

theorem prescribed_calendar_results (Claim : Type) (defaultClaim : Claim) :
    (runInstructions (policy Claim defaultClaim) calendar (root Claim)).map
        (fun final => results final.application) =
      (FinDist.uniformOfFintype (α := Bool)).map (fun bit =>
        (⟨.success bit, .success false, .success false⟩ : Results)) := by
  rw [prescribed_calendar_law, FinDist.map_bind, FinDist.map_eq_bind]
  exact FinDist.bind_congr (fun bit _ => prescribed_binding_results Claim defaultClaim _ _ bit)

theorem prescribed_initial_results (Claim : Type) [Fintype Claim] (defaultClaim : Claim) :
    (((model Claim).runBehavioral (profile Claim defaultClaim) (2 * horizon + 1)).map
      (fun history => protocolResults history.state)) =
      (FinDist.uniformOfFintype (α := Bool)).map (fun bit =>
        (⟨.success bit, .success false, .success false⟩ : Results)) := by
  have law := (menu Claim).run_eq_finish (FinDist.pure initial) horizon (scheduler Claim)
    (profile Claim defaultClaim) (2 * horizon + 1) (arena Claim).initHistory (by exact le_rfl)
  have decoded : (menu Claim).decodeProfile (FinDist.pure initial) horizon (scheduler Claim)
      (profile Claim defaultClaim) = policy Claim defaultClaim := by
    funext who past view
    exact decode_profile Claim defaultClaim who past view
  rw [decoded] at law
  have projected := congrArg (fun law : FinDist (application Claim).ProtocolState =>
    law.map protocolResults) law
  rw [FinDist.map_comp] at projected
  change ((model Claim).runBehavioral (profile Claim defaultClaim) (2 * horizon + 1)).map
    (fun history => protocolResults history.state) =
      ((application Claim).finish (FinDist.pure initial) horizon (scheduler Claim)
        (policy Claim defaultClaim) none).map protocolResults at projected
  rw [projected]
  simp only [ReactiveApplication.finish, FinDist.pure_bind, FinDist.map_comp]
  change ((application Claim).runRounds (scheduler Claim) (policy Claim defaultClaim)
    calendar.length (root Claim)).map (fun final => results final.application) = _
  rw [segment_rounds (policy Claim defaultClaim) [] calendar [] (by simp) (root Claim) rfl]
  exact prescribed_calendar_results Claim defaultClaim

theorem prescribed_initial_alice_payoff (Claim : Type) [Fintype Claim] (defaultClaim : Claim) :
    ((model Claim).runBehavioral (profile Claim defaultClaim) (2 * horizon + 1)).expect
      (payoff alice) = 0 := by
  have value := congrArg (fun law : FinDist Results =>
    law.expect (fun result => utility result alice))
    (prescribed_initial_results Claim defaultClaim)
  simp only [FinDist.expect_map, utility_alice, sub_self, openingPenalty_success,
    FinDist.expect_const] at value
  exact value

end VegasTests.SelectiveAssociation.NamedSource
