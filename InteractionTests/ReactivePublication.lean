/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePublication

/-! # Rejection spends an identifier; a fresh envelope can retry the call -/

noncomputable section

namespace InteractionTests.ReactivePublication

open Interaction GameTheory.Math.Probability

private abbrev app : ReactiveApplication Bool where
  State := Bool
  Payload := Nat
  Submission := Nat
  EnvironmentCommand := Unit
  LocalObservation := Bool
  PublicObservation := Bool
  packet := id
  submit state _ _ := state
  handle ready _ := if ready then some ready else none
  environment _ _ := FinDist.pure true
  observePlayer ready _ := ready
  observePublic := id
  observePending _ _ := FinDist.pure ∅

private def sent : app.Execution :=
  (ReactiveApplication.Execution.initial app false).respond app false
    ⟨some (.submit 7)⟩

private def rejected : app.Execution := sent.includePending app (false, 0)

theorem rejection_is_published :
    rejected.network.ledger = [⟨(false, 0), 7⟩] ∧
      rejected.receipts = [((false, 0), false)] := ⟨rfl, rfl⟩

private def ready : app.Execution := { rejected with application := true }

private def replayed : app.Execution :=
  ready.respond app false ⟨some (.replay (false, 0))⟩

/-- Rebroadcast is a legal transmission and still enters the pending pool. -/
theorem rejected_replay_is_pending :
    replayed.network.pending = [⟨(false, 0), 7⟩] := rfl

/-- Making the application ready does not restore an already spent identifier. -/
theorem rejected_replay_is_not_reincluded :
    app.atMostOnceCommand (replayed.observeEnvironment app) (.include (false, 0)) =
      .wait := rfl

theorem rejected_replay_service_law :
    ((replayed.environmentStep app
      (app.atMostOnceCommand (replayed.observeEnvironment app) (.include (false, 0)))).map
        (fun execution => execution.receipts)) = FinDist.pure [((false, 0), false)] := by
  rw [rejected_replay_is_not_reincluded]
  simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
  rfl

private def retried : app.Execution :=
  replayed.respond app false ⟨some (.submit 7)⟩

/-- The payload can be identical; the retry receives a fresh identifier. -/
theorem retry_is_fresh :
    app.atMostOnceCommand (retried.observeEnvironment app) (.include (false, 1)) =
      .include (false, 1) := rfl

theorem retry_service_law :
    ((retried.environmentStep app
      (app.atMostOnceCommand (retried.observeEnvironment app) (.include (false, 1)))).map
        (fun execution => execution.receipts)) =
      FinDist.pure [((false, 0), false), ((false, 1), true)] := by
  rw [retry_is_fresh]
  simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
  rfl

end InteractionTests.ReactivePublication
