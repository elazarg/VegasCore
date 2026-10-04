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
  packet := fun _ _ _ => id
  submit state _ _ := state
  handle ready _ := if ready then some ready else none
  environment _ _ := PMF.pure true
  observePlayer ready _ := ready
  observePublic := id
  observePending _ _ := PMF.pure ∅

private def sent : app.Execution :=
  (ReactiveApplication.Execution.initial app false).respond app false
    ⟨some 7⟩

private def rejected : app.Execution := sent.includePending app (false, 0)

theorem rejection_is_published :
    rejected.network.ledger = [⟨(false, 0), 7⟩] ∧
      rejected.receipts = [((false, 0), false)] := ⟨rfl, rfl⟩

private def ready : app.Execution := { rejected with application := true }

/-- A spent identifier is no longer pending: making the application ready
does not let it be included again. -/
theorem rejected_is_not_reincluded :
    ready.network.pending = [] ∧
      (ready.includePending app (false, 0)).receipts = [((false, 0), false)] := ⟨rfl, rfl⟩

/-- The service's at-most-once guard also refuses the spent identifier. -/
theorem rejected_service_law :
    app.atMostOnceCommand (ready.observeEnvironment app) (.include (false, 0)) = .wait := rfl

private def retried : app.Execution :=
  ready.respond app false ⟨some 7⟩

/-- The payload can be identical; the retry receives a fresh identifier. -/
theorem retry_is_fresh :
    app.atMostOnceCommand (retried.observeEnvironment app) (.include (false, 1)) =
      .include (false, 1) := rfl

theorem retry_service_law :
    ((retried.environmentStep app
      (app.atMostOnceCommand (retried.observeEnvironment app) (.include (false, 1)))).map
        (fun execution => execution.receipts)) =
      PMF.pure [((false, 0), false), ((false, 1), true)] := by
  rw [retry_is_fresh]
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rfl

end InteractionTests.ReactivePublication
