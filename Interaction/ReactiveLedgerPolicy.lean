/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveApplication

/-! # Policies that ignore pending-message observations

The ledger projection retains application observations, receipts, the player's
own actions and emitted packets. It removes passive pending-message observations
from both the current view and every view in private recall. For the event
application the retained application view consists of contract state and the
player's own private values.
-/

namespace Interaction.ReactiveApplication

variable {Principal : Type} (app : ReactiveApplication Principal)

/-- Retain the ledger, local application state and receipts. -/
def PlayerView.ledgerOnly (view : app.PlayerView) : app.PlayerView :=
  { view with messages := { view.messages with leaked := [] } }

/-- Retain own actions and output while removing an earlier pending observation. -/
def PlayerEntry.ledgerOnly (entry : app.PlayerEntry) : app.PlayerEntry :=
  { entry with beforeView := entry.beforeView.ledgerOnly app }

@[simp] theorem PlayerView.ledgerOnly_idempotent (view : app.PlayerView) :
    (view.ledgerOnly app).ledgerOnly app = view.ledgerOnly app := rfl

@[simp] theorem PlayerEntry.ledgerOnly_idempotent (entry : app.PlayerEntry) :
    (entry.ledgerOnly app).ledgerOnly app = entry.ledgerOnly app := rfl

/-- Run a policy using ledger observations throughout its recall. -/
def ledgerPolicy (policy : app.Policy) : app.Policy := fun past view =>
  policy (past.map (PlayerEntry.ledgerOnly app)) (view.ledgerOnly app)

/-- Removing all pending observations leaves the policy's action law unchanged. -/
def Policy.UsesLedgerOnly (policy : app.Policy) : Prop :=
  ∀ past view, policy past view =
    policy (past.map (PlayerEntry.ledgerOnly app)) (view.ledgerOnly app)

theorem ledgerPolicy_usesLedgerOnly (policy : app.Policy) :
    Policy.UsesLedgerOnly app (app.ledgerPolicy policy) := by
  intro past view
  simp only [ledgerPolicy, List.map_map, Function.comp_def,
    PlayerEntry.ledgerOnly_idempotent, PlayerView.ledgerOnly_idempotent]

/-- Equal retained recall and views give equal action laws. -/
theorem ledgerPolicy_congr (policy : app.Policy)
    (firstPast secondPast : List app.PlayerEntry) (firstView secondView : app.PlayerView)
    (past : firstPast.map (PlayerEntry.ledgerOnly app) =
      secondPast.map (PlayerEntry.ledgerOnly app))
    (view : firstView.ledgerOnly app = secondView.ledgerOnly app) :
    app.ledgerPolicy policy firstPast firstView =
      app.ledgerPolicy policy secondPast secondView := by
  simp only [ledgerPolicy, past, view]

end Interaction.ReactiveApplication
