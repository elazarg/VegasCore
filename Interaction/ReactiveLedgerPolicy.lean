module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveApplication

@[expose] public section

/-! # Policies on the ledger projection of callback views

The ledger projection retains application observations, receipts, the player's
own actions and emitted packets. It erases the leaked-message field from the current
view and every recorded pre-response view. It does not erase information carried by
retained own output: certificate materialization can depend on earlier passive
delivery. For the event application the retained application view consists of
contract state and the player's own private values. Physical realization of
arbitrary decoded profiles additionally uses an empty pending-delivery kernel.
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

/-- Project current and recalled views, retaining own actions and emitted packets. -/
def ledgerPolicy (policy : app.Policy) : app.Policy := fun past view =>
  policy (past.map (PlayerEntry.ledgerOnly app)) (view.ledgerOnly app)

/-- Erasing explicit leaked fields leaves the action law unchanged. Own actions,
emitted packets and all other retained fields are held fixed by this predicate. -/
def Policy.IgnoresLeakedFields (policy : app.Policy) : Prop :=
  ∀ past view, policy past view =
    policy (past.map (PlayerEntry.ledgerOnly app)) (view.ledgerOnly app)

theorem ledgerPolicy_ignoresLeakedFields (policy : app.Policy) :
    Policy.IgnoresLeakedFields app (app.ledgerPolicy policy) := by
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
