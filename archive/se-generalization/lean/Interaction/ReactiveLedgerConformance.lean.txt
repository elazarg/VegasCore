/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePublication
import Interaction.ReactivePolicyInvariant

/-! # Persistent conformance evidence from included packets

The checker reads only the public ledger and attributes each envelope to its
author. Application acceptance does not erase
the packet or exempt it from the public predicate. The predicate must be proved
sound for the intended source implementation separately.

These results establish observable, persistent evidence. They neither force
pending packets to be included nor implement collection of a monetary charge.
-/

noncomputable section

namespace Interaction

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {Payload : Type}

def ledgerViolation (who : Player) (permitted : Payload → Bool)
    (ledger : List (Message Player (Payload))) : Bool :=
  ledger.any fun message => decide (message.sender = who) && !permitted message.payload

theorem ledgerViolation_iff (who : Player) (permitted : Payload → Bool)
    (ledger : List (Message Player (Payload))) :
    ledgerViolation who permitted ledger = true ↔
      ∃ message ∈ ledger, message.sender = who ∧ permitted message.payload = false := by
  simp [ledgerViolation, List.any_eq_true]

theorem ledgerViolation_mono (who : Player) (permitted : Payload → Bool)
    {first second : List (Message Player (Payload))}
    (included : first ⊆ second) (detected : ledgerViolation who permitted first = true) :
    ledgerViolation who permitted second = true := by
  rw [ledgerViolation_iff] at detected ⊢
  obtain ⟨message, member, authored, rejected⟩ := detected
  exact ⟨message, included member, authored, rejected⟩

theorem ledgerViolation_clear (who : Player) (permitted : Payload → Bool)
    (ledger : List (Message Player (Payload)))
    (compliant : ∀ message ∈ ledger, message.sender = who → permitted message.payload = true) :
    ledgerViolation who permitted ledger = false := by
  cases alarm : ledgerViolation who permitted ledger with
  | false => rfl
  | true =>
      obtain ⟨message, member, authored, rejected⟩ :=
        (ledgerViolation_iff who permitted ledger).mp alarm
      have allowed := compliant message member authored
      rw [allowed] at rejected
      contradiction

namespace ReactiveApplication

variable (app : ReactiveApplication Player) (who : Player) (permitted : app.Payload → Bool)

/-- Inclusion exposes the packet regardless of whether its application call succeeds. -/
theorem ledgerViolation_includePending
    (execution : app.Execution) (id : MessageId Player)
    (message : Message Player app.Payload)
    (found : execution.network.lookup id = some message) (authored : message.sender = who)
    (nonconforming : permitted message.payload = false) :
    ledgerViolation who permitted
      (execution.includePending app id).network.ledger = true := by
  rw [app.includePending_network]
  simp only [MessageNetwork.includePending, found]
  rw [ledgerViolation_iff]
  exact ⟨message, List.mem_append_right _ (List.mem_singleton_self _), authored, nonconforming⟩

/-- Application maintenance, including expiry, creates no ledger liability. -/
theorem ledgerViolation_application
    (execution next : app.Execution)
    (command : app.EnvironmentCommand)
    (reached : next ∈ (execution.environmentStep app
      (.application command)).support) :
    ledgerViolation who permitted next.network.ledger =
      ledgerViolation who permitted execution.network.ledger := by
  obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
  obtain ⟨_, _, rfl⟩ := PMF.support_map .. ▸ supported
  rfl

theorem ledgerViolation_respond
    (execution : app.Execution) (actor : Player)
    (action : app.Action)
    (detected : ledgerViolation who permitted execution.network.ledger = true) :
    ledgerViolation who permitted
      (execution.respond app actor action).network.ledger =
        true := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact detected
  | some material => exact detected

theorem ledgerViolation_environment
    (execution next : app.Execution)
    (command : app.Command)
    (detected : ledgerViolation who permitted execution.network.ledger = true)
    (reached : next ∈
      (execution.environmentStep app command).support) :
    ledgerViolation who permitted next.network.ledger = true := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact detected
  | activate actor =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact detected
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      change ledgerViolation who permitted
        (execution.includePending app id).network.ledger = true
      rw [app.includePending_network]
      cases found : execution.network.lookup id with
      | none => simpa only [MessageNetwork.includePending, found] using detected
      | some message =>
          simp only [MessageNetwork.includePending, found]
          exact ledgerViolation_mono who permitted (fun _ member => List.mem_append_left _ member)
            detected
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨_, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact detected

theorem ledgerViolation_policyInvariant
    (players : Player → app.Policy) :
    app.PolicyInvariant players
      (fun execution => ledgerViolation who permitted execution.network.ledger = true) where
  respond execution actor action detected _ :=
    app.ledgerViolation_respond who permitted execution actor action detected
  environment execution next command detected reached :=
    app.ledgerViolation_environment who permitted execution next command detected reached

/-- Once recorded, no later raw policy or scheduling choice can erase this evidence. -/
theorem ledgerViolation_continuation
    (players : Player → app.Policy)
    (scheduler : app.Scheduler) (count : Nat)
    (execution next : app.Execution)
    (detected : ledgerViolation who permitted execution.network.ledger = true)
    (reached : next ∈ (app.runRounds scheduler players count
      execution).support) :
    ledgerViolation who permitted next.network.ledger = true :=
  (app.ledgerViolation_policyInvariant who permitted players).runRounds
    scheduler count execution next detected reached

end ReactiveApplication
end Interaction
