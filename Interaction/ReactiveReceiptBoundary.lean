/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRoundBoundary
import Interaction.ReactiveReceiptIdentity

/-! # An actual accepting receipt is reached through its original inclusion command -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- A currently pending identifier has no earlier receipt in a genuine history. -/
theorem pending_identifier_not_receipted (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (message : Message Principal app.Payload)
    (pending : message ∈ control.execution.network.pending)
    (accepted : Bool) : (message.id, accepted) ∉ control.execution.receipts := by
  intro receipted
  have identifiers := app.receipt_identifiers_history initial horizon scheduler control trace
  have published : message.id ∈ control.execution.network.ledger.map Message.id := by
    rw [← identifiers]
    exact List.mem_map.mpr ⟨(message.id, accepted), receipted, rfl⟩
  have distinct := app.idsDistinct_history scheduler initial horizon trace
  change ((control.execution.network.pending ++ control.execution.network.ledger).map
    Message.id).Nodup at distinct
  rw [List.map_append] at distinct
  exact (List.nodup_append.mp distinct).2.2 _
    (List.mem_map.mpr ⟨message, pending, rfl⟩) _ published rfl

private theorem new_accepting_receipt_command (execution next : app.Execution)
    (identifier : MessageId Principal) (before : (identifier, true) ∉ execution.receipts)
    (command : app.Command) (reached : next ∈ (execution.environmentStep app command).support)
    (accepted : (identifier, true) ∈ next.receipts) : command = .include identifier := by
  cases command with
  | wait =>
      simp only [Execution.environmentStep, PMF.pure_map, PMF.mem_support_pure_iff] at reached
      cases reached
      exact (before accepted).elim
  | activate owner =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _chosen, rfl⟩ := PMF.support_map .. ▸ supported
      exact (before accepted).elim
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, _chosen, rfl⟩ := PMF.support_map .. ▸ supported
      exact (before accepted).elim
  | «include» selected =>
      simp only [Execution.environmentStep, PMF.pure_map, PMF.mem_support_pure_iff] at reached
      cases reached
      cases found : execution.network.lookup selected with
      | none =>
          simp only [Execution.includePending, MessageNetwork.includePending, found] at accepted
          exact (before accepted).elim
      | some message =>
          simp only [Execution.includePending, MessageNetwork.includePending, found] at accepted
          rcases List.mem_append.mp accepted with earlier | current
          · exact (before earlier).elim
          · have same := List.mem_singleton.mp current
            exact congrArg Command.include (congrArg Prod.fst same).symm

/-- The existing round evaluator retains the precise inclusion prefix and the
same supported suffix witnessing a newly accepting receipt. -/
theorem runRounds_accepting_receipt_boundary (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) (execution final : app.Execution)
    (identifier : MessageId Principal) (before : (identifier, true) ∉ execution.receipts)
    (reached : final ∈ (app.runRounds scheduler players count execution).support)
    (accepted : (identifier, true) ∈ final.receipts) :
    ∃ used remaining prior middle,
      used + 1 + remaining = count ∧
      prior ∈ (app.runRounds scheduler players used execution).support ∧
      (identifier, true) ∉ prior.receipts ∧
      (.include identifier : app.Command) ∈
        (scheduler prior.environmentRecall (prior.observeEnvironment app)).support ∧
      middle ∈ (prior.environmentStep app (.include identifier)).support ∧
      (identifier, true) ∈ middle.receipts ∧
      final ∈ (app.runRounds scheduler players remaining middle).support := by
  obtain ⟨used, remaining, prior, middle, resumed, command, length, path, unreceipted,
      chosen, moved, receipted, response, tail⟩ :=
    app.runRounds_environment_boundary scheduler players
      (fun current => (identifier, true) ∉ current.receipts)
      (fun current owner action safe => by
        rcases action with ⟨transmission⟩
        cases transmission <;> exact safe)
      count execution final before reached (by simpa only [not_not] using accepted)
  have commandEq := new_accepting_receipt_command app prior middle identifier unreceipted
    command moved (by simpa only [not_not] using receipted)
  subst command
  have resumedEq : resumed = middle := (PMF.mem_support_pure_iff _ _).mp response
  subst resumed
  exact ⟨used, remaining, prior, middle, length, path, unreceipted, chosen, moved,
    by simpa only [not_not] using receipted, tail⟩

end Interaction.ReactiveApplication
