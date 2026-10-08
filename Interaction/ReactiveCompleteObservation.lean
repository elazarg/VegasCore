/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.CompletePendingObservation
import Interaction.ReactiveMessageIdentity
import Interaction.ReactiveMessageReadout
import Interaction.ReactivePublication
import Interaction.ReactiveTrafficState

/-! # Complete packet observation at every raw activation

Under complete pending observation, a player's actual activation view contains
every foreign packet submitted so far. Raw histories establish the carrier
identity and retention invariants; neither conformant play nor application
acceptance is required.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- Complete sampling exposes every retained foreign submission in the
ordinary player view before that activation's response. -/
theorem complete_activation_submitted_visible
    (complete : app.observePending = MessageNetwork.completePendingObservation)
    (scheduler : app.Scheduler) (initial : PMF app.State) (horizon : Nat)
    (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (who : Principal) (next : app.Execution)
    (activated : next ∈ (control.execution.environmentStep app (.activate who)).support)
    (message : Message Principal app.Payload)
    (submitted : message ∈ control.execution.network.inputs)
    (foreign : message.sender ≠ who) :
    message ∈ (next.observe app who).messages.leaked ∨
      message ∈ (next.observe app who).messages.ledger := by
  rw [Execution.activation_samples, complete] at activated
  simp only [MessageNetwork.completePendingObservation, PMF.pure_map,
    PMF.mem_support_pure_iff] at activated
  subst next
  exact MessageNetwork.submitted_visible_of_complete_observation control.execution.network
    (app.uniqueIds_history scheduler initial horizon control trace)
    (app.pendingOrPublished_history scheduler initial horizon trace) who message submitted foreign

private theorem complete_history_visible
    (complete : app.observePending = MessageNetwork.completePendingObservation)
    (scheduler : app.Scheduler) (initial : PMF app.State) (horizon : Nat) :
    ∀ {state} (_trace : (app.protocol initial horizon scheduler).Trace state)
      (control : app.Control), state = some control →
      ∀ (who : Principal), control.actor = some who →
      ∀ (message : Message Principal app.Payload),
        message ∈ control.execution.network.inputs → message.sender ≠ who →
          message ∈ (control.execution.observe app who).messages.leaked ∨
            message ∈ (control.execution.observe app who).messages.ledger
  | _, .start, _, equal, _, _, _, _, _ => by cases equal
  | _, .extend (source := source) (target := target) prior joint _ realized,
      control, equal, who, active, message, submitted, foreign => by
      change target ∈ (app.transition initial horizon scheduler source joint).support at realized
      rw [equal] at realized
      change some control ∈ (app.transition initial horizon scheduler source joint).support
        at realized
      cases source with
      | none =>
          simp only [transition, PMF.support_map] at realized
          obtain ⟨state, _, equal⟩ := realized
          cases equal
          cases active
      | some before =>
          cases actorEq : before.actor with
          | some owner =>
              simp only [transition, actorEq, PMF.mem_support_pure_iff] at realized
              cases realized
              cases active
          | none =>
              cases remainingEq : before.remaining with
              | zero =>
                  simp only [transition, actorEq, remainingEq, PMF.mem_support_pure_iff]
                    at realized
                  cases realized
                  rw [actorEq] at active
                  cases active
              | succ remaining =>
                  simp only [transition, actorEq, remainingEq, PMF.support_bind,
                    PMF.support_map] at realized
                  obtain ⟨command, _, next, moved, equal⟩ := Set.mem_iUnion₂.mp realized
                  cases equal
                  cases command with
                  | activate observer =>
                      have same : observer = who := Option.some.inj active
                      subst observer
                      rw [app.environmentStep_inputs before.execution next (.activate who)
                        moved] at submitted
                      exact app.complete_activation_submitted_visible complete scheduler initial
                        horizon before prior who next moved message submitted foreign
                  | wait | application operation | «include» id => cases active

/-- Every actual raw decision view exposes all previously submitted foreign
packets. The legal trace itself supplies the preceding complete activation. -/
theorem complete_decision_submitted_visible
    (complete : app.observePending = MessageNetwork.completePendingObservation)
    (scheduler : app.Scheduler) (initial : PMF app.State) (horizon : Nat)
    (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (who : Principal) (active : control.actor = some who)
    (message : Message Principal app.Payload)
    (submitted : message ∈ control.execution.network.inputs)
    (foreign : message.sender ≠ who) :
    message ∈ (control.execution.observe app who).messages.leaked ∨
      message ∈ (control.execution.observe app who).messages.ledger :=
  complete_history_visible app complete scheduler initial horizon trace control rfl who active
    message submitted foreign

end Interaction.ReactiveApplication
