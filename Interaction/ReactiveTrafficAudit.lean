/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveHistory
import GameTheory.Protocol.StateKernel

/-! # Settlement evidence from the public traffic history

An audit record contains a submitted envelope, the public application
observation, and the ledger before that submission. It retains the phase and
prior publication evidence even when the envelope later becomes acceptable or
appears on the ledger.

The readout uses only successive public environment views. It is not added to
player observations. An implementation supplying this readout must authenticate
its traffic and phase records; ordinary envelope signatures alone do not
authenticate observation times. Partial observation and
collection are separate probabilistic contracts.

All results allow arbitrary raw responses and arbitrary schedulers. They do not
assume reserved reporting opportunities or a single pending envelope.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

structure TrafficRecord where
  observation : app.PublicObservation
  ledger : List (Message Principal app.Payload)
  envelope : Message Principal app.Payload

/-- Append-only network inputs identify successful transmissions. The record
carries the public phase preceding the transmission. -/
def trafficStep (before after : app.ProtocolState) : List app.TrafficRecord :=
  match before, after with
  | some previous, some next =>
      (next.execution.network.inputs.drop previous.execution.network.inputs.length).map
        fun input => ⟨app.observePublic previous.execution.application,
          previous.execution.network.ledger, input⟩
  | _, _ => []

/-- A settlement readout of the existing protocol history, not another
interpreter or a new observation available to players during execution. -/
def trafficAudit (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    {state : app.ProtocolState} → (app.protocol initial horizon scheduler).Trace state →
      List app.TrafficRecord
  | _, .start => []
  | state, .extend (source := before) prior _ _ _ =>
      trafficAudit initial horizon scheduler prior ++ app.trafficStep before state

/-- Environment operations never invent a transmission record. -/
theorem trafficStep_environment (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support) (remaining : Nat) :
    app.trafficStep (some ⟨remaining + 1, none, execution⟩)
      (some ⟨remaining, command.actor? app, next⟩) = [] := by
  cases command with
  | wait =>
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      simp [trafficStep]
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      simp [trafficStep, MessageNetwork.learn]
  | «include» id =>
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      cases found : execution.network.lookup id <;>
        simp [trafficStep, Execution.includePending, MessageNetwork.includePending, found]
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ supported
      simp [trafficStep]

/-- Once a transmission is recorded, no subsequent player or scheduler choice
can erase its phase or authorship from the settlement readout. -/
theorem trafficAudit_reaches (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler)
    {first last : (app.protocol initial horizon scheduler).History} {fuel : Nat}
    (path : (app.protocol initial horizon scheduler).ReachesWithin fuel first last) :
    app.trafficAudit initial horizon scheduler first.trace <+:
      app.trafficAudit initial horizon scheduler last.trace := by
  induction path with
  | refl => rfl
  | step _ _ _ _ ih =>
      change _ ++ _ <+: _ at ih
      exact (List.prefix_append ..).trans ih

end Interaction.ReactiveApplication
