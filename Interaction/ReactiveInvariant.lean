/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveProtocol

/-! # Application invariants at every canonical reactive history -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

/-- Local application obligations suffice for every player and scheduler.
Network delivery, replay, and private memory do not change application state. -/
structure Invariant (predicate : app.State → Prop) : Prop where
  submit : ∀ state who material, predicate state → predicate (app.submit state who material)
  handle : ∀ state message next, predicate state → app.handle state message = some next →
    predicate next
  environment : ∀ state command next, predicate state →
    next ∈ (app.environment state command).support → predicate next

variable [DecidableEq Principal] {app} {predicate : app.State → Prop}

theorem Invariant.respond (invariant : app.Invariant predicate)
    (execution : app.Execution) (who : Principal) (action : app.Action)
    (valid : predicate execution.application) :
    predicate (execution.respond app who action).application := by
  rcases action with ⟨memory, transmission⟩
  cases transmission with
  | none => exact valid
  | some transmission =>
      cases transmission with
      | replay id => exact valid
      | submit material => exact invariant.submit execution.application who material valid

theorem Invariant.includePending (invariant : app.Invariant predicate)
    (execution : app.Execution) (id : MessageId Principal)
    (valid : predicate execution.application) :
    predicate (execution.includePending app id).application := by
  unfold Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup id with
  | none => exact valid
  | some message =>
      change predicate ((app.handle execution.application message).getD execution.application)
      cases accepted : app.handle execution.application message with
      | none => exact valid
      | some next => exact invariant.handle execution.application message next valid accepted

theorem Invariant.environmentStep (invariant : app.Invariant predicate)
    (execution next : app.Execution) (command : app.Command)
    (valid : predicate execution.application)
    (reached : next ∈ (execution.environmentStep app command).support) :
    predicate next.application := by
  cases command with
  | activate who | wait | deliver who id =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact valid
  | «include» id =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact invariant.includePending execution id valid
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := FinDist.support_map .. ▸ supported
      exact invariant.environment execution.application command state valid changed

def stateInvariant (predicate : app.State → Prop) : app.ProtocolState → Prop
  | none => True
  | some control => predicate control.execution.application

variable [Inhabited app.Memory]

theorem Invariant.transition (invariant : app.Invariant predicate)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (setup : ∀ state ∈ initial.support, predicate state)
    (before after : app.ProtocolState) (joint : Principal → Option app.Action)
    (valid : stateInvariant predicate before)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    stateInvariant predicate after := by
  cases before with
  | none =>
      obtain ⟨state, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      exact setup state supported
  | some control =>
      rcases control with ⟨remaining, current, execution⟩
      cases current with
      | some who =>
          cases FinDist.mem_support_pure.mp reached
          exact invariant.respond execution who _ valid
      | none =>
          cases remaining with
          | zero => cases FinDist.mem_support_pure.mp reached; exact valid
          | succ remaining =>
              obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ moved
              exact invariant.environmentStep execution next command valid supported

/-- Covers every legal initialized history, including arbitrary deviations,
off-path prefixes, and scheduler choices outside a reserved service. -/
theorem Invariant.history (invariant : app.Invariant predicate)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (setup : ∀ state ∈ initial.support, predicate state) :
    ∀ {state} (_trace : (app.protocol initial horizon scheduler).Trace state),
      stateInvariant predicate state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      invariant.transition initial horizon scheduler setup _ _ joint
        (invariant.history initial horizon scheduler setup prior) reached

end Interaction.ReactiveApplication
