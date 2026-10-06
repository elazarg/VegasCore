/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveProtocol

/-! # Application invariants at every canonical reactive history

An invariant is a predicate every application operation preserves; a step
relation relates every application state to its successor. Both lift from the
application's submit, handle and environment operations to every protocol
transition.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

/-- Local application obligations suffice for every player and scheduler.
Passive observation and silence do not change application state. -/
structure Invariant (predicate : app.State → Prop) : Prop where
  submit : ∀ state who material, predicate state → predicate (app.submit state who material)
  handle : ∀ state message next, predicate state → app.handle state message = some next →
    predicate next
  environment : ∀ state command next, predicate state →
    next ∈ (app.environment state command).support → predicate next

/-- A relation between an application state and its successor that every
application operation establishes. Passive observation, silence and scheduler
bookkeeping leave the state unchanged, so the relation must be reflexive. -/
structure StepRelation (relation : app.State → app.State → Prop) : Prop where
  refl : ∀ state, relation state state
  submit : ∀ state who material, relation state (app.submit state who material)
  handle : ∀ state message next, app.handle state message = some next → relation state next
  environment : ∀ state command next,
    next ∈ (app.environment state command).support → relation state next

variable [DecidableEq Principal] {app} {predicate : app.State → Prop}

theorem Invariant.respond (invariant : app.Invariant predicate)
    (execution : app.Execution) (who : Principal) (action : app.Action)
    (valid : predicate execution.application) :
    predicate (execution.respond app who action).application := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact valid
  | some material => exact invariant.submit execution.application who material valid

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
  | wait =>
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact valid
  | «include» id =>
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact invariant.includePending execution id valid
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      exact invariant.environment execution.application command state valid changed

def stateInvariant (predicate : app.State → Prop) : app.ProtocolState → Prop
  | none => True
  | some control => predicate control.execution.application

theorem Invariant.transition (invariant : app.Invariant predicate)
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (setup : ∀ state ∈ initial.support, predicate state)
    (before after : app.ProtocolState) (joint : Principal → Option app.Action)
    (valid : stateInvariant predicate before)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    stateInvariant predicate after := by
  cases before with
  | none =>
      obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
      exact setup state supported
  | some control =>
      rcases control with ⟨remaining, current, execution⟩
      cases current with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact invariant.respond execution who _ valid
      | none =>
          cases remaining with
          | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact valid
          | succ remaining =>
              obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
              exact invariant.environmentStep execution next command valid supported

/-- Covers every legal initialized history, including arbitrary deviations,
off-path prefixes, and scheduler choices outside a reserved service. -/
theorem Invariant.history (invariant : app.Invariant predicate)
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (setup : ∀ state ∈ initial.support, predicate state) :
    ∀ {state} (_trace : (app.protocol initial horizon scheduler).Trace state),
      stateInvariant predicate state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      invariant.transition initial horizon scheduler setup _ _ joint
        (invariant.history initial horizon scheduler setup prior) reached

variable {relation : app.State → app.State → Prop}

theorem StepRelation.respond (step : app.StepRelation relation)
    (execution : app.Execution) (who : Principal) (action : app.Action) :
    relation execution.application (execution.respond app who action).application := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact step.refl _
  | some material => exact step.submit execution.application who material

theorem StepRelation.includePending (step : app.StepRelation relation)
    (execution : app.Execution) (id : MessageId Principal) :
    relation execution.application (execution.includePending app id).application := by
  unfold Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup id with
  | none => exact step.refl _
  | some message =>
      change relation execution.application
        ((app.handle execution.application message).getD execution.application)
      cases accepted : app.handle execution.application message with
      | none => exact step.refl _
      | some next => exact step.handle execution.application message next accepted

theorem StepRelation.environmentStep (step : app.StepRelation relation)
    (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support) :
    relation execution.application next.application := by
  cases command with
  | wait =>
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact step.refl _
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact step.refl _
  | «include» id =>
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact step.includePending execution id
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      exact step.environment execution.application command state changed

/-- Every protocol transition between initialized states relates the
application states, under arbitrary responses and scheduler choices. -/
theorem StepRelation.transition (step : app.StepRelation relation)
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (before after : app.Control) (joint : Principal → Option app.Action)
    (reached : some after ∈ (app.transition initial horizon scheduler (some before)
      joint).support) :
    relation before.execution.application after.execution.application := by
  rcases before with ⟨remaining, current, execution⟩
  cases current with
  | some who =>
      cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
      exact step.respond execution who _
  | none =>
      cases remaining with
      | zero =>
          cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
          exact step.refl _
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨next, supported, same⟩ := PMF.support_map .. ▸ moved
          cases Option.some.inj same
          exact step.environmentStep execution next command supported

end Interaction.ReactiveApplication
