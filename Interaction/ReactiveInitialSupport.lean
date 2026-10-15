/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseMenu

/-! # Legal reactive traces under restriction of the initial support

Only initialization reads the initial distribution. Every later control,
response, environment command and observation remains the same.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)
  (smaller larger : PMF app.State) (included : smaller.support ⊆ larger.support)
  (horizon : Nat) (scheduler : app.Scheduler)

include included

/-- Restricting the initial support restricts the actual transition support. -/
theorem transition_support_subset_of_initial_support_subset
    (state : app.ProtocolState) (joint : Principal → Option app.Action) :
    (app.transition smaller horizon scheduler state joint).support ⊆
      (app.transition larger horizon scheduler state joint).support := by
  cases state with
  | none =>
      simp only [transition, PMF.support_map]
      exact Set.image_mono included
  | some control =>
      cases control.actor <;> rfl

/-- The same realized controls and responses form a trace under the larger
initial support. No probabilities are identified by this embedding. -/
def trace_of_initial_support_subset :
    ∀ {state}, (app.protocol smaller horizon scheduler).Trace state →
      (app.protocol larger horizon scheduler).Trace state
  | _, .start => .start
  | _, .extend prior joint legal reached =>
      .extend (trace_of_initial_support_subset prior) joint legal
        (app.transition_support_subset_of_initial_support_subset
          smaller larger included horizon scheduler _ _ reached)

@[simp]
theorem trace_of_initial_support_subset_length {state}
    (trace : (app.protocol smaller horizon scheduler).Trace state) :
    (app.trace_of_initial_support_subset smaller larger included horizon scheduler trace).length =
      trace.length := by
  induction trace with
  | start => rfl
  | extend prior joint legal reached ih => exact congrArg Nat.succ ih

namespace ResponseMenu

variable {app} (menu : app.ResponseMenu)

/-- A fixed response menu transports the same legal responses and actual
controls when only the initial support is enlarged. -/
def trace_of_initial_support_subset :
    ∀ {state}, (menu.protocol smaller horizon scheduler).Trace state →
      (menu.protocol larger horizon scheduler).Trace state
  | _, .start => .start
  | _, .extend prior joint legal reached =>
      .extend (trace_of_initial_support_subset prior) joint legal
        (app.transition_support_subset_of_initial_support_subset
          smaller larger included horizon scheduler _ _ reached)

@[simp]
theorem trace_of_initial_support_subset_length {state}
    (trace : (menu.protocol smaller horizon scheduler).Trace state) :
    (menu.trace_of_initial_support_subset smaller larger included horizon scheduler trace).length =
      trace.length := by
  induction trace with
  | start => rfl
  | extend prior joint legal reached ih => exact congrArg Nat.succ ih

end ResponseMenu
end Interaction.ReactiveApplication
