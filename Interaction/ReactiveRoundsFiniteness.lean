/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRounds
import Interaction.ReactiveProtocol
import Interaction.ReactiveMessageReadout
import Interaction.ReactivePolicyMixture

/-! # Finitely branching reactive rounds

When every player response law and the application's own nature branch
finitely, so does every dispatched command. The standard policies are finitely
branching: silence is a point mass, a scheduled policy is one of
two policies, and a mixture over finitely many indices mixes finitely branching
policies.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- A policy branches finitely at every recall and view. -/
def Policy.FiniteSupport (policy : app.Policy) : Prop :=
  ∀ past view, (policy past view).support.Finite

theorem invoke_support_finite {players : Principal → app.Policy}
    (finite : ∀ who, Policy.FiniteSupport app (players who)) (who : Principal)
    (execution : app.Execution) : (app.invoke players who execution).support.Finite := by
  rw [invoke, PMF.support_map]
  exact (finite who _ _).image _

theorem resume_support_finite {players : Principal → app.Policy}
    (finite : ∀ who, Policy.FiniteSupport app (players who)) (actor : Option Principal)
    (execution : app.Execution) : (app.resume players actor execution).support.Finite := by
  cases actor with
  | none => simp [resume]
  | some who => exact app.invoke_support_finite finite who execution

theorem dispatch_support_finite [app.FiniteEnvironment] {players : Principal → app.Policy}
    (finite : ∀ who, Policy.FiniteSupport app (players who)) (command : app.Command)
    (execution : app.Execution) : (app.dispatch players command execution).support.Finite :=
  bind_support_finite (app.environmentStep_support_finite execution command)
    fun next _ => app.resume_support_finite finite _ next

omit [DecidableEq Principal] in
theorem silentPolicy_finiteSupport : Policy.FiniteSupport app app.silentPolicy := by
  intro past view
  simp [silentPolicy]

omit [DecidableEq Principal] in
theorem turnScheduledPolicy_finiteSupport
    (turn : List app.PlayerEntry → app.PlayerView → Option Nat) {slots : Nat}
    (selected : Option (Fin slots)) {opening waiting : app.Policy}
    (openingFinite : Policy.FiniteSupport app opening)
    (waitingFinite : Policy.FiniteSupport app waiting) :
    Policy.FiniteSupport app (app.turnScheduledPolicy turn selected opening waiting) := by
  intro past view
  cases selected with
  | none => exact waitingFinite past view
  | some slot =>
      by_cases current : turn past view = some slot.val
      · rw [app.turnScheduledPolicy_selected turn slot opening waiting past view current]
        exact openingFinite past view
      · rw [app.turnScheduledPolicy_unselected turn (some slot) opening waiting past view
          (fun other same => by cases same; exact current)]
        exact waitingFinite past view

omit [DecidableEq Principal] in
theorem scheduledPolicy_finiteSupport (offset : Nat) {slots : Nat}
    (selected : Option (Fin slots)) {opening waiting : app.Policy}
    (openingFinite : Policy.FiniteSupport app opening)
    (waitingFinite : Policy.FiniteSupport app waiting) :
    Policy.FiniteSupport app (app.scheduledPolicy offset selected opening waiting) := by
  rw [scheduledPolicy_eq_turnScheduledPolicy]
  exact app.turnScheduledPolicy_finiteSupport _ selected openingFinite waitingFinite

omit [DecidableEq Principal] in
theorem policyMixture_finiteSupport {Index : Type} [Finite Index] (initial : PMF Index)
    {policies : Index → app.Policy} (finite : ∀ index, Policy.FiniteSupport app (policies index)) :
    Policy.FiniteSupport app (app.policyMixture initial policies).policy := by
  intro past view
  rw [policyMixture_policy]
  exact bind_support_finite (Set.toFinite _) fun index _ => finite index past view

end Interaction.ReactiveApplication
