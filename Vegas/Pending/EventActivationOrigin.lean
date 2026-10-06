/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ServicePlan

/-! # Activation origins and deadline protection

A live activation timestamp is either retained from before a transition or
created no earlier than its entry clock. An activation at most one tick old is
still within its deadline under a feasible deadline configuration.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

namespace State

/-- A transition either retains a live activation timestamp or creates it no
earlier than the transition's entry clock. -/
def ActivationOrigin (before after : State graph) : Prop :=
  ∀ event entered, after.activatedAt event = some entered →
    event ∉ after.config.cut.completed →
      before.activatedAt event = some entered ∨ before.clock ≤ entered

omit [DecidableEq Player] in
theorem activationOrigin_of_activatedEq {before after : State graph}
    (activatedEq : after.activatedAt = before.activatedAt) :
    ActivationOrigin before after := by
  intro event entered activated unfinished
  exact Or.inl (by simpa only [activatedEq] using activated)

omit [DecidableEq Player] in
theorem activationOrigin_refresh (before : State graph) (config : graph.Config) :
    ActivationOrigin before
      { before with
        config
        activatedAt := refreshActivated config before.clock before.activatedAt } := by
  intro event entered activated unfinished
  change refreshActivated config before.clock before.activatedAt event = some entered at activated
  unfold refreshActivated at activated
  split at activated
  · rename_i ready
    cases actor : graph.actor? event with
    | none => simp [actor] at activated
    | some owner =>
        rw [actor] at activated
        cases prior : before.activatedAt event with
        | none =>
            right
            have same : before.clock = entered := by simpa [prior] using activated
            omega
        | some priorEntered =>
            left
            have same : priorEntered = entered := by simpa [prior] using activated
            exact congrArg some same
  · simp_all

omit [DecidableEq Player] in
theorem activationOrigin_of_refreshEq {before after : State graph}
    (activated : after.activatedAt =
      refreshActivated after.config before.clock before.activatedAt) :
    ActivationOrigin before after := by
  intro event entered value unfinished
  rw [activated] at value
  exact activationOrigin_refresh before after.config event entered value unfinished

omit [DecidableEq Player] in
theorem ActivationOrigin.trans {before middle after : State graph}
    (first : ActivationOrigin before middle)
    (second : ActivationOrigin middle after)
    (clock : before.clock ≤ middle.clock)
    (completed : middle.config.cut.completed ⊆ after.config.cut.completed) :
    ActivationOrigin before after := by
  intro event entered activated unfinished
  rcases second event entered activated unfinished with retained | created
  · have middleUnfinished : event ∉ middle.config.cut.completed := by
      intro done
      exact unfinished (completed done)
    exact first event entered retained middleUnfinished
  · exact Or.inr (clock.trans created)

end State

omit [DecidableEq Player] in
/-- The deadline configuration leaves an event activated at most one tick ago
within its deadline. -/
theorem withinDeadline_of_age_le_one (runtime : EventGraphRuntime graph)
    (feasible : runtime.ServiceFeasible) (state : State graph) (event : graph.EventId)
    (entered : Nat) (activated : state.activatedAt event = some entered)
    (age : state.clock - entered ≤ 1) : state.WithinDeadline runtime event := by
  have bound := feasible event
  simp only [State.WithinDeadline, activated]
  omega

end Vegas.EventGraphRuntime
