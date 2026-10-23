/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceProgress
import Vegas.Pending.CompletionService
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.EventActivationOrigin

/-! # Timely recurring owner opportunities after dependency settlement

The existing reactive epoch visits every event before its one clock tick.
An event newly activated during an arbitrary epoch is at most one tick old
at the boundary. Its next reserved owner activation therefore remains timely
when the configured deadline is at least two, unless another allowed action
has already completed the event. Player omissions, malformed submissions,
passive leaks, and network reactions are unrestricted.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Every operation of the reactive application starts timers exactly: a
timestamp is kept, or a newly activated event is stamped with the clock at the
operation. This covers arbitrary submissions, inclusions and environment
commands. -/
theorem reactiveActivationStart (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (runtime.reactiveApplication leaks).StepRelation State.ActivationStart where
  refl _ := State.activationStart_of_activatedEq rfl
  submit state who material := State.activationStart_of_activatedEq
    (congrArg PublicView.activatedAt
      (runtime.reactiveApplication_submit_publicView leaks state who material))
  handle state message next accepted := State.activationStart_of_refreshEq
    (handle_clock_activated runtime state next ⟨message.id, message.payload.call⟩
      (reactiveHandle_call accepted)).2
  environment state command next reached := by
    cases command with
    | advanceClock =>
        simp only [reactiveApplication, environmentStep, PMF.mem_support_pure_iff _ _]
          at reached
        subst next
        exact State.activationStart_of_activatedEq rfl
    | executeSample event =>
        obtain ⟨_, stutter | changed⟩ :=
          runtime.environmentStep_executeSample_config_activated state next event reached
        · exact State.activationStart_of_activatedEq stutter.2
        · obtain ⟨_, _, _, activated⟩ := changed
          exact State.activationStart_of_refreshEq activated
    | expire event =>
        obtain ⟨_, stutter | changed⟩ :=
          runtime.environmentStep_expire_config_activated state next event reached
        · exact State.activationStart_of_activatedEq stutter.2
        · obtain ⟨_, _, _, activated⟩ := changed
          exact State.activationStart_of_refreshEq activated

end Vegas.EventGraphRuntime
