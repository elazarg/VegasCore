/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionActivationOrigin
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.ReactiveServiceProgress

/-! # Activation origins in the reactive application

Native inclusion and environment service refresh activation times and then
complete automatic events at the same clock. A live timestamp is retained or
created no earlier than the operation's entry clock. The statement covers raw
states as well as initialized executions.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Every application operation retains a live activation timestamp or creates
it no earlier than the operation's entry clock. -/
theorem reactiveActivationOrigin (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (runtime.reactiveApplication leaks).StepRelation State.ActivationOrigin where
  refl _ := State.activationOrigin_of_activatedEq rfl
  submit state who material := State.activationOrigin_of_activatedEq
    (congrArg PublicView.activatedAt
      (runtime.reactiveApplication_submit_publicView leaks state who material))
  handle state message next accepted := by
    obtain ⟨native, handled, nextEq⟩ := reactiveHandle_call accepted
    rw [← nextEq]
    have first := State.activationOrigin_of_refreshEq
      (handle_clock_activated runtime state native ⟨message.id, message.payload.call⟩ handled).2
    exact first.trans native.drain_activationOrigin
      (le_of_eq (handle_clock_activated runtime state native
        ⟨message.id, message.payload.call⟩ handled).1.symm)
      (native.drainFuel_completed_subset _)
  environment state command next reached := by
    change next ∈ ((environmentStep runtime state command).map State.drain).support at reached
    obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ reached
    have first : State.ActivationOrigin state native := by
      cases command with
      | advanceClock =>
          cases (PMF.mem_support_pure_iff _ _).mp moved
          exact State.activationOrigin_of_activatedEq rfl
      | executeSample event =>
          rcases (runtime.environmentStep_executeSample_config_activated state native event
            moved).2 with stutter | ⟨_, _, _, activated⟩
          · exact State.activationOrigin_of_activatedEq stutter.2
          · exact State.activationOrigin_of_refreshEq activated
      | expire event =>
          rcases (runtime.environmentStep_expire_config_activated state native event
            moved).2 with stutter | ⟨_, _, _, activated⟩
          · exact State.activationOrigin_of_activatedEq stutter.2
          · exact State.activationOrigin_of_refreshEq activated
    exact first.trans native.drain_activationOrigin
      (by rw [environmentStep_clock runtime state native command moved]; omega)
      (native.drainFuel_completed_subset _)

/-- A physical response retains activation origins, including private candidate
registration and submission. -/
theorem reactive_respond_activationOrigin (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action) :
    State.ActivationOrigin execution.application
      (execution.respond (runtime.reactiveApplication leaks) who action).application :=
  (reactiveActivationOrigin runtime leaks).respond execution who action

/-- Every scheduler command retains activation origins through its finite
automatic completion path. -/
theorem reactive_environmentStep_activationOrigin (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) : State.ActivationOrigin execution.application next.application :=
  (reactiveActivationOrigin runtime leaks).environmentStep execution next command reached

end Vegas.EventGraphRuntime
