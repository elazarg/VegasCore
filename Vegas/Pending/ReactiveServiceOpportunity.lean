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
theorem reactiveActivationOrigin (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    ((reactiveApplication timeouts) leaks).StepRelation State.ActivationOrigin where
  refl _ := State.activationOrigin_of_activatedEq rfl
  submit state who material := State.activationOrigin_of_activatedEq
    (congrArg PublicView.activatedAt
      ((reactiveApplication_submit_publicView timeouts) leaks state who material))
  handle state message next accepted := by
    obtain ⟨native, handled, nextEq⟩ := reactiveHandle_call accepted
    rw [← nextEq]
    have first := State.activationOrigin_of_refreshEq
      (handle_clock_activated timeouts state native ⟨message.id, message.payload.call⟩ handled).2
    exact first.trans native.drain_activationOrigin
      (le_of_eq (handle_clock_activated timeouts state native
        ⟨message.id, message.payload.call⟩ handled).1.symm)
      (native.drainFuel_completed_subset _)
  environment state command next reached := by
    change next ∈ ((environmentStep timeouts state command).map State.drain).support at reached
    obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ reached
    have first : State.ActivationOrigin state native := by
      cases command with
      | advanceClock =>
          cases (PMF.mem_support_pure_iff _ _).mp moved
          exact State.activationOrigin_of_activatedEq rfl
      | executeSample event =>
          rcases ((environmentStep_executeSample_config_activated timeouts) state native event
            moved).2 with stutter | ⟨_, _, _, activated⟩
          · exact State.activationOrigin_of_activatedEq stutter.2
          · exact State.activationOrigin_of_refreshEq activated
      | expire event =>
          rcases ((environmentStep_expire_config_activated timeouts) state native event
            moved).2 with stutter | ⟨_, _, _, activated⟩
          · exact State.activationOrigin_of_activatedEq stutter.2
          · exact State.activationOrigin_of_refreshEq activated
    exact first.trans native.drain_activationOrigin
      (by rw [environmentStep_clock timeouts state native command moved]; omega)
      (native.drainFuel_completed_subset _)

/-- A physical response retains activation origins, including private candidate
registration and submission. -/
theorem reactive_respond_activationOrigin (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : ((reactiveApplication timeouts) leaks).Execution) (who : Player)
    (action : ((reactiveApplication timeouts) leaks).Action) :
    State.ActivationOrigin execution.application
      (execution.respond ((reactiveApplication timeouts) leaks) who action).application :=
  (reactiveActivationOrigin timeouts leaks).respond execution who action

/-- Every scheduler command retains activation origins through its finite
automatic completion path. -/
theorem reactive_environmentStep_activationOrigin (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : ((reactiveApplication timeouts) leaks).Execution)
    (command : ((reactiveApplication timeouts) leaks).Command)
    (reached : next ∈ (execution.environmentStep ((reactiveApplication timeouts) leaks)
      command).support) : State.ActivationOrigin execution.application next.application :=
  (reactiveActivationOrigin timeouts leaks).environmentStep execution next command reached

end Vegas.EventGraphRuntime
