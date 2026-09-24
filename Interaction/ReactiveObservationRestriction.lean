/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveServiceInvariant

/-! # Removing passive observation in the existing reactive protocol

Using the constant empty-selection rule for pending observation leaves every
player's leaked-packet list empty at every legal initialized history. The
statement covers arbitrary raw responses, replay and adaptive scheduling.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

theorem respond_leaked (execution : app.Execution) (actor who : Principal)
    (action : app.Action) :
    (execution.respond app actor action).network.leaked who = execution.network.leaked who := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
    cases transmission with
    | submit material => rfl
    | replay id =>
      cases found : (execution.network.known actor).find? (fun message => message.id = id) <;>
        simp only [Execution.respond, MessageNetwork.replay, found]

theorem environment_leaked_of_empty_observation
    (emptyObservation : ∀ who pending, app.observePending who pending = FinDist.pure ∅)
    (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support) (who : Principal) :
    next.network.leaked who = execution.network.leaked who := by
  cases command with
  | wait =>
    simp only [Execution.environmentStep, FinDist.map_pure] at reached
    cases FinDist.mem_support_pure.mp reached
    rfl
  | activate actor =>
    simp only [Execution.environmentStep, emptyObservation, FinDist.map_pure,
      MessageNetwork.learn_empty] at reached
    cases FinDist.mem_support_pure.mp reached
    rfl
  | «include» id =>
    simp only [Execution.environmentStep, FinDist.map_pure] at reached
    cases FinDist.mem_support_pure.mp reached
    cases found : execution.network.lookup id <;>
      simp only [Execution.includePending, MessageNetwork.includePending, found]
  | application command =>
    obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
    obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ supported
    rfl

theorem empty_observation_serviceInvariant
    (emptyObservation : ∀ who pending, app.observePending who pending = FinDist.pure ∅)
    (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler (fun execution => ∀ who, execution.network.leaked who = []) where
  respond execution actor action empty who := by
    rw [app.respond_leaked, empty who]
  environment execution next command empty _ reached who := by
    rw [app.environment_leaked_of_empty_observation emptyObservation execution next command
      reached who, empty who]

/-- The restriction is an existing runtime parameter, not an additional game
semantics. No other protocol or scheduler parameter is changed. -/
theorem history_leaked_empty
    (emptyObservation : ∀ who pending, app.observePending who pending = FinDist.pure ∅)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    {state} (trace : (app.protocol initial horizon scheduler).Trace state) :
    serviceInvariant (fun execution => ∀ who, execution.network.leaked who = []) state :=
  (app.empty_observation_serviceInvariant emptyObservation scheduler).history initial horizon
    (fun _ _ _ => rfl) trace

end Interaction.ReactiveApplication
