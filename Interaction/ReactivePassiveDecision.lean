/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePassiveContinuation
import Interaction.ReactiveLocalContinuation

/-! # The last observed response of a player

After a player's last activation, its complete behavioral continuation
depends only on its current response lottery and the other players' future
policies. After the game's last activation, all future policies are irrelevant.
Both identities hold on off-path histories and with arbitrary passive inclusion.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- At a player's last response, the exact endpoint law retains every other
player's future policy. Only the focal player's later policy is irrelevant. -/
theorem run_last_response_of_unactivated
    (cursor : Nat)
    (who : Principal)
    (absent : ∀ past view, cursor ≤ past.length →
      ∀ command ∈ (scheduler past view).support, command.actor? app ≠ some who)
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol initial horizon scheduler).History)
    (remaining : Nat) (execution : app.Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (later : cursor ≤ execution.environmentRecall.length) :
    ((menu.information initial horizon scheduler).runBehavioralFrom profile
      (2 * horizon + 1) history).map History.state =
      ((profile who ((menu.information initial horizon scheduler).infoOf who
        history.trace)).map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
          (app.runRounds scheduler
            (Function.update (menu.decodeProfile initial horizon scheduler profile) who
              app.silentPolicy) remaining
            (execution.respond app who response)).map app.finished := by
  classical
  have raw : (app.protocol initial horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) :=
    current ▸ menu.toRawTrace initial horizon scheduler history.trace
  have bounded := app.trace_bound initial horizon scheduler raw
  have enough : app.rank horizon history.state ≤ 2 * horizon + 1 := by
    rw [current]
    omega
  have split := menu.run_local_law_finish initial horizon scheduler profile history
    who remaining execution current (profile who _) (2 * horizon) enough
  rw [InformationModel.BehavioralPolicy.withLaw_eq_self, Profile.update_eq_self] at split
  refine split.trans ?_
  apply bind_congr_on_support _
  intro response _supported
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind]
  have responded : cursor ≤ (execution.respond app who response).environmentRecall.length := by
    rw [app.respond_environmentRecall]
    exact later
  rw [app.continuation_policy_independent_of_unactivated scheduler cursor who absent
    _ (Function.update (menu.decodeProfile initial horizon scheduler profile) who app.silentPolicy)
    (by intro actor different; rw [Function.update_of_ne different]) remaining _ responded]

/-- The exact endpoint law at the last response of the entire game. The
passive hypothesis concerns physical commands, not payoff comparisons or beliefs. -/
theorem run_last_response
    (cursor : Nat)
    (passive : ∀ past view, cursor ≤ past.length →
      ∀ command ∈ (scheduler past view).support, command.actor? app = none)
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol initial horizon scheduler).History)
    (who : Principal) (remaining : Nat) (execution : app.Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (later : cursor ≤ execution.environmentRecall.length) :
    ((menu.information initial horizon scheduler).runBehavioralFrom profile
      (2 * horizon + 1) history).map History.state =
      ((profile who ((menu.information initial horizon scheduler).infoOf who
        history.trace)).map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
          (app.runRounds scheduler (fun _ => app.silentPolicy) remaining
            (execution.respond app who response)).map app.finished := by
  rw [menu.run_last_response_of_unactivated initial horizon scheduler cursor who
    (by intro past view late command selected; rw [passive past view late command selected];
        simp) profile history remaining execution current later]
  apply bind_congr_on_support
  intro response _
  have responded : cursor ≤ (execution.respond app who response).environmentRecall.length := by
    rwa [app.respond_environmentRecall]
  rw [app.passive_continuation_policy_independent scheduler cursor passive
    _ (fun _ => app.silentPolicy) remaining _ responded]

end Interaction.ReactiveApplication.ResponseMenu
