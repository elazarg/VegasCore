/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveRawRoundTrace
import GameTheoryExtensions.Analysis.Protocol.SupportedChoiceContinuation

/-! # Remaining player-response opportunities in the actual reactive protocol -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- A scheduler round can activate at most one response. A pending activation
adds its response to the remaining scheduler-round budget. -/
def remainingResponses (horizon : Nat) : app.ProtocolState → Nat
  | none => horizon
  | some control => control.remaining + if control.actor.isSome then 1 else 0

/-- Only a pending player response can depend on the behavioral profile. -/
def responseCharge (state : app.ProtocolState) : Nat :=
  if (app.actor state).isSome then 1 else 0

omit [DecidableEq Principal] in
theorem responseCharge_le_one (state : app.ProtocolState) : app.responseCharge state ≤ 1 := by
  unfold responseCharge
  split <;> omega

omit [DecidableEq Principal] in
theorem remainingResponses_le_rank (horizon : Nat) (state : app.ProtocolState) :
    app.remainingResponses horizon state ≤ app.rank horizon state := by
  cases state with
  | none => change horizon ≤ 2 * horizon + 1; omega
  | some control =>
    change control.remaining + (if control.actor.isSome then 1 else 0) ≤
      2 * control.remaining + (if control.actor.isSome then 1 else 0)
    omega

/-- Actual initialization and environment kernels cost no response. A player
step spends one unit, independently of whether it emits a packet. -/
theorem remainingResponses_step (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler)
    (before after : app.ProtocolState) (joint : Principal → Option app.Action)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    app.remainingResponses horizon after + app.responseCharge before ≤
      app.remainingResponses horizon before := by
  cases before with
  | none =>
    obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
    exact Nat.le_refl _
  | some control =>
    rcases control with ⟨remaining, actor, execution⟩
    cases actor with
    | some who =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact Nat.le_refl _
    | none =>
      cases remaining with
      | zero =>
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact Nat.le_refl _
      | succ remaining =>
        obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
        obtain ⟨next, _, rfl⟩ := PMF.support_map .. ▸ moved
        cases command <;> simp [remainingResponses, responseCharge, actor, Command.actor?]

variable [Fintype Principal]

namespace ResponseMenu

variable {app}

variable (menu : app.ResponseMenu) (initial : PMF app.State) (horizon : Nat)
  (scheduler : app.Scheduler)

open Classical in
theorem active_card (state : app.ProtocolState) :
    (Finset.univ.filter ((menu.protocol initial horizon scheduler).active state)).card =
      app.responseCharge state := by
  classical
  cases state with
  | none => simp [protocol, actor, responseCharge]
  | some control =>
    cases acting : control.actor with
    | none => simp [protocol, actor, responseCharge, acting]
    | some who =>
      have filtered :
          Finset.univ.filter ((menu.protocol initial horizon scheduler).active (some control)) =
            {who} := by
        ext other
        simp [protocol, actor, acting, eq_comm]
      rw [filtered]
      simp [responseCharge, actor, acting]

omit [Fintype Principal] in
theorem remainingResponses_le_horizon_add_one
    (history : (menu.protocol initial horizon scheduler).History) :
    app.remainingResponses horizon history.state ≤ horizon + 1 := by
  cases state : history.state with
  | none => simp [remainingResponses]
  | some control =>
    have trace := menu.toRawTrace initial horizon scheduler history.trace
    rw [state] at trace
    have accounted := app.raw_trace_horizon initial horizon scheduler trace
    change control.remaining + (if control.actor.isSome then 1 else 0) ≤ horizon + 1
    split <;> omega

/-- At every initialization or environment step the full one-step history law
is independent of the player profile, including stochastic nature branches. -/
theorem run_one_eq_of_no_actor
    (source target : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (history : (menu.protocol initial horizon scheduler).History)
    (inactive : app.actor history.state = none) :
    (menu.information initial horizon scheduler).runBehavioralFrom source 1 history =
      (menu.information initial horizon scheduler).runBehavioralFrom target 1 history := by
  classical
  apply PMF.WithinTV.eq_of_zero
  let model := menu.information initial horizon scheduler
  have lower := model.runBehavioralFrom_one_domination_of_active_choices
    source target 1 (by norm_num) history
      (fun who active => by
        change app.actor history.state = some who at active
        rw [inactive] at active
        cases active)
  simpa only [sub_self] using PMF.WithinTV.of_domination _ _ 1 le_rfl
    (by simpa only [one_pow] using lower)

end ResponseMenu
end Interaction.ReactiveApplication
