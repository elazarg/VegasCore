/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveAuditContinuation
import Interaction.ReactiveResponseMenu

/-! # Terminal audit bounds allow unbounded nonterminal rewards -/

noncomputable section

namespace InteractionTests.TerminalAudit

open Interaction GameTheory GameTheory.Protocol GameTheory.Math.Probability
  GameTheory.Enforcement

variable (app : ReactiveApplication Unit)

private def base (state : app.ProtocolState) (_ : Unit) : ℝ :=
  match state with
  | none => 0
  | some control =>
      if control.remaining = 0 ∧ control.actor = none then 7 else control.remaining

private def audit (_ : List app.TrafficRecord) : PMF (Unit → Bool) :=
  PMF.pure fun _ => true

/-- Every terminal state is covered, including horizon exhaustion with no
application-completion premise. -/
theorem terminal_base_bound (state : app.ProtocolState) (stopped : app.terminal state) :
    |base app state ()| ≤ 7 := by
  cases state with
  | none => exact stopped.elim
  | some control => simp only [ReactiveApplication.terminal] at stopped
                    simp [base, stopped]

theorem nonterminal_base_unbounded (initialState : app.State) :
    ¬ ∃ bound : ℝ, ∀ state, |base app state ()| ≤ bound := by
  rintro ⟨bound, bounded⟩
  obtain ⟨remaining, larger⟩ := exists_nat_gt bound
  have upper := bounded (some ⟨remaining + 1, none,
    ReactiveApplication.Execution.initial app initialState⟩)
  simp [base, Nat.cast_add, Nat.cast_one] at upper
  linarith [le_abs_self ((remaining : ℝ) + 1)]

/-- A positive audit charge remains in the payoff at an exhausted native
terminal even though the application state has not changed. -/
theorem exhausted_terminal_charged (initialState : app.State) :
    let state : app.ProtocolState := some ⟨0, none,
      ReactiveApplication.Execution.initial app initialState⟩
    app.terminal state ∧
      TerminalAudit.utility (base app) app.stateTraffic (audit app) (fun _ => 3) state () = 4 := by
  dsimp only
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  change (7 : ℝ) - ((((PMF.pure (fun _ : Unit => true)).map
    (fun verdict => verdict ())) true).toReal) * 3 = 4
  rw [PMF.pure_map, PMF.pure_apply_self]
  norm_num

/-- The actual behavioral continuation context integrates this payoff under
every unilateral replacement despite the unbounded nonterminal reward. -/
theorem continuation_integrable
    (menu : app.ResponseMenu) (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler)
    (assessment : (menu.information initial horizon scheduler).BehavioralAssessment)
    (site : (menu.information initial horizon scheduler).InformationSite ())
    (alternative : (menu.information initial horizon scheduler).BehavioralPolicy ()) :
    (assessment.continuationContext (menu.bounded initial horizon scheduler).wellFoundedHistories
      site (fun final => TerminalAudit.utility (base app) app.stateTraffic (audit app)
        (fun _ => 3) final.state ())).IntegrableAt alternative := by
  apply assessment.continuationContext_integrable_of_bounded_terminal _ site _ 10
  intro final stopped
  have bound := TerminalAudit.utility_abs_le (base app) app.stateTraffic (audit app)
    (fun _ => 3) final.state () (terminal_base_bound app final.state stopped)
  norm_num at bound
  exact bound

end InteractionTests.TerminalAudit
