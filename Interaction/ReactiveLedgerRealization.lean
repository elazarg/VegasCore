/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveLedgerPolicy
import Interaction.ReactiveRecallInvariant
import Interaction.ReactiveEnvironmentStep

/-! # Ledger policies at every legal decision without pending delivery

The invariant concerns all raw responses, including deviations. Remembered
views are handled by the existing recorded-response origin theorem. Thus
ledger projection preserves every policy at every initialized legal decision,
independently of game utilities, prescribed play or equilibrium beliefs.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)
  (unobserved : ∀ who pending, app.observePending who pending = PMF.pure ∅)

private def noPendingKnowledge (execution : app.Execution) : Prop :=
  ∀ who, execution.network.leaked who = []

include unobserved

private theorem noPendingKnowledgeInvariant (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler (noPendingKnowledge app) where
  respond execution who action valid := by
    rcases action with ⟨transmission⟩
    cases transmission <;> exact valid
  environment execution next command valid _ reached := by
    apply app.environmentStep_cases execution next command reached
      (predicate := fun _ next => noPendingKnowledge app next)
    · exact valid
    · intro who selected supported
      rw [unobserved] at supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      simpa only [noPendingKnowledge, MessageNetwork.learn_empty] using valid
    · intro id
      cases found : execution.network.lookup id <;>
        simpa only [noPendingKnowledge, Execution.includePending,
          MessageNetwork.includePending, found] using valid
    · exact fun _ _ _ => valid

theorem pendingKnowledge_empty (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (who : Principal) : control.execution.network.leaked who = [] :=
  (noPendingKnowledgeInvariant app unobserved scheduler).history initial horizon
    (fun _ _ _ => rfl) trace who

omit unobserved [DecidableEq Principal] in
theorem PlayerView.ledgerOnly_eq_self (view : app.PlayerView)
    (empty : view.messages.leaked = []) : view.ledgerOnly app = view := by
  cases view with
  | mk messages application receipts =>
      cases messages with
      | mk leaked ledger => cases empty; rfl

theorem ledgerPolicy_eq_at_history (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (who : Principal) (policy : app.Policy) :
    app.ledgerPolicy policy (control.execution.recall who) (control.execution.observe app who) =
      policy (control.execution.recall who) (control.execution.observe app who) := by
  have current : (control.execution.observe app who).ledgerOnly app =
      control.execution.observe app who :=
    PlayerView.ledgerOnly_eq_self app _
      (app.pendingKnowledge_empty unobserved initial horizon scheduler control trace who)
  have past : (control.execution.recall who).map (PlayerEntry.ledgerOnly app) =
      control.execution.recall who := by
    calc
      _ = (control.execution.recall who).map id := by
        apply List.map_congr_left
        intro entry member
        obtain ⟨before, ⟨earlier⟩, _active, seen⟩ :=
          app.recorded_response_prefix initial horizon scheduler control trace who entry member
        have empty : entry.beforeView.messages.leaked = [] := by
          rw [seen]
          exact app.pendingKnowledge_empty unobserved initial horizon scheduler before earlier who
        have beforeView := PlayerView.ledgerOnly_eq_self app entry.beforeView empty
        cases entry
        exact congrArg (fun view => (⟨view, _, _⟩ : app.PlayerEntry)) beforeView
      _ = _ := List.map_id' _
  simp only [ledgerPolicy, current, past]

end Interaction.ReactiveApplication
