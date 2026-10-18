/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveCompleteInput
import Interaction.ReactiveServiceInvariant

/-! # Empty complete observations certify the absence of earlier transmissions -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- At a complete actual decision, empty own outputs, leaked packets and
ledger rule out every earlier submission, including rejected packets. -/
theorem complete_decision_inputs_eq_nil
    (complete : app.observePending = MessageNetwork.completePendingObservation)
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (who : Principal) (active : control.actor = some who)
    (own : app.outputs (control.execution.recall who) = [])
    (leaked : (control.execution.observe app who).messages.leaked = [])
    (ledger : (control.execution.observe app who).messages.ledger = []) :
    control.execution.network.inputs = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro message member
  by_cases authored : message.sender = who
  · have output : message ∈ app.outputs (control.execution.recall who) := by
      rw [← app.history_inputRecall initial horizon scheduler trace who]
      exact List.mem_filter.mpr ⟨member, by simp [authored]⟩
    rw [own] at output
    exact List.not_mem_nil output
  · have visible := app.complete_decision_submitted_visible complete scheduler initial
      horizon control trace who active message member authored
    rw [leaked, ledger] at visible
    exact visible.elim List.not_mem_nil List.not_mem_nil

/-- In an actual raw history, an empty input log forces every remembered
response to be literal silence. No policy or service honesty is assumed. -/
theorem empty_inputs_recorded_silent
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (empty : control.execution.network.inputs = [])
    (who : Principal) (entry : app.PlayerEntry)
    (member : entry ∈ control.execution.recall who) : entry.action = ⟨none⟩ := by
  let predicate : app.Execution → Prop := fun execution =>
    execution.network.inputs = [] → ∀ who entry,
      entry ∈ execution.recall who → entry.action = ⟨none⟩
  have invariant : app.ServiceInvariant scheduler predicate := by
    constructor
    · rintro execution actor ⟨transmission⟩ valid inputs observer response recorded
      cases transmission with
      | none =>
          have prior := valid inputs
          by_cases same : observer = actor
          · subst observer
            simp only [Execution.respond, ↓reduceIte, List.mem_append,
              List.mem_singleton] at recorded
            rcases recorded with earlier | rfl
            · exact prior actor response earlier
            · rfl
          · rw [app.respond_recall_other execution actor observer same] at recorded
            exact prior observer response recorded
      | some material =>
          simp [Execution.respond, MessageNetwork.submit] at inputs
    · intro execution next command valid _ moved inputs observer response recorded
      rw [app.environmentStep_inputs execution next command moved] at inputs
      rw [app.environmentStep_recall execution next command moved] at recorded
      exact valid inputs observer response recorded
  have faithful := invariant.history initial horizon
    (fun _ _ _ _ _ recorded => (List.not_mem_nil recorded).elim) trace
  exact faithful empty who entry member

end Interaction.ReactiveApplication
