/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveCompleteObservation
import Interaction.ReactiveTrafficIdentity

/-! # Complete decision inputs identify every submitted envelope -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- Foreign inputs are visible and own inputs are retained in literal recall.
Thus equal complete decision inputs identify the entire submitted envelope set,
including rejected receipts and hidden preparation aliases with the same packet. -/
theorem complete_decision_inputs_congr
    (complete : app.observePending = MessageNetwork.completePendingObservation)
    (initial : PMF app.State) (horizon : Nat)
    (leftScheduler rightScheduler : app.Scheduler) (left right : app.Control)
    (leftTrace : (app.protocol initial horizon leftScheduler).Trace (some left))
    (rightTrace : (app.protocol initial horizon rightScheduler).Trace (some right))
    (who : Principal) (leftActive : left.actor = some who) (rightActive : right.actor = some who)
    (recalled : left.execution.recall who = right.execution.recall who)
    (observed : left.execution.observe app who = right.execution.observe app who) :
    ∀ message, message ∈ left.execution.network.inputs ↔
      message ∈ right.execution.network.inputs := by
  have transfer (firstScheduler secondScheduler : app.Scheduler) (first second : app.Control)
      (firstTrace : (app.protocol initial horizon firstScheduler).Trace (some first))
      (secondTrace : (app.protocol initial horizon secondScheduler).Trace (some second))
      (active : first.actor = some who)
      (past : first.execution.recall who = second.execution.recall who)
      (view : first.execution.observe app who = second.execution.observe app who)
      (message : Message Principal app.Payload)
      (member : message ∈ first.execution.network.inputs) :
      message ∈ second.execution.network.inputs := by
    by_cases own : message.sender = who
    · have output : message ∈ app.outputs (first.execution.recall who) := by
        rw [← app.history_inputRecall initial horizon firstScheduler firstTrace who]
        exact List.mem_filter.mpr ⟨member, by simp [own]⟩
      rw [past, ← app.history_inputRecall initial horizon secondScheduler secondTrace who]
        at output
      exact (List.mem_filter.mp output).1
    · have visible := app.complete_decision_submitted_visible complete firstScheduler initial
        horizon first firstTrace who active message member own
      have retained := app.retained_envelopes_mem_inputs second.execution
        (app.history_provenance initial horizon secondScheduler secondTrace)
        (app.history_inputRecall initial horizon secondScheduler secondTrace)
      rw [view] at visible
      exact visible.elim (retained.leaked who message) (retained.ledger message)
  intro message
  exact ⟨transfer leftScheduler rightScheduler left right leftTrace rightTrace leftActive
    recalled observed message,
    transfer rightScheduler leftScheduler right left rightTrace leftTrace rightActive
      recalled.symm observed.symm message⟩

end Interaction.ReactiveApplication
