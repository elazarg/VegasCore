/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveSubmissionRecall
import Interaction.ReactiveServiceInvariant

/-! # Actual authored emission for every recalled submission

Every nonempty recalled response emitted its author's actual signed call.
Initialized raw history supplies that fact independently of readiness,
deadline protection, later acceptance, or any player's strategy support.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- The actual recall contains the full emitted owner envelope of each
submission. No historical deadline-fit resource is needed. -/
theorem recalled_submission_emission
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control))
    (who : Player) (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (recalled : entry ∈ control.execution.recall who)
    (material : (runtime.reactiveApplication leaks).Submission)
    (transmission : entry.action.transmission = some material) :
    ∃ message, entry.emitted = some message ∧ message.sender = who ∧
      message.payload.call = material.call.packet := by
  let app := runtime.reactiveApplication leaks
  let property := fun execution : app.Execution =>
    ∀ observer, ∀ entry ∈ execution.recall observer, ∀ material,
      entry.action.transmission = some material →
      ∃ message, entry.emitted = some message ∧ message.sender = observer ∧
        message.payload.call = material.call.packet
  have invariant : app.ServiceInvariant scheduler property := {
    respond := by
      intro execution author action prior observer entry member material submitted
      by_cases same : observer = author
      · subst observer
        rcases action with ⟨choice⟩
        cases choice with
        | none =>
            simp only [ReactiveApplication.Execution.respond, ↓reduceIte,
              List.mem_append, List.mem_singleton] at member
            rcases member with old | rfl
            · exact prior author entry old material submitted
            · cases submitted
        | some selected =>
            simp only [ReactiveApplication.Execution.respond, ↓reduceIte,
              List.mem_append, List.mem_singleton] at member
            rcases member with old | rfl
            · exact prior author entry old material submitted
            · cases Option.some.inj submitted
              exact ⟨_, rfl, rfl, rfl⟩
      · exact prior observer entry
          (app.respond_recall_other execution author observer same action ▸ member)
          material submitted
    environment := by
      intro execution next command prior _selected reached observer entry member material submitted
      rw [app.environmentStep_recall execution next command reached] at member
      exact prior observer entry member material submitted }
  exact invariant.history initial horizon
    (fun _ _ _ _ member => False.elim (List.not_mem_nil member)) trace
      who entry recalled material transmission

end Vegas.EventGraphRuntime
