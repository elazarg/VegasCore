/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDisclosure
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.EventHandleObservation

/-! # Stable inputs of a submitted disclosure

Submission and inclusion preserve the application cache and every completed
read field. Accepted associations at those fields are immutable as well. Thus
later unrelated traffic cannot change either the selected disclosure packet or
its deferred-guard result.
-/

noncomputable section

namespace Vegas.EventGraphRuntime
open GameTheory.Math.Probability Interaction EventGraph
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem handle_accepted_of_present (runtime : EventGraphRuntime graph)
    (state next : State graph) (field : graph.Field)
    (present : (state.config.store field).isSome = true)
    (message : Message Player (Payload graph))
    (handled : handle runtime state message = some next) :
    next.accepted field = state.accepted field := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at handled
  | opening event chosen raw =>
      rw [(handle_resolution_tables runtime state next _ (by intros; simp) handled).1]
  | commitment event chosen =>
      have tables := (handle_commitment_tables runtime state next id event chosen handled).2.1
      have different : field ≠ .inr event := by
        intro same
        subst field
        have completed := (state.config.output_available event).mp present
        obtain ⟨actual, addressed, ready, action, supported⟩ := handle_config_mem_step runtime
          state next ⟨id, .commitment event chosen⟩ handled
        have equal : actual = event := by simpa only [Payload.event?, Option.some.injEq]
          using addressed.symm
        subst actual
        exact ready.1 completed
      rw [tables, Function.update_of_ne different]

end Vegas.EventGraphRuntime
