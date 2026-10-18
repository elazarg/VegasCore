/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalCompletion

/-! # A genuinely unresolved original binding is a ready native request -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- The ready-or-resolved split follows from actual native geometry. It needs
no equilibrium reach, posterior or assumption that the current phase survives. -/
theorem original_binding_request_of_unresolved (selected : app.Scheduler)
    (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current)) (owner : Player)
    (unresolved : ¬ (originalCoordinate owner).Resolved current.execution.application) :
    current.execution.application.SeedRequest owner (originalCoordinate owner) := by
  have generationZero : current.execution.application.attempt.generation = 0 := by
    by_contra nonzero
    apply unresolved
    exact Or.inl (by change 0 < _; omega)
  have phaseZero : current.execution.application.attempt.phase = 0 := by
    by_contra nonzero
    apply unresolved
    exact Or.inr (Or.inl (by change 0 < _; omega))
  have original : current.execution.application.attempt = originalAttempt := by
    cases address : current.execution.application.attempt with
    | mk phase generation =>
        simp only [address] at generationZero phaseZero
        simp only [generationZero, phaseZero, originalAttempt]
  have unfinished : bindingEvent owner ∉
      current.execution.application.current.native.config.cut.completed := by
    intro completed
    exact unresolved (Or.inr (Or.inr ⟨original.symm, completed⟩))
  have phases := original_phases selected current trace original
  have inside : bindingEvent owner ∈ commitmentPhase.events := by
    apply (RuntimePhase.mem_events commitmentPhase _).mpr
    change 0 ≤ owner.val ∧ owner.val < 3
    exact ⟨Nat.zero_le _, owner.isLt⟩
  have actor : graph.actor? (bindingEvent owner) = some owner := binding_actor owner
  have requested := raw_phase_event_request selected current trace commitmentPhase
    (by rw [phases]; rfl) (Or.inl rfl) (bindingEvent owner) inside owner actor unfinished
  change current.execution.application.SeedRequest owner
    ⟨originalAttempt, bindingEvent owner⟩
  rw [← original]
  exact requested

end Vegas.Examples.CommitSeedBroadcast
