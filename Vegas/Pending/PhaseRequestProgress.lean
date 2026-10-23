/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseReadyRequests

/-! # A genuine ready coordinate persists until physical resolution -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Automatic phase normalization retains every ready nonexcluded request,
including its physical namespace. Such an event prevents phase closure. -/
theorem SeedRequest.normalize {state : PhaseRuntimeState graph} {owner : Player}
    {coordinate : CommitAttemptEvent graph} (requested : state.SeedRequest owner coordinate) :
    state.normalize.attempt = state.attempt ∧ state.normalize.SeedRequest owner coordinate := by
  classical
  rcases state with ⟨phases, generation, entry, current, retired⟩
  cases phases with
  | nil =>
      obtain ⟨phase, installed, _⟩ := requested.2.1
      cases installed
  | cons phase remaining =>
      have inside : coordinate.event ∈ phase.events := by
        obtain ⟨actual, installed, member⟩ := requested.2.1
        have same : actual = phase := by
          change some phase = some actual at installed
          exact (Option.some.inj installed).symm
        exact same ▸ member
      have unfinished : coordinate.event ∉ (phase.drain current).native.config.cut.completed := by
        intro completed
        exact requested.2.2.1.1 ((phase.drainFuel_completed_survivor
          current.native.config.remaining current coordinate.event owner requested.2.2.2.1
            requested.2.2.2.2).mp completed)
      have notFinished : ¬ phase.Finished (phase.drain current) :=
        fun finished => unfinished (finished inside)
      have normalized : (⟨phase :: remaining, generation, entry, current, retired⟩ :
          PhaseRuntimeState graph).normalize =
          ⟨phase :: remaining, generation, entry, phase.drain current, retired⟩ := by
        simp only [PhaseRuntimeState.normalize, settle, ite_eq_right notFinished]
      rw [normalized]
      refine ⟨rfl, requested.1, requested.2.1, ?_, requested.2.2.2.1, ?_⟩
      · exact ⟨unfinished, requested.2.2.1.2.trans (phase.drain_completed current)⟩
      · simpa only [phase.drain_excluded] using requested.2.2.2.2

end PhaseRuntimeState

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

end Vegas.EventGraphRuntime
