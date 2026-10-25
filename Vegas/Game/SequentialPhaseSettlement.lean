/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseDrain
import Vegas.Pending.PhaseSingletonTransition

/-! # Clean sequential singleton settlement and global recovery -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRuntimeState

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A completed noncommitment singleton closes cleanly before the actual global drain. -/
theorem settle_current_noncommit_singleton_eq_drain_sequential
    (phase : RuntimePhase graph.sequentialize) (remaining : List (RuntimePhase graph.sequentialize))
    (generation : Nat) (entry current : RecoveryState graph.sequentialize)
    (retired : List (RetiredCommitAttempt graph.sequentialize))
    (frontier : Frontier (⟨phase :: remaining, generation, entry, current, retired⟩ :
      PhaseRuntimeState graph.sequentialize))
    (event : graph.EventId) (only : phase.events = {event})
    (completed : event ∈ current.native.config.cut.completed)
    (kind : phase.kind ≠ .commitment) :
    (settle (phase :: remaining) generation entry current retired).current = current.drain := by
  have drained := phase.drain_eq_of_singleton_completed current event only completed
  have finished : phase.Finished current := by
    intro other inside
    have same := Finset.mem_singleton.mp ((Finset.ext_iff.mp only _).mp inside)
    subst other
    exact completed
  have high := phase.finished_prefix current frontier.positioned.2 finished
  have tail := positioned_next phase remaining current frontier.adjacent frontier.last high
  have clean : ¬ (phase.kind = .commitment ∧
      (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty) :=
    fun failed => kind failed.1
  rw [settle_clean phase remaining generation entry current retired
    (by rwa [drained]) clean, drained]
  exact settle_current_eq_drain_sequential remaining generation current current retired rfl
    ⟨tail.adjacent, tail.last, tail.positioned⟩

end Vegas.EventGraphRuntime.PhaseRuntimeState
