/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialRuntimePhases
import Vegas.Pending.PhaseDrainCorrespondence

/-! # Sequential phase settlement is the actual recovery drain

When the saved and live exclusions agree, source-order readiness and the real
phase frontier determine the exact native recovery endpoint. No observation or
strategy equivalence is asserted for the additional phase metadata.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRuntimeState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- The actual sequential engine supplies both uniqueness and quiescence for
the primitive recovery-drain correspondence. -/
theorem settle_current_eq_drain_sequential
    (phases : List (RuntimePhase graph.sequentialize)) (generation : Nat)
    (entry current : RecoveryState graph.sequentialize)
    (retired : List (RetiredCommitAttempt graph.sequentialize))
    (sameExcluded : entry.excluded = current.excluded)
    (frontier : Frontier (⟨phases, generation, entry, current, retired⟩ :
      PhaseRuntimeState graph.sequentialize)) :
    (settle phases generation entry current retired).current = current.drain :=
  settle_current_eq_drain phases generation entry current retired sameExcluded
    (fun cut _ _ leftReady rightReady => cut.ready_unique leftReady rightReady)
    (settle_global_quiescent_sequential phases generation entry current retired frontier)

end Vegas.EventGraphRuntime.PhaseRuntimeState
