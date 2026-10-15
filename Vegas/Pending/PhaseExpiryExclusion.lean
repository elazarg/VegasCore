/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseResolution

/-! # Physical expiry permanently excludes its actual requested owner -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRuntimeState

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Expiring a due genuine request excludes its owner before normalization.
The exclusion survives any immediate rollback, including retirement of the
expired semantic event and automatic completion of the remaining phase. -/
theorem expire_excludes_of_request (runtime : EventGraphRuntime graph)
    (state next : PhaseRuntimeState graph) (owner : Player)
    (coordinate : CommitAttemptEvent graph) (request : state.SeedRequest owner coordinate)
    (entered : Nat) (stamp : state.current.native.activatedAt coordinate.event = some entered)
    (due : runtime.deadline coordinate.event ≤ state.current.native.clock - entered)
    (supported : next ∈ (state.environment runtime (.expire coordinate.event)).support) :
    owner ∈ next.current.excluded := by
  obtain ⟨_attempt, ⟨phase, installed, inside⟩, ready, owned, _unexcluded⟩ := request
  change state.phases.head? = some phase at installed
  have allowed : state.commandAllowed (.expire coordinate.event) = true := by
    simp only [commandAllowed, installed, Option.any_some, inside, decide_true]
  unfold environment at supported
  rw [ite_eq_left allowed, PMF.mem_support_map_iff] at supported
  obtain ⟨native, nativeSupport, rfl⟩ := supported
  have completed := environmentStep_expire_complete runtime state.current.native native
    coordinate.event ready (by simp only [owned, Option.isSome_some]) entered stamp due
      nativeSupport
  change owner ∈ (settle state.phases state.generation state.entry
    (state.current.environmentResult (.expire coordinate.event) native)
      state.retired).current.excluded
  rw [(settle_physical _ _ _ _ _).1,
    RecoveryState.environmentResult_expire_completed state.current coordinate.event native
      ready.1 completed owned]
  exact Finset.mem_insert_self _ _

end Vegas.EventGraphRuntime.PhaseRuntimeState
