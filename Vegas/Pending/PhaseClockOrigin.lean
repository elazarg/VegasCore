/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseActivationOrigin

/-! # Strict timer origins at actual physical clock advances -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRuntimeState

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A clock command retains an old timer or starts it strictly after the old
physical clock. This remains true when that command closes or retries a phase. -/
theorem advanceClock_activationOrigin (runtime : EventGraphRuntime graph)
    {inputs : graph.Inputs} (state next : PhaseRuntimeState graph)
    (valid : state.Invariant inputs)
    (reached : next ∈ (state.environment runtime .advanceClock).support)
    (event : graph.EventId) (entered : Nat)
    (activated : next.current.native.activatedAt event = some entered)
    (unfinished : event ∉ next.current.native.config.cut.completed) :
    state.current.native.activatedAt event = some entered ∨
      state.current.native.clock < entered := by
  unfold environment at reached
  simp only [commandAllowed, ↓reduceIte, environmentStep] at reached
  rw [PMF.support_map] at reached
  obtain ⟨native, moved, rfl⟩ := reached
  cases (PMF.mem_support_pure_iff _ _).mp moved
  have middle := environmentStep_invariant runtime state.current.native
    ({ state.current.native with clock := state.current.native.clock + 1 })
    .advanceClock valid.active ((PMF.mem_support_pure_iff _ _).mpr rfl)
  have origin := settle_activationOrigin state.phases state.generation state.entry
    (state.current.environmentResult .advanceClock
      { state.current.native with clock := state.current.native.clock + 1 })
    state.retired valid.saved middle
  rcases origin event entered activated unfinished with retained | created
  · exact Or.inl retained
  · right
    change state.current.native.clock + 1 ≤ entered at created
    omega

end Vegas.EventGraphRuntime.PhaseRuntimeState
