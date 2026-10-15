/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourceCheckpoint

/-! # The actual initialized dispatcher has its single-draw source checkpoint -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem phaseInitial_eq_raw {graph : Vegas.EventGraph Player L}
    (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    PhaseRuntimeState.initial plan inputs =
      (⟨plan.phases, 0, ⟨EventGraphRuntime.State.initial inputs, ∅⟩,
        ⟨EventGraphRuntime.State.initial inputs, ∅⟩, []⟩ : PhaseRuntimeState graph) := by
  unfold PhaseRuntimeState.initial
  cases phases : plan.phases with
  | nil => rfl
  | cons phase remaining =>
      have drained : phase.drain ⟨EventGraphRuntime.State.initial inputs, ∅⟩ =
          (⟨EventGraphRuntime.State.initial inputs, ∅⟩ : RecoveryState graph) := by
        apply phase.drainFuel_eq_of_clear
        intro event eligible
        obtain ⟨owner, _acting, excluded⟩ := eligible.2.owned
        exact Finset.notMem_empty owner excluded
      have unfinished : ¬ phase.Finished
          (⟨EventGraphRuntime.State.initial inputs, ∅⟩ : RecoveryState graph) := by
        intro finished
        let event : graph.EventId := ⟨phase.low, lt_of_lt_of_le phase.nonempty phase.bounded⟩
        have member := (phase.mem_events event).mpr ⟨Nat.le_refl _, phase.nonempty⟩
        exact Finset.notMem_empty event (finished member)
      simp only [PhaseRuntimeState.settle, drained, unfinished, ↓reduceIte]

/-- The actual initialized dispatcher has the same source checkpoint as its
single supported setup draw. Empty exclusion cannot service any owned slot. -/
def RecoverySourceCheckpoint.initialized (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode)
    (plan : RuntimePhasePlan ((toEventGraph setup.program).withMode mode))
    (initial : State L setup.context) (supported : initial ∈ setup.initialLaw.support) :
    RecoverySourceCheckpoint setup mode
      (PhaseRuntimeState.initial plan (encodeInputs initial)) := by
  rw [phaseInitial_eq_raw]
  exact RecoverySourceCheckpoint.initial setup mode plan initial supported

end Vegas
