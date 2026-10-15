/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseExclusionRecord

/-! # Exclusion evidence at genuine native transition endpoints -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

theorem ExclusionRecord.inclusionResult (runtime : EventGraphRuntime graph)
    (state : PhaseRuntimeState graph) (valid : state.ExclusionRecord)
    (message : Message Player (Payload graph)) (native : State graph)
    (authorized : state.allows message.payload = true)
    (accepted : EventGraphRuntime.handle runtime state.current.native message = some native) :
    ExclusionRecord
      {state with current := state.current.inclusionResult message.payload native} := by
  refine ⟨raw_handle_frontier runtime state valid.frontier message native authorized accepted,
    valid.saved, valid.active.step (completionStep_handle runtime _ native _ accepted), ?_⟩
  intro phase member
  exact (valid.installed phase member).inclusionResult runtime message native accepted

/-- A supported permitted native environment result has exact evidence before closure. -/
theorem ExclusionRecord.environmentResult (runtime : EventGraphRuntime graph)
    (state : PhaseRuntimeState graph) (valid : state.ExclusionRecord)
    (command : EnvironmentCommand graph) (native : State graph)
    (authorized : state.commandAllowed command = true)
    (supported : native ∈ (environmentStep runtime state.current.native command).support) :
    ExclusionRecord {state with current := state.current.environmentResult command native} := by
  refine ⟨raw_environment_frontier runtime state valid.frontier command native authorized supported,
    valid.saved, valid.active.step (completionStep_environmentStep runtime _ native command
      supported), ?_⟩
  intro phase member
  exact (valid.installed phase member).environmentResult runtime command native supported

end PhaseRuntimeState
end Vegas.EventGraphRuntime
