/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkSource
import Vegas.Game.SourceServiceInitialReadout
import Vegas.Game.SourceServiceRecordedResolutionAlignment

/-! # Bob's actual initialized TRUE binding

The fixed input reference retains Bob's authentic TRUE value at every legal RAW
history. The literal last resolution has no guard checks. Thus its operational
TRUE result is derived from initialized native input, independently of native
beliefs, source-policy support, foreign packets or private opportunity risk.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

/-- The actual immutable input reference used by Bob's compiled resolution. -/
def bobInitialBinding : FieldRef nativeGraph.layout (.binding bob BaseTy.bool) :=
  (ContextRefs.initial setup.context (outputLayout setup.program)).get (.there .here)

/-- The literal compiled Bob node uses his initialized binding and no guards. -/
theorem bob_resolution_code :
    cast (congrArg (EventGraph.EventCode nativeGraph.layout)
      (show nativeGraph.outputLayout bobResolution = .publication BaseTy.bool from rfl))
      (nativeGraph.nodes bobResolution) = EventCode.resolve (L := simpleExpr)
        (layout := nativeGraph.layout) bob BaseTy.bool bobInitialBinding [] := by
  rfl

/-- Every supported initial draw has the same typed TRUE binding at Bob,
although Alice's immutable private type remains random. -/
theorem bob_initial_binding_true_of_readout
    (config : nativeGraph.Config) (initial : State simpleExpr setup.context)
    (selected : initial ∈ setup.initialLaw.support)
    (read : sourceInitialReadout setup config = some initial) :
    bobInitialBinding.get? config.store = some (.success true) := by
  have agree : (ContextRefs.initial setup.context (outputLayout setup.program)).Agrees
      initial config.store := decodeState?_agrees _ _ initial read
  have bound := agree (.there .here)
  change initial ∈ (mix (1 / 4) (by norm_num) (by norm_num)
    (PMF.pure (sourceInitial true)) (PMF.pure (sourceInitial false))).support at selected
  rcases support_mix_subset _ _ _ _ _ selected with high | low
  · cases (PMF.mem_support_pure_iff _ _).mp high
    exact bound
  · cases (PMF.mem_support_pure_iff _ _).mp low
    exact bound

/-- Actual raw-history provenance supplies the same persistent input, so TRUE
is operationally successful at the real current configuration. -/
theorem bob_true_resolution_of_history
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph))
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) :
    EventGraph.EventCode.resolveOutput? bobInitialBinding [] true
      control.execution.application.config.store = some (.success true) := by
  obtain ⟨initial, selected, read⟩ := sourceInitialReadout_history setup leaks horizon scheduler
    control trace
  have stored := bob_initial_binding_true_of_readout control.execution.application.config
    initial selected read
  unfold EventGraph.EventCode.resolveOutput?
  rw [stored]
  rfl

end Vegas.PrivateResolutionFork
