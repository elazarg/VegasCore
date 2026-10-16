/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingRecallMemory
import Vegas.Pending.PhaseBindingRepairFrame

/-! # Actual operational observations in directed binding repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- A physical repair preserves the current erased observation, including
every slot's freshness. This does not assert equality of past observations. -/
theorem operationalView_eq (frame : Frame runtime leaks memory owner original repaired) :
    phaseOperationalView runtime leaks (original.observe (phaseApplication runtime leaks) owner) =
      phaseOperationalView runtime leaks
        (repaired.observe (phaseApplication runtime leaks) owner) := by
  change (⟨original.application.publicView, original.network.observe owner, original.receipts,
      fun slot => match original.application.current.native.candidates.lookup (owner, slot) with
        | .fresh => true | _ => false⟩ : PhaseOperationalView graph) =
    ⟨repaired.application.publicView, repaired.network.observe owner, repaired.receipts,
      fun slot => match repaired.application.current.native.candidates.lookup (owner, slot) with
        | .fresh => true | _ => false⟩
  rw [frame.publicView, frame.network, frame.receipts]
  congr 1
  funext slot
  have slots : original.application.current.native.candidates.lookup (owner, slot) = .fresh ↔
      repaired.application.current.native.candidates.lookup (owner, slot) = .fresh :=
    frame.live.slots slot
  cases first : original.application.current.native.candidates.lookup (owner, slot) <;>
    cases second : repaired.application.current.native.candidates.lookup (owner, slot) <;>
      simp_all

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
