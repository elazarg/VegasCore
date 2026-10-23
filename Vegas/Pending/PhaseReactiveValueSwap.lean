/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSwapApplication
import Vegas.Pending.ReactiveValueSwap

/-! # Full physical executions under a phased hidden-value swap -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

namespace HiddenSwap

variable (swap : HiddenSwap graph)

/-- Only hidden preparation data changes; physical packet fields stay fixed. -/
def phaseAction (response : (phaseApplication runtime leaks).Action) :
    (phaseApplication runtime leaks).Action :=
  ⟨response.transmission.map (WitnessedSubmission.swap swap)⟩

/-- The native private projection changes while the entire phase public view is fixed. -/
def phaseView (observed : (phaseApplication runtime leaks).PlayerView) :
    (phaseApplication runtime leaks).PlayerView :=
  ⟨observed.messages, (PlayerView.swap swap observed.application.1, observed.application.2),
    observed.receipts⟩

def phaseEntry (entry : (phaseApplication runtime leaks).PlayerEntry) :
    (phaseApplication runtime leaks).PlayerEntry :=
  ⟨swap.phaseView entry.beforeView, swap.phaseAction entry.action, entry.emitted⟩

/-- Preserve the full physical network, receipts and scheduler recall, and map
all saved/live/archive values together with each original private response. -/
def phaseExecution (current : (phaseApplication runtime leaks).Execution) :
    (phaseApplication runtime leaks).Execution :=
  ⟨current.application.swap swap, current.network, current.receipts,
    fun who => (current.recall who).map swap.phaseEntry, current.environmentRecall⟩

@[simp] theorem phaseExecution_application (current : (phaseApplication runtime leaks).Execution) :
    (swap.phaseExecution current).application = current.application.swap swap := rfl

@[simp] theorem phaseExecution_network (current : (phaseApplication runtime leaks).Execution) :
    (swap.phaseExecution current).network = current.network := rfl

end HiddenSwap
end Vegas.EventGraphRuntime
