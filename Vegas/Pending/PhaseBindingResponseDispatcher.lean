/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingSubmittedPreservation
import Vegas.Pending.PhaseBindingRepairProjection

/-! # Every actual response extends the directed phased repair invariants -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- Only the repaired owner's binding responses change. The replacement keeps
the original prepared slot, uses canonical absent evidence, and replaces an
unusable preparation by a value of the binding type. -/
def responseImage (repairOwner actor : Player)
    (response : (phaseApplication runtime leaks).Action) :
    (phaseApplication runtime leaks).Action :=
  if actor = repairOwner then
    match response.transmission with
    | some ⟨⟨.commitment event candidate, preparation⟩, _⟩ =>
        match nodeView graph event with
        | .bind _ payload _ _ =>
            ⟨some ⟨⟨.commitment event candidate,
              match preparation.bind (fun raw => raw.as? payload) with
              | none => some ⟨payload, L.someValue payload⟩
              | some _ => preparation⟩, .none⟩⟩
        | .sample .. | .resolve .. => response
    | _ => response
  else response

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
