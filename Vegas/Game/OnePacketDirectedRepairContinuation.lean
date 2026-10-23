/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketDirectedRepairSteps

/-! # Directed binding repair through delayed execution

Silent owner responses, clock advances, and delayed inclusion preserve the
operational private-memory frame. These are actual execution operations; no
fixed roster or immediate-inclusion schedule is required.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

namespace DirectedBindingFrame

variable {memory : BindingMemory (runtime setup) leaks} {owner : Player}
  {original repaired : (application setup leaks).Execution}

/-- Advancing the actual clock preserves the repaired owner's recorded inputs. -/
theorem advanceClock (frame : DirectedBindingFrame memory owner original repaired) :
    let app := application setup leaks
    DirectedBindingFrame memory owner
      { original with
        application := { original.application with clock := original.application.clock + 1 }
        environmentRecall := original.environmentRecall ++
          [⟨original.observeEnvironment app, .application .advanceClock⟩] }
      { repaired with
        application := { repaired.application with clock := repaired.application.clock + 1 }
        environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment app, .application .advanceClock⟩] } :=
  ⟨frame.toFrame.advanceClock, frame.recalled⟩

/-- A delayed inclusion of the same actual opaque envelope preserves the
operational frame. Its remembered original result and successful-value
agreement are exactly the candidate facts retained by the repair frame. -/
theorem pending_binding_inclusion
    (frame : DirectedBindingFrame memory owner original repaired)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (id : MessageId Player) (candidate : Handle (graph setup))
    (sender : id.1 = owner) (owned : candidate.1 = owner)
    (found : original.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, none, some ⟨event⟩⟩⟩)
    (ready : original.application.config.cut.Ready event)
    (timely : original.application.WithinDeadline (runtime setup) event)
    (vacant : original.application.accepted (.inr event) = none)
    (unused : original.application.HandleUnused candidate)
    (leftFixed : original.application.candidates.lookup candidate ≠ .fresh)
    (rightFixed : repaired.application.candidates.lookup candidate ≠ .fresh)
    (rememberedAction : memory.shadow.actions event = some
      (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (original.application.bindingResult candidate payload)))
    (rememberedValue : memory.shadow.values (.inr event) = some
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (original.application.bindingResult candidate payload)))
    (successful : ∀ value, original.application.bindingResult candidate payload = .success value →
      repaired.application.bindingResult candidate payload = .success value) :
    let app := application setup leaks
    DirectedBindingFrame memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  refine ⟨frame.toFrame.pending_binding_inclusion event payload outputEq codeEq node id candidate
    sender owned found ready timely vacant unused leftFixed rightFixed rememberedAction
    rememberedValue successful, ?_⟩
  have unchanged (execution : (application setup leaks).Execution) :
      (execution.includePending (application setup leaks) id).recall = execution.recall := by
    simp only [ReactiveApplication.Execution.includePending]
    split <;> rfl
  change operationalRecall
      ((original.includePending (application setup leaks) id).recall owner) =
    operationalRecall ((repaired.includePending (application setup leaks) id).recall owner)
  rw [unchanged original, unchanged repaired]
  exact frame.recalled

end DirectedBindingFrame

end Vegas
