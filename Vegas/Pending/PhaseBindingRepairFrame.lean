/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseBindingRepairProjection

/-! # Existing native repair frames at both physical checkpoints -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "nativeApp" => runtime.reactiveApplication (nativeLeaks (graph := graph))

/-- Saved semantic data is read with the persistent live catalogue. This is the
catalogue used by physical restoration, rather than an invented earlier preparation. -/
def checkpoint (physical : (phaseApplication runtime leaks).Execution) : (nativeApp).Execution :=
  { execution runtime leaks physical with application :=
    { physical.application.entry.native with
      candidates := physical.application.current.native.candidates } }

/-- The runtime relation retains actual physical transcripts while reusing the
existing native repair frame at both saved and live semantic frontiers. -/
structure Frame (memory : BindingMemory runtime (nativeLeaks (graph := graph)))
    (owner : Player) (original repaired : (phaseApplication runtime leaks).Execution) : Prop where
  live : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) memory owner
    (execution runtime leaks original) (execution runtime leaks repaired)
  saved : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) memory owner
    (checkpoint runtime leaks original) (checkpoint runtime leaks repaired)
  phases : original.application.phases = repaired.application.phases
  generation : original.application.generation = repaired.application.generation
  clearOriginal : original.application.current.excluded = ∅
  clearRepaired : repaired.application.current.excluded = ∅
  archiveOriginal : original.application.retired = []
  archiveRepaired : repaired.application.retired = []
  network : original.network = repaired.network
  service : original.environmentRecall = repaired.environmentRecall
  foreignRecall : ∀ who, who ≠ owner → original.recall who = repaired.recall who

variable {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

theorem frame_atRecall (owner : Player) (physical : (phaseApplication runtime leaks).Execution)
    (clear : physical.application.current.excluded = ∅)
    (archive : physical.application.retired = []) :
    Frame runtime leaks (BindingMemory.atRecall runtime (nativeLeaks (graph := graph))
      ((execution runtime leaks physical).recall owner)) owner physical physical where
  live := BindingMemory.frame_atRecall _ _ owner _
  saved := BindingMemory.frame_atRecall runtime (nativeLeaks (graph := graph)) owner
    (checkpoint runtime leaks physical)
  phases := rfl
  generation := rfl
  clearOriginal := clear
  clearRepaired := clear
  archiveOriginal := archive
  archiveRepaired := archive
  network := rfl
  service := rfl
  foreignRecall := fun _ _ => rfl

namespace Frame

variable {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

theorem receipts (frame : Frame runtime leaks memory owner original repaired) :
    original.receipts = repaired.receipts := frame.live.receipts

theorem publicView (frame : Frame runtime leaks memory owner original repaired) :
    PhaseRuntimeState.publicView (graph := graph) original.application =
      PhaseRuntimeState.publicView (graph := graph) repaired.application := by
  have native : original.application.current.native.publicView =
      repaired.application.current.native.publicView := frame.live.publicView
  simp only [PhaseRuntimeState.publicView, PhaseRuntimeState.attempt,
    frame.clearOriginal, frame.clearRepaired, frame.phases, frame.generation,
    frame.archiveOriginal, frame.archiveRepaired, native]

/-- Count tests see exactly the same physical signed word. This follows from
actual recall correctness and the frame, including retired envelope identities. -/
theorem outputs (frame : Frame runtime leaks memory owner original repaired)
    (left : original.InputRecall (phaseApplication runtime leaks))
    (right : repaired.InputRecall (phaseApplication runtime leaks)) (who : Player) :
    (phaseApplication runtime leaks).outputs (original.recall who) =
      (phaseApplication runtime leaks).outputs (repaired.recall who) := by
  rw [← left who, ← right who, frame.network]

end Frame
end Vegas.EventGraphRuntime.PhaseBindingRepair
