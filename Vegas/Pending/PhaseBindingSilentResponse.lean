/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingResponseAliases

/-! # Silent owner callbacks retain exact private reconstruction -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- A silent callback is recorded as silence and changes neither semantic
frontier. It is not identified with source omission or eventual failure. -/
theorem silence (frame : Frame runtime leaks memory owner original repaired) :
    let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
    let remembered := memory.record runtime (nativeLeaks (graph := graph))
      (memory.shadow.inputView runtime (nativeLeaks (graph := graph))
        ((execution runtime leaks repaired).observe nativeApp owner)) ⟨none⟩
    Frame runtime leaks remembered owner
      (original.respond (phaseApplication runtime leaks) owner ⟨none⟩)
      (repaired.respond (phaseApplication runtime leaks) owner ⟨none⟩) := by
  let app := phaseApplication runtime leaks
  let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
  let remembered := memory.record runtime (nativeLeaks (graph := graph))
    (memory.shadow.inputView runtime (nativeLeaks (graph := graph))
      ((execution runtime leaks repaired).observe nativeApp owner)) ⟨none⟩
  have live : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) remembered owner
      (execution runtime leaks (original.respond app owner ⟨none⟩))
      (execution runtime leaks (repaired.respond app owner ⟨none⟩)) := by
    rw [execution_respond runtime leaks original owner ⟨none⟩ (by
      intro material impossible; cases impossible),
      execution_respond runtime leaks repaired owner ⟨none⟩ (by
        intro material impossible; cases impossible)]
    exact frame.live.transport_response ⟨none⟩ (by intro material impossible; cases impossible)
  have saved : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) remembered owner
      (checkpoint runtime leaks (original.respond app owner ⟨none⟩))
      (checkpoint runtime leaks (repaired.respond app owner ⟨none⟩)) := by
    apply checkpointFrame live (checkpoint runtime leaks original).application
      (checkpoint runtime leaks repaired).application
    · exact congrArg ReactiveApplication.PlayerView.application frame.saved.observed
    · exact frame.saved.views
    · exact frame.saved.slots
    · exact frame.saved.successful
  refine ⟨live, saved, frame.phases, frame.generation, frame.clearOriginal, frame.clearRepaired,
    frame.archiveOriginal, frame.archiveRepaired, frame.network, frame.service, ?_⟩
  intro who different
  rw [app.respond_recall_other original owner who different,
    app.respond_recall_other repaired owner who different]
  exact frame.foreignRecall who different

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
