/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingRepairFrame

/-! # Clear phase installation transports both existing native repair frames -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- Clean phase installation saves the paired live semantic state. Earlier
unrevealed repaired bindings remain paired when their phase becomes the checkpoint. -/
theorem normalize (frame : Frame runtime leaks memory owner original repaired) :
    Frame runtime leaks memory owner
      (PhaseRuntimeState.normalizeExecution runtime leaks original)
      (PhaseRuntimeState.normalizeExecution runtime leaks repaired) := by
  rcases original with ⟨leftState, leftNetwork, leftReceipts, leftRecall, leftService⟩
  rcases repaired with ⟨rightState, rightNetwork, rightReceipts, rightRecall, rightService⟩
  change PhaseRuntimeState graph at leftState rightState
  rcases leftState with ⟨phases, generation, leftEntry, leftCurrent, leftArchive⟩
  rcases rightState with ⟨rightPhases, rightGeneration, rightEntry, rightCurrent, rightArchive⟩
  have phaseEq : phases = rightPhases := frame.phases
  subst rightPhases
  have generationEq : generation = rightGeneration := frame.generation
  subst rightGeneration
  have leftRetired : leftArchive = [] := frame.archiveOriginal
  have rightRetired : rightArchive = [] := frame.archiveRepaired
  subst leftArchive
  subst rightArchive
  change Frame runtime leaks memory owner
    ⟨PhaseRuntimeState.settle phases generation leftEntry leftCurrent [], leftNetwork,
      leftReceipts, leftRecall, leftService⟩
    ⟨PhaseRuntimeState.settle phases generation rightEntry rightCurrent [], rightNetwork,
      rightReceipts, rightRecall, rightService⟩
  induction phases generalizing leftEntry rightEntry with
  | nil => exact frame
  | cons phase remaining ih =>
      have leftClear : leftCurrent.excluded = ∅ := frame.clearOriginal
      have rightClear : rightCurrent.excluded = ∅ := frame.clearRepaired
      have leftDrain := phase.drain_eq_of_clear leftCurrent (by
        rintro event ⟨_, eligible⟩
        obtain ⟨who, _, excluded⟩ := eligible.owned
        simp only [leftClear, Finset.notMem_empty] at excluded)
      have rightDrain := phase.drain_eq_of_clear rightCurrent (by
        rintro event ⟨_, eligible⟩
        obtain ⟨who, _, excluded⟩ := eligible.owned
        simp only [rightClear, Finset.notMem_empty] at excluded)
      have publics : leftCurrent.native.publicView = rightCurrent.native.publicView :=
        frame.live.publicView
      have cuts := EventGraph.cut_eq_of_completionOrder_eq leftCurrent.native.config
        rightCurrent.native.config (congrArg PublicObservation.completionOrder
          (congrArg PublicView.observation publics))
      have finishedEq : phase.Finished leftCurrent ↔ phase.Finished rightCurrent := by
        unfold RuntimePhase.Finished
        rw [cuts]
      by_cases finished : phase.Finished leftCurrent
      · have rightFinished := finishedEq.mp finished
        simp only [PhaseRuntimeState.settle, leftDrain, rightDrain, finished, rightFinished,
          leftClear, rightClear, Finset.empty_sdiff, Finset.empty_inter,
          Finset.not_nonempty_empty, and_false, ite_false, ite_true]
        apply ih leftCurrent rightCurrent
        exact ⟨frame.live, frame.live, rfl, rfl, leftClear, rightClear, rfl, rfl,
          frame.network, frame.service, frame.foreignRecall⟩
      · have rightUnfinished : ¬ phase.Finished rightCurrent :=
          fun yes => finished (finishedEq.mpr yes)
        simpa only [PhaseRuntimeState.settle, leftDrain, rightDrain, finished, rightUnfinished,
          ite_false] using frame

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
