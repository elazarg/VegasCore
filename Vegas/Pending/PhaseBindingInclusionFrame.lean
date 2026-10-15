/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingAdmittedInclude

/-! # Actual admitted inclusion frames through phase installation -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- The existing native accepted-inclusion kernel lifts to BOTH physical
frontiers. Actual source clear survival and public result agreement determine
the image's exclusion update; neither a target clear state nor trace is assumed. -/
theorem admitted_inclusion (frame : Frame runtime leaks memory owner original repaired)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : original.network.lookup id = some message)
    (admitted : (message.payload.tokenValid original.application.attempt &&
      original.application.allows message.payload.packet.call &&
      !original.application.current.excludedCall message.payload.packet.call) = true)
    (leftNative rightNative : State graph)
    (leftHandled : handle runtime original.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some leftNative)
    (rightHandled : handle runtime repaired.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some rightNative)
    (leftCandidates : leftNative.candidates = original.application.current.native.candidates)
    (rightCandidates : rightNative.candidates = repaired.application.current.native.candidates)
    (native : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) memory owner
      { (execution runtime leaks original).includePending
          (runtime.reactiveApplication (nativeLeaks (graph := graph))) id with
        environmentRecall := (execution runtime leaks original).environmentRecall ++
          [⟨(execution runtime leaks original).observeEnvironment
            (runtime.reactiveApplication (nativeLeaks (graph := graph))), .include id⟩] }
      { (execution runtime leaks repaired).includePending
          (runtime.reactiveApplication (nativeLeaks (graph := graph))) id with
        environmentRecall := (execution runtime leaks repaired).environmentRecall ++
          [⟨(execution runtime leaks repaired).observeEnvironment
            (runtime.reactiveApplication (nativeLeaks (graph := graph))), .include id⟩] })
    (clear : (original.includePending (phaseApplication runtime leaks)
      id).application.current.excluded = ∅) :
    Frame runtime leaks memory owner
      { original.includePending (phaseApplication runtime leaks) id with
        environmentRecall := original.environmentRecall ++
          [⟨original.observeEnvironment (phaseApplication runtime leaks), .include id⟩] }
      { repaired.includePending (phaseApplication runtime leaks) id with
        environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment (phaseApplication runtime leaks), .include id⟩] } := by
  let app := phaseApplication runtime leaks
  let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
  have nativeToken : message.payload.packet.tokenValid = true :=
    (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp admitted).1).1).2
  have rightFound : repaired.network.lookup id = some message := frame.network ▸ found
  have effect (physical : app.Execution) (found : physical.network.lookup id = some message)
      (result : State graph)
      (handled : handle runtime physical.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some result) :
      ((execution runtime leaks physical).includePending nativeApp id).application = result := by
    have projected : (PhaseBindingRepair.network physical.network).lookup id =
        some (PhaseCount.nativeMessage message) := by rw [network_lookup, found]; rfl
    unfold ReactiveApplication.Execution.includePending
    dsimp only [execution, nativeApp]
    simp only [MessageNetwork.includePending, projected, reactiveApplication_handle,
      PhaseCount.nativeMessage, nativeToken, ↓reduceIte, handled, Option.getD_some]
  have leftApplication := effect original found leftNative leftHandled
  have rightApplication := effect repaired rightFound rightNative rightHandled
  have publics : leftNative.publicView = rightNative.publicView := by
    have result := native.publicView
    change ((execution runtime leaks original).includePending nativeApp id).application.publicView =
      ((execution runtime leaks repaired).includePending nativeApp id).application.publicView
        at result
    rwa [leftApplication, rightApplication] at result
  have leftClear := inclusion_clear_of_actual runtime leaks original id message found admitted
    leftNative leftHandled clear
  have rightClear : (repaired.application.current.inclusionResult message.payload.packet.call
      rightNative).excluded = ∅ := by
    have same := inclusion_exclusion_congr original.application.current repaired.application.current
      (frame.clearOriginal.trans frame.clearRepaired.symm) leftNative rightNative publics
        message.payload.packet.call
    exact same.symm.trans leftClear
  let left := rawBindingInclude runtime leaks original id
  let right := rawBindingInclude runtime leaks repaired id
  let leftRecorded : app.Execution := { left with environmentRecall :=
    original.environmentRecall ++ [⟨original.observeEnvironment app, .include id⟩] }
  let rightRecorded : app.Execution := { right with environmentRecall :=
    repaired.environmentRecall ++ [⟨repaired.observeEnvironment app, .include id⟩] }
  have live : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) memory owner
      (execution runtime leaks leftRecorded) (execution runtime leaks rightRecorded) := by
    change BindingMemory.Frame runtime (nativeLeaks (graph := graph)) memory owner
      { execution runtime leaks left with environmentRecall := _ }
      { execution runtime leaks right with environmentRecall := _ }
    rw [show execution runtime leaks left = _ from execution_rawBindingInclude runtime leaks
      original id, show execution runtime leaks right = _ from
        execution_rawBindingInclude runtime leaks repaired id]
    rw [PhaseBindingRepair.observeEnvironment runtime leaks original,
      PhaseBindingRepair.observeEnvironment runtime leaks repaired] at native
    simpa only [leftRecorded, rightRecorded, List.map_append, List.map_cons, List.map_nil,
      environmentEntry, command, execution, app] using native
  have savedLeft : (checkpoint runtime leaks leftRecorded).application =
      (checkpoint runtime leaks original).application := by
    change ({ original.application.entry.native with candidates :=
      ((execution runtime leaks original).includePending nativeApp id).application.candidates } :
        State graph) = _
    rw [leftApplication, leftCandidates]
    rfl
  have savedRight : (checkpoint runtime leaks rightRecorded).application =
      (checkpoint runtime leaks repaired).application := by
    change ({ repaired.application.entry.native with candidates :=
      ((execution runtime leaks repaired).includePending nativeApp id).application.candidates } :
        State graph) = _
    rw [rightApplication, rightCandidates]
    rfl
  have saved : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) memory owner
      (checkpoint runtime leaks leftRecorded) (checkpoint runtime leaks rightRecorded) := by
    apply checkpointFrame live (checkpoint runtime leaks leftRecorded).application
      (checkpoint runtime leaks rightRecorded).application
    · rw [savedRight, savedLeft]
      exact congrArg ReactiveApplication.PlayerView.application frame.saved.observed
    · rw [savedLeft, savedRight]
      exact frame.saved.views
    · rw [savedLeft, savedRight]
      exact frame.saved.slots
    · rw [savedLeft, savedRight]
      exact frame.saved.successful
  have raw : Frame runtime leaks memory owner leftRecorded rightRecorded := by
    refine ⟨live, saved, frame.phases, frame.generation, frame.clearOriginal,
      frame.clearRepaired, frame.archiveOriginal, frame.archiveRepaired, ?_, ?_,
      frame.foreignRecall⟩
    · exact congrArg (fun pool => (pool.includePending id).2) frame.network
    · change original.environmentRecall ++ [_] = repaired.environmentRecall ++ [_]
      rw [frame.service, frame.environment_input]
  have leftActual := include_native_eq_normalize runtime leaks original id message found admitted
    leftNative leftHandled (leftClear.trans frame.clearOriginal.symm)
  have rightActual := include_native_eq_normalize runtime leaks repaired id message rightFound
    ((frame.admission message).symm.trans admitted) rightNative rightHandled
      (rightClear.trans frame.clearRepaired.symm)
  rw [leftActual, rightActual]
  exact raw.normalize

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
