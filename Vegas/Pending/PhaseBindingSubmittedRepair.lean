/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingSubmittedPreservation
import Vegas.Pending.ReactiveBindingSubmittedRepair

/-! # Actual phase binding responses establish delayed inclusion records -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- A real count-admitted binding response extends the delayed packet record.
Static firstness is derived from actual clear physical namespace history; the
existing native repair implementation then supplies the original private value. -/
theorem binding_response_records (frame : Frame runtime leaks memory owner original repaired)
    (recorded : memory.RecordsSubmittedBindings runtime (nativeLeaks (graph := graph)) owner
      (execution runtime leaks original) (execution runtime leaks repaired))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat)
    (left : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, original⟩))
    (right : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, repaired⟩))
    (stored : repaired.application.StoredCheckpoint)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (fresh : original.application.current.native.candidates.lookup
      (owner, .prepared serial) = .fresh)
    (ready : original.application.current.native.config.cut.Ready event)
    (bounded : (⟨payload, L.someValue payload⟩ : Raw L) ∈ bounds.values)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩ :
      (phaseApplication runtime leaks).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds
        owner (original.recall owner) (original.observe (phaseApplication runtime leaks) owner)) :
    let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
    let source : (phaseApplication runtime leaks).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
    let replacementOpening := match opening.bind (fun raw => raw.as? payload) with
      | none => some (⟨payload, L.someValue payload⟩ : Raw L)
      | some _ => opening
    let target : (phaseApplication runtime leaks).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), replacementOpening⟩, .none⟩⟩
    let view := (execution runtime leaks repaired).observe nativeApp owner
    let change := memory.repairResponse runtime (nativeLeaks (graph := graph)) owner view
      (action runtime leaks source)
    let remembered : BindingMemory runtime (nativeLeaks (graph := graph)) :=
      ⟨change.2, memory.responses ++
        [(memory.shadow.inputView runtime (nativeLeaks (graph := graph)) view,
          action runtime leaks source)]⟩
    target ∈ PhaseCount.onePacketActions runtime leaks bounds owner (repaired.recall owner)
        (repaired.observe (phaseApplication runtime leaks) owner) ∧
      Frame runtime leaks remembered owner
        (original.respond (phaseApplication runtime leaks) owner source)
        (repaired.respond (phaseApplication runtime leaks) owner target) ∧
      remembered.RecordsSubmittedBindings runtime (nativeLeaks (graph := graph)) owner
        (execution runtime leaks (original.respond (phaseApplication runtime leaks) owner source))
        (execution runtime leaks
          (repaired.respond (phaseApplication runtime leaks) owner target)) := by
  let app := phaseApplication runtime leaks
  let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let material : WitnessedSubmission graph :=
    ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩
  let source : app.Action := ⟨some material⟩
  let replacementOpening := match opening.bind (fun raw => raw.as? payload) with
    | none => some (⟨payload, L.someValue payload⟩ : Raw L)
    | some _ => opening
  let target : app.Action :=
    ⟨some ⟨⟨.commitment event (owner, .prepared serial), replacementOpening⟩, .none⟩⟩
  let view := (execution runtime leaks repaired).observe nativeApp owner
  let change := memory.repairResponse runtime (nativeLeaks (graph := graph)) owner view
    (action runtime leaks source)
  let remembered : BindingMemory runtime (nativeLeaks (graph := graph)) :=
    ⟨change.2, memory.responses ++
      [(memory.shadow.inputView runtime (nativeLeaks (graph := graph)) view,
        action runtime leaks source)]⟩
  have rawLeft := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler left
  have rawRight := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler right
  have paired := frame.binding_response bounds
    (PhaseCount.countRecall_history runtime leaks rawLeft)
    (PhaseCount.countRecall_history runtime leaks rawRight) stored event payload outputEq codeEq
      node
      serial opening fresh ready bounded member
  refine ⟨paired.1, paired.2, ?_⟩
  have count := native_countRecall runtime leaks original
    (PhaseCount.countRecall_history runtime leaks rawLeft)
  obtain ⟨postTrace⟩ := (PhaseCount.onePacketMenu runtime leaks bounds).trace_respond initial
    horizon scheduler remaining original owner source left member
  have clear : (original.respond app owner source).application.current.excluded = ∅ :=
    frame.clearOriginal
  have clean := native_countClean_of_clear runtime leaks bounds plan inputs horizon
    scheduler postTrace clear
  rw [execution_respond_of_onePacket runtime leaks bounds original owner source member] at clean
  have locality := runtime.countPermits_respond (nativeLeaks (graph := graph))
    (execution runtime leaks original) count owner material
  have present : runtime.localEnvelope (nativeLeaks (graph := graph)) owner
      ((execution runtime leaks original).recall owner)
      ((execution runtime leaks original).observe nativeApp owner) material ∈
        ((execution runtime leaks original).respond nativeApp owner
          (action runtime leaks source)).network.inputs := by
    change runtime.localEnvelope (nativeLeaks (graph := graph)) owner
      ((execution runtime leaks original).recall owner)
      ((execution runtime leaks original).observe
        (runtime.reactiveApplication (nativeLeaks (graph := graph))) owner) material ∈
      ((execution runtime leaks original).respond
        (runtime.reactiveApplication (nativeLeaks (graph := graph))) owner
          ⟨some material⟩).network.inputs
    rw [locality.1]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have permitted := locality.2.1.symm.trans (clean.2 _ present)
  have native := recorded.binding_submission frame.live count event payload outputEq codeEq node
    serial opening fresh permitted
  have ownFresh : (memory.shadow.inputView runtime (nativeLeaks (graph := graph))
      view).application.candidates (.prepared serial) = .fresh := by
    rw [frame.live.observed]
    exact fresh
  have actualFresh : repaired.application.current.native.candidates.lookup
      (owner, .prepared serial) = .fresh := (frame.live.slots (.prepared serial)).mp fresh
  have changed : change.1 = action runtime leaks target := by
    dsimp only [change, source, material, action]
    cases decoded : opening.bind (fun raw => raw.as? payload) with
    | none =>
        rw [memory.repairResponse_unusable runtime (nativeLeaks (graph := graph)) owner view event
          payload outputEq codeEq node serial opening ownFresh actualFresh decoded]
        simp only [target, replacementOpening, decoded]
        rfl
    | some value =>
        rw [memory.repairResponse_usable runtime (nativeLeaks (graph := graph)) owner view event
          payload outputEq codeEq node serial opening ownFresh actualFresh value decoded]
        simp only [target, replacementOpening, decoded]
  change remembered.RecordsSubmittedBindings runtime (nativeLeaks (graph := graph)) owner
    ((execution runtime leaks original).respond nativeApp owner (action runtime leaks source))
    ((execution runtime leaks repaired).respond nativeApp owner change.1) at native
  rw [changed] at native
  rw [execution_respond_of_onePacket runtime leaks bounds original owner source member,
    execution_respond_of_onePacket runtime leaks bounds repaired owner target paired.1]
  exact native

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
