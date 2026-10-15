/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingSubmittedRepair

/-! # Exact raw aliases retain delayed original binding records -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- Normalization preserves the original physical packet and candidate effects.
The delayed record therefore survives arbitrary raw evidence aliases while
private response memory keeps the original supplied action. -/
theorem raw_binding_response_records (frame : Frame runtime leaks memory owner original repaired)
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
    (serial : Nat) (opening : Option (Raw L)) (evidence : EvidenceRequest graph)
    (fresh : original.application.current.native.candidates.lookup
      (owner, .prepared serial) = .fresh)
    (ready : original.application.current.native.config.cut.Ready event)
    (bounded : (⟨payload, L.someValue payload⟩ : Raw L) ∈ bounds.values)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ :
      (phaseApplication runtime leaks).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds
        owner (original.recall owner) (original.observe (phaseApplication runtime leaks) owner)) :
    let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
    let canonical : (phaseApplication runtime leaks).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
    let source : (phaseApplication runtime leaks).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩
    let replacementOpening := match opening.bind (fun raw => raw.as? payload) with
      | none => some (⟨payload, L.someValue payload⟩ : Raw L)
      | some _ => opening
    let target : (phaseApplication runtime leaks).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), replacementOpening⟩, .none⟩⟩
    let view := (execution runtime leaks repaired).observe nativeApp owner
    let change := memory.repairResponse runtime (nativeLeaks (graph := graph)) owner view
      (action runtime leaks canonical)
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
  let call : Submission graph := ⟨.commitment event (owner, .prepared serial), opening⟩
  let canonicalMaterial : WitnessedSubmission graph := ⟨call, .none⟩
  let rawMaterial : WitnessedSubmission graph := ⟨call, evidence⟩
  let canonical : app.Action := ⟨some canonicalMaterial⟩
  let source : app.Action := ⟨some rawMaterial⟩
  let replacementOpening := match opening.bind (fun raw => raw.as? payload) with
    | none => some (⟨payload, L.someValue payload⟩ : Raw L)
    | some _ => opening
  let target : app.Action :=
    ⟨some ⟨⟨.commitment event (owner, .prepared serial), replacementOpening⟩, .none⟩⟩
  let view := (execution runtime leaks repaired).observe nativeApp owner
  let change := memory.repairResponse runtime (nativeLeaks (graph := graph)) owner view
    (action runtime leaks canonical)
  let remembered : BindingMemory runtime (nativeLeaks (graph := graph)) :=
    ⟨change.2, memory.responses ++
      [(memory.shadow.inputView runtime (nativeLeaks (graph := graph)) view,
        action runtime leaks source)]⟩
  have rawLeft := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler left
  have rawRight := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler right
  have countLeft := PhaseCount.countRecall_history runtime leaks rawLeft
  have countRight := PhaseCount.countRecall_history runtime leaks rawRight
  have paired := frame.raw_binding_response bounds countLeft countRight stored event payload
    outputEq codeEq node serial opening evidence fresh ready bounded member
  refine ⟨paired.1, paired.2, ?_⟩
  have permitted : PhaseCount.permits (app.outputs (original.recall owner))
      (PhaseCount.localEnvelope runtime leaks owner (original.recall owner)
        (original.observe app owner) rawMaterial) = true := by
    have allowed := member
    rw [PhaseCount.mem_onePacketActions] at allowed
    rcases allowed.2 with impossible | ⟨other, transmitted, allowed⟩
    · cases impossible
    · cases Option.some.inj transmitted
      exact allowed
  have normalized : (PhaseCount.normalization runtime leaks).action owner (original.recall owner)
      (original.observe app owner) source = canonical := by
    have absent := PhaseCount.normalize_binding_evidence_none runtime leaks owner
      (original.recall owner) (original.observe app owner) rawMaterial event
        (owner, .prepared serial) rfl permitted
    have effective : openingEffective owner (original.observe app owner).application.1
        (.commitment event (owner, .prepared serial)) := ⟨rfl, fresh⟩
    have calls : ((PhaseCount.normalization runtime leaks).normalize owner
        (original.observe app owner).application
        (ReactiveApplication.ResponseMenu.knownPackets (original.recall owner)
          (original.observe app owner)) rawMaterial).call = call :=
      Submission.normalizeReactive_effective _ _ _ effective
    exact congrArg (fun material => (⟨some material⟩ : app.Action))
      (congrArg₂ WitnessedSubmission.mk calls absent)
  have canonicalMember := PhaseCount.normalize_mem_onePacketActions runtime leaks bounds owner
    (original.recall owner) (original.observe app owner) source member
  rw [normalized] at canonicalMember
  have effects := (PhaseCount.normalization runtime leaks).effects original owner source countLeft.1
  rw [normalized] at effects
  have canonicalRecords := frame.binding_response_records recorded bounds plan
    inputs horizon scheduler remaining left right stored event payload outputEq codeEq node serial
      opening fresh ready bounded canonicalMember
  apply canonicalRecords.2.2.rebase
  · exact congrArg (List.map PhaseCount.nativeMessage)
      (congrArg MessageNetwork.inputs effects.2.1.symm)
  · intro candidate _fixed
    exact congrArg (fun state : PhaseRuntimeState graph =>
      state.current.native.candidates.lookup candidate) effects.1.symm
  · intro candidate _fixed
    rfl
  · rfl

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
