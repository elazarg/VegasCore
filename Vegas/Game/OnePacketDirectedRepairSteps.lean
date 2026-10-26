/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDirectedRepairFrame
import Vegas.Pending.ReactiveBindingSubmissionFrame

/-! # Directed binding repair through actual responses

A directed binding frame augments the existing private-memory repair frame with
the operational recall needed by the native likelihood factorization. Actual
canonical binding responses preserve this relation, including absent or mistyped
private opening material. The repaired response is constructed by the existing
owner-local repair implementation; its correctness is not assumed.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A private binding-repair frame that also preserves the complete operational
part of its owner's actual recall. -/
structure DirectedBindingFrame (memory : BindingMemory runtime leaks) (owner : Player)
    (original repaired : (application setup runtime leaks).Execution) : Prop
    extends BindingMemory.Frame runtime leaks memory owner original repaired where
  /-- Erasing private material from both actual recalls gives the same record. -/
  recalled : operationalRecall (runtime := runtime) (setup := setup) (leaks := leaks)
    (original.recall owner) =
    operationalRecall (runtime := runtime) (repaired.recall owner)

namespace DirectedBindingFrame

variable {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (application setup runtime leaks).Execution}

/-- The repair starts from the actual execution and its actual recall. -/
theorem atRecall (owner : Player) (execution : (application setup runtime leaks).Execution) :
    DirectedBindingFrame (runtime := runtime) (BindingMemory.atRecall runtime leaks
      (execution.recall owner)) owner execution execution :=
  ⟨BindingMemory.frame_atRecall runtime leaks owner execution, rfl⟩

/-- Private unusability is repaired at the actual response, before any receipt
or inclusion. The resulting frame retains the operational recall jointly with
all foreign inputs, scheduler information, and the pending network. -/
theorem binding_submission (frame : DirectedBindingFrame (runtime := runtime) memory owner
  original repaired)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (fresh : original.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (ready : original.application.config.cut.Ready event) :
    let app := application setup runtime leaks
    let view := repaired.observe app owner
    let response : app.Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
    let change := memory.repairResponse runtime leaks owner view response
    let remembered : BindingMemory runtime leaks :=
      ⟨change.2, memory.responses ++ [(memory.shadow.inputView runtime leaks view,
        response)]⟩
    DirectedBindingFrame (runtime := runtime) remembered owner
      (original.respond app owner response) (repaired.respond app owner change.1) := by
  refine ⟨frame.toFrame.binding_submission event payload outputEq codeEq node
    serial opening
    fresh ready, ?_⟩
  have actualFresh := (frame.slots (.prepared serial)).mp fresh
  have ownFresh : (memory.shadow.inputView runtime leaks
      (repaired.observe (application setup runtime leaks) owner)).application.candidates
        (.prepared serial) = .fresh := by
    rw [frame.observed]
    exact fresh
  cases decoded : opening.bind (fun raw => raw.as? payload) with
  | none =>
      rw [memory.repairResponse_unusable runtime leaks owner _ event payload outputEq
        codeEq node serial opening ownFresh actualFresh decoded]
      exact frame.toFrame.operationalRecall_rawBinding
        frame.recalled event opening
        (some ⟨payload, L.someValue payload⟩) serial
  | some value =>
      rw [memory.repairResponse_usable runtime leaks owner _ event payload outputEq
        codeEq node serial opening ownFresh actualFresh value decoded]
      exact frame.toFrame.operationalRecall_rawBinding
        frame.recalled event opening opening serial

/-- An activation samples the same actual pending packets and preserves the
owner's operational recall. -/
theorem activate (frame : DirectedBindingFrame (runtime := runtime) memory owner original repaired)
    (actor : Player) (selected : Finset (MessageId Player)) :
    DirectedBindingFrame (runtime := runtime) memory owner
      (original.sampledActivation (application setup runtime leaks) actor selected)
      (repaired.sampledActivation (application setup runtime leaks) actor selected) :=
  ⟨frame.toFrame.activate actor selected, frame.recalled⟩

/-- Another player's response leaves the repairing owner's recall untouched. -/
theorem foreign_response (frame : DirectedBindingFrame (runtime := runtime) memory owner original
  repaired)
    (actor : Player) (foreign : actor ≠ owner) (response : (application setup runtime
      leaks).Action) :
    DirectedBindingFrame (runtime := runtime) memory owner
      (original.respond (application setup runtime leaks) actor response)
      (repaired.respond (application setup runtime leaks) actor response) := by
  refine ⟨frame.toFrame.foreign_response actor foreign response, ?_⟩
  rw [(application setup runtime leaks).respond_recall_other original actor owner (Ne.symm foreign),
    (application setup runtime leaks).respond_recall_other repaired actor owner (Ne.symm foreign)]
  exact frame.recalled

end DirectedBindingFrame

end Vegas
