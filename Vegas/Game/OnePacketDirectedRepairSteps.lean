module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketDirectedRepairFrame
public import Vegas.Pending.ReactiveBindingSubmissionFrame
public import Interaction.ReactiveMessageReadout

@[expose] public section

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
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A private binding-repair frame that also preserves the complete operational
part of its owner's actual recall. -/
structure DirectedBindingFrame (memory : BindingMemory timeouts leaks) (owner : Player)
    (original repaired : (application setup timeouts leaks).Execution) : Prop
    extends BindingMemory.Frame timeouts leaks memory owner original repaired where
  /-- Erasing private material from both actual recalls gives the same record. -/
  recalled : operationalRecall (timeouts := timeouts) (setup := setup) (leaks := leaks)
    (original.logs owner) =
    operationalRecall (timeouts := timeouts) (repaired.logs owner)

namespace DirectedBindingFrame

variable {memory : BindingMemory timeouts leaks} {owner : Player}
  {original repaired : (application setup timeouts leaks).Execution}

/-- The repair starts from the actual execution and its actual recall. -/
theorem atRecall (owner : Player) (execution : (application setup timeouts leaks).Execution) :
    DirectedBindingFrame (timeouts := timeouts) (BindingMemory.atRecall timeouts leaks
      (execution.logs owner)) owner execution execution :=
  ⟨BindingMemory.frame_atRecall timeouts leaks owner execution, rfl⟩

/-- Private unusability is repaired at the actual response, before any receipt
or inclusion. The resulting frame retains the operational recall jointly with
all foreign inputs, scheduler information, and the pending network. -/
theorem binding_submission (frame : DirectedBindingFrame (timeouts := timeouts) memory owner
  original repaired)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (fresh : original.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (ready : original.application.config.cut.Ready event) :
    let app := application setup timeouts leaks
    let view := repaired.observe app owner
    let response : app.Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
    let change := memory.repairResponse timeouts leaks owner view response
    let remembered : BindingMemory timeouts leaks :=
      ⟨change.2, memory.responses ++ [(memory.shadow.inputView timeouts leaks view,
        response)]⟩
    DirectedBindingFrame (timeouts := timeouts) remembered owner
      (original.respond app owner response) (repaired.respond app owner change.1) := by
  refine ⟨frame.toFrame.binding_submission event payload outputEq codeEq node
    serial opening
    fresh ready, ?_⟩
  have actualFresh := (frame.slots (.prepared serial)).mp fresh
  have ownFresh : (memory.shadow.inputView timeouts leaks
      (repaired.observe (application setup timeouts leaks) owner)).application.candidates
        (.prepared serial) = .fresh := by
    rw [frame.observed]
    exact fresh
  cases decoded : opening.bind (fun raw => raw.as? payload) with
  | none =>
      rw [memory.repairResponse_unusable timeouts leaks owner _ event payload outputEq
        codeEq node serial opening ownFresh actualFresh decoded]
      exact frame.toFrame.operationalRecall_rawBinding
        frame.recalled event opening
        (some ⟨payload, L.someValue payload⟩) serial
  | some value =>
      rw [memory.repairResponse_usable timeouts leaks owner _ event payload outputEq
        codeEq node serial opening ownFresh actualFresh value decoded]
      exact frame.toFrame.operationalRecall_rawBinding
        frame.recalled event opening opening serial

/-- An activation samples the same actual pending packets and preserves the
owner's operational recall. -/
theorem activate (frame : DirectedBindingFrame (timeouts := timeouts) memory owner original
  repaired)
    (actor : Player) (selected : Finset (MessageId Player)) :
    DirectedBindingFrame (timeouts := timeouts) memory owner
      (original.sampledActivation (application setup timeouts leaks) actor selected)
      (repaired.sampledActivation (application setup timeouts leaks) actor selected) :=
  ⟨frame.toFrame.activate actor selected, frame.recalled⟩

/-- Another player's response leaves the repairing owner's recall untouched. -/
theorem foreign_response (frame : DirectedBindingFrame (timeouts := timeouts) memory owner original
  repaired)
    (actor : Player) (foreign : actor ≠ owner) (response : (application setup timeouts
      leaks).Action) :
    DirectedBindingFrame (timeouts := timeouts) memory owner
      (original.respond (application setup timeouts leaks) actor response)
      (repaired.respond (application setup timeouts leaks) actor response) := by
  refine ⟨frame.toFrame.foreign_response actor foreign response, ?_⟩
  rw [(application setup timeouts leaks).respond_recall_other original actor owner (Ne.symm
    foreign),
    (application setup timeouts leaks).respond_recall_other repaired actor owner (Ne.symm foreign)]
  exact frame.recalled

end DirectedBindingFrame

end Vegas
