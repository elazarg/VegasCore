/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDirectedRepairSteps

/-! # Operational recall through repaired owner responses

Equality of the actual networks before and after two owner responses forces the
responses to emit the same envelope, even if their private material differs.
This lifts the existing concrete binding-frame response constructors to directed
frames without a separate operational-recall proof for each response form.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

namespace DirectedBindingFrame

variable {memory nextMemory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (application setup runtime leaks).Execution}

/-- Every owner-response constructor preserving the actual binding frame also
preserves operational recall. The equality of emitted envelopes follows from
actual network inputs, rather than a separate assumed packet identity. -/
theorem respond (frame : DirectedBindingFrame (runtime := runtime) memory owner original repaired)
    (left right : (application setup runtime leaks).Action)
    (after : BindingMemory.Frame runtime leaks nextMemory owner
      (original.respond (application setup runtime leaks) owner left)
      (repaired.respond (application setup runtime leaks) owner right)) :
    DirectedBindingFrame (runtime := runtime) nextMemory owner
      (original.respond (application setup runtime leaks) owner left)
      (repaired.respond (application setup runtime leaks) owner right) := by
  refine ⟨after, ?_⟩
  have inputs := congrArg (fun net => net.inputs) after.network
  rcases left with ⟨left⟩
  rcases right with ⟨right⟩
  cases left with
  | none =>
      cases right with
      | none =>
          simp only [ReactiveApplication.Execution.respond, operationalRecall,
            List.map_append, List.map_cons, List.map_nil, ite_true]
          change operationalRecall (runtime := runtime) (original.recall owner) ++ [_] =
            operationalRecall (runtime := runtime) (repaired.recall owner) ++ [_]
          rw [frame.recalled, frame.toFrame.operationalView]
      | some material =>
          change original.network.inputs = repaired.network.inputs ++ [_] at inputs
          rw [frame.network] at inputs
          have length := congrArg List.length inputs
          simp only [List.length_append, List.length_singleton] at length
          omega
  | some leftMaterial =>
      cases right with
      | none =>
          change original.network.inputs ++ [_] = repaired.network.inputs at inputs
          rw [frame.network] at inputs
          have length := congrArg List.length inputs
          simp only [List.length_append, List.length_singleton] at length
          omega
      | some rightMaterial =>
          change original.network.inputs ++ [_] = repaired.network.inputs ++ [_] at inputs
          rw [frame.network] at inputs
          have emitted := List.singleton_inj.mp (List.append_cancel_left inputs)
          simp only [ReactiveApplication.Execution.respond, operationalRecall,
            List.map_append, List.map_cons, List.map_nil, ite_true]
          change operationalRecall (runtime := runtime) (original.recall owner) ++ [_] =
            operationalRecall (runtime := runtime) (repaired.recall owner) ++ [_]
          rw [frame.recalled]
          congr 1
          apply congrArg List.singleton
          apply Prod.ext frame.toFrame.operationalView
          simpa only [frame.network, MessageNetwork.submit] using congrArg some emitted

/-- Actual environment steps preserve every player's own recall. Thus each
existing concrete environment-frame constructor lifts to the operational frame. -/
theorem environmentStep (frame : DirectedBindingFrame (runtime := runtime) memory owner original
  repaired)
    (command : (application setup runtime leaks).Command)
    (nextOriginal nextRepaired : (application setup runtime leaks).Execution)
    (left : nextOriginal ∈ (original.environmentStep (application setup runtime leaks)
      command).support)
    (right : nextRepaired ∈ (repaired.environmentStep (application setup runtime leaks)
      command).support)
    (after : BindingMemory.Frame runtime leaks memory owner nextOriginal nextRepaired) :
    DirectedBindingFrame (runtime := runtime) memory owner nextOriginal nextRepaired := by
  refine ⟨after, ?_⟩
  rw [(application setup runtime leaks).environmentStep_recall original nextOriginal command left,
    (application setup runtime leaks).environmentStep_recall repaired nextRepaired command right]
  exact frame.recalled

/-- A genuine unchanged opening records its actual original input and preserves
the operational frame. Candidate provenance and certificate equality are the
existing native opening facts. -/
theorem opening_submission (frame : DirectedBindingFrame (runtime := runtime) memory owner
  original repaired)
    (event : (graph setup).EventId) (candidate : Handle (graph setup)) (raw : Raw L)
    (evidence : EvidenceRequest (graph setup))
    (rightFixed : repaired.application.candidates.lookup candidate = .openable raw)
    (certified : (WitnessedSubmission.mk ⟨.opening event candidate raw, none⟩ evidence |>.emit
      original.application owner (original.network.known owner)).evidence =
        some ⟨candidate, raw⟩) :
    let app := application setup runtime leaks
    let response : app.Action :=
      ⟨some ⟨⟨.opening event candidate raw, none⟩, evidence⟩⟩
    DirectedBindingFrame (runtime := runtime)
      (memory.record runtime leaks
        (memory.shadow.inputView runtime leaks (repaired.observe app owner)) response)
      owner (original.respond app owner response) (repaired.respond app owner response) := by
  exact frame.respond _ _
    (frame.toFrame.opening_submission event candidate raw evidence rightFixed
      certified)

end DirectedBindingFrame

end Vegas
