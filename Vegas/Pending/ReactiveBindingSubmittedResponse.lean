/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingSubmittedRecords

/-! # Submitted binding provenance through other responses -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

/-- A foreign response, silence, or an opening preserves the complete submitted
binding records. The second response may prepare additional private material. -/
theorem RecordsSubmittedBindings.respond {memory : BindingMemory runtime leaks}
    {who : Player} {original repaired : (runtime.reactiveApplication leaks).Execution}
    (recorded : memory.RecordsSubmittedBindings runtime leaks who original repaired)
    (actor : Player) (left right : (runtime.reactiveApplication leaks).Action)
    (nonbinding : actor ≠ who ∨ ∀ material, left.transmission = some material →
      ∀ event candidate, material.call.packet ≠ .commitment event candidate) :
    memory.RecordsSubmittedBindings runtime leaks who
      (original.respond (runtime.reactiveApplication leaks) actor left)
      (repaired.respond (runtime.reactiveApplication leaks) actor right) := by
  intro message member sender event candidate call payload outputEq codeEq node
  have old : message ∈ original.network.inputs := by
    rcases left with ⟨transmission⟩
    cases transmission with
    | none => exact member
    | some material =>
        simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
          List.mem_append, List.mem_singleton] at member
        rcases member with retained | rfl
        · exact retained
        · rcases nonbinding with foreign | harmless
          · exact (foreign sender).elim
          · exact (harmless material rfl event candidate call).elim
  obtain ⟨remembered, firstFixed, secondFixed, succeeds, successes⟩ :=
    recorded message old sender event candidate call payload outputEq codeEq node
  have firstStable := runtime.reactive_respond_candidate_fixed leaks original actor left
    candidate firstFixed
  have secondStable := runtime.reactive_respond_candidate_fixed leaks repaired actor right
    candidate secondFixed
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [State.bindingResult, firstStable] using remembered
  · rwa [firstStable]
  · rwa [secondStable]
  · simpa only [State.bindingResult, secondStable] using succeeds
  · simpa only [State.bindingResult, firstStable, secondStable] using successes

/-- Appending private response recall does not change any submitted binding record. -/
theorem RecordsSubmittedBindings.record {memory : BindingMemory runtime leaks}
    {who : Player} {original repaired : (runtime.reactiveApplication leaks).Execution}
    (recorded : memory.RecordsSubmittedBindings runtime leaks who original repaired)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action) :
    (memory.record runtime leaks view response).RecordsSubmittedBindings runtime leaks who
      original repaired := recorded

end Vegas.EventGraphRuntime.BindingMemory
