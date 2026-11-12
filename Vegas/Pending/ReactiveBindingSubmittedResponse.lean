module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveBindingSubmittedRecords

@[expose] public section

/-! # Submitted binding provenance through other responses -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  {timeouts : EventTimeouts graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

/-- A foreign response, silence, or an opening preserves the complete submitted
binding records. The second response may prepare additional private material. -/
theorem RecordsSubmittedBindings.respond {memory : BindingMemory timeouts leaks}
    {who : Player} {original repaired : ((reactiveApplication timeouts) leaks).Execution}
    (recorded : memory.RecordsSubmittedBindings timeouts leaks who original repaired)
    (actor : Player) (left right : ((reactiveApplication timeouts) leaks).Action)
    (nonbinding : actor ≠ who ∨ ∀ material, left.transmission = some material →
      ∀ event candidate, material.call.packet ≠ .commitment event candidate) :
    memory.RecordsSubmittedBindings timeouts leaks who
      (original.respond ((reactiveApplication timeouts) leaks) actor left)
      (repaired.respond ((reactiveApplication timeouts) leaks) actor right) := by
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
  have firstStable := (reactive_respond_candidate_fixed timeouts) leaks original actor left
    candidate firstFixed
  have secondStable := (reactive_respond_candidate_fixed timeouts) leaks repaired actor right
    candidate secondFixed
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [State.bindingResult, firstStable] using remembered
  · rwa [firstStable]
  · rwa [secondStable]
  · simpa only [State.bindingResult, secondStable] using succeeds
  · simpa only [State.bindingResult, firstStable, secondStable] using successes

/-- Appending private response recall does not change any submitted binding record. -/
theorem RecordsSubmittedBindings.record {memory : BindingMemory timeouts leaks}
    {who : Player} {original repaired : ((reactiveApplication timeouts) leaks).Execution}
    (recorded : memory.RecordsSubmittedBindings timeouts leaks who original repaired)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (response : ((reactiveApplication timeouts) leaks).Action) :
    (memory.record timeouts leaks view response).RecordsSubmittedBindings timeouts leaks who
      original repaired := recorded

end Vegas.EventGraphRuntime.BindingMemory
