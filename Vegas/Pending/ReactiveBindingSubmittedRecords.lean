module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveBindingPreparationRecord
public import Vegas.Pending.ReactiveOnePacketMenu
public import Vegas.Pending.ReactiveBinding

@[expose] public section

/-! # Original records of submitted owned bindings -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

private theorem earlierInput_of_countRecall
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (count : (CountRecall timeouts) leaks execution) (who : Player)
    (material : WitnessedSubmission graph)
    (message : Message Player (WitnessedPacket graph))
    (member : message ∈ execution.network.inputs) (sender : message.sender = who) :
    EarlierOwnPacket (((reactiveApplication timeouts) leaks).outputs (execution.logs who))
      ((localEnvelope timeouts) leaks who (execution.logs who)
        (execution.observe ((reactiveApplication timeouts) leaks) who) material) message := by
  refine ⟨?_, sender, ?_⟩
  · rw [← count.1 who]
    exact List.mem_filter.mpr ⟨member, by simpa using sender⟩
  · change message.id.2 < ((reactiveApplication timeouts) leaks).submissionCount
      (execution.logs who)
    rw [← count.2.1 who, ← sender]
    exact count.2.2.serial_lt member

/-- The count verdict prevents an admitted binding from overwriting any
previous own binding event's private record. -/
theorem priorBinding_ne_of_permitted
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (count : (CountRecall timeouts) leaks execution) (who : Player)
    (event : graph.EventId) (serial : Nat) (opening : Option (Raw L))
    (permitted : countPermits
      (((reactiveApplication timeouts) leaks).outputs (execution.logs who))
      ((localEnvelope timeouts) leaks who (execution.logs who)
        (execution.observe ((reactiveApplication timeouts) leaks) who)
        ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩) = true)
    (message : Message Player (WitnessedPacket graph))
    (member : message ∈ execution.network.inputs) (sender : message.sender = who)
    (other : graph.EventId) (candidate : Handle graph)
    (call : message.payload.call = .commitment other candidate) : other ≠ event := by
  have first := ((countPermits_eq_true_iff _ _).mp permitted).2.2
  have different := first message (earlierInput_of_countRecall timeouts leaks execution count
    who _ message member sender)
  change message.payload.call.event? graph ≠ some event at different
  intro same
  apply different
  rw [call, same]
  rfl

/-- Every submitted own binding has its original typed result in memory, with
fixed candidates on both sides and preservation of all original successes.
Completed packets remain covered, so actual inclusion needs no memory deletion. -/
def RecordsSubmittedBindings (memory : BindingMemory timeouts leaks) (who : Player)
    (original repaired : ((reactiveApplication timeouts) leaks).Execution) : Prop :=
  ∀ message ∈ original.network.inputs, message.sender = who →
    ∀ event candidate, message.payload.call = .commitment event candidate →
      ∀ payload (outputEq : graph.outputLayout event = .binding who payload)
        (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
          (graph.nodes event) = .bind who payload),
        nodeView graph event = .bind who payload outputEq codeEq →
        memory.shadow.RecordsBinding event outputEq
            (original.application.bindingResult candidate payload) ∧
          original.application.candidates.lookup candidate ≠ .fresh ∧
          repaired.application.candidates.lookup candidate ≠ .fresh ∧
          (∃ value, repaired.application.bindingResult candidate payload = .success value) ∧
          ∀ value, original.application.bindingResult candidate payload = .success value →
            repaired.application.bindingResult candidate payload = .success value

/-- The concrete initializer has no signed submissions, so preparation
provenance holds for any initial application state and any private memory. -/
theorem recordsSubmittedBindings_initial (memory : BindingMemory timeouts leaks) (who : Player)
    (first second : ((reactiveApplication timeouts) leaks).State) :
    memory.RecordsSubmittedBindings timeouts leaks who
      (ReactiveApplication.Execution.initial ((reactiveApplication timeouts) leaks) first)
      (ReactiveApplication.Execution.initial ((reactiveApplication timeouts) leaks) second) := by
  intro message member
  cases member

/-- Actual environment operations preserve all recorded submitted bindings.
This covers arbitrary sampling, inclusion, expiry, and clock commands jointly;
fixed candidates are immutable even when other handles are accepted. -/
theorem RecordsSubmittedBindings.environmentStep {memory : BindingMemory timeouts leaks}
    {who : Player} {original repaired : ((reactiveApplication timeouts) leaks).Execution}
    (recorded : memory.RecordsSubmittedBindings timeouts leaks who original repaired)
    (command : ((reactiveApplication timeouts) leaks).Command)
    (nextOriginal nextRepaired : ((reactiveApplication timeouts) leaks).Execution)
    (left : nextOriginal ∈ (original.environmentStep ((reactiveApplication timeouts) leaks)
      command).support)
    (right : nextRepaired ∈ (repaired.environmentStep ((reactiveApplication timeouts) leaks)
      command).support) :
    memory.RecordsSubmittedBindings timeouts leaks who nextOriginal nextRepaired := by
  intro message member sender event candidate call payload outputEq codeEq node
  rw [((reactiveApplication timeouts) leaks).environmentStep_inputs original nextOriginal
    command left] at member
  obtain ⟨remembered, firstFixed, secondFixed, succeeds, successes⟩ :=
    recorded message member sender event candidate call payload outputEq codeEq node
  have firstStable := ((fixedCandidateLookupInvariant timeouts) leaks original.application
    candidate firstFixed).environmentStep original nextOriginal command rfl left
  have secondStable := ((fixedCandidateLookupInvariant timeouts) leaks repaired.application
    candidate secondFixed).environmentStep repaired nextRepaired command rfl right
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [State.bindingResult, firstStable] using remembered
  · rwa [firstStable]
  · rwa [secondStable]
  · simpa only [State.bindingResult, secondStable] using succeeds
  · simpa only [State.bindingResult, firstStable, secondStable] using successes

end Vegas.EventGraphRuntime.BindingMemory
