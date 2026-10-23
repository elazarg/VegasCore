/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingSubmittedPreservation

/-! # Typed physical provenance of actual submitted phase bindings

Physical prepared handles persist across rollback. Their event-indexed typed
results are retained independently of logical completion records, which are
masked when a commitment attempt is canceled.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Physical fixedness and typed success at one actual submitted event.
The type parameter is the event's declared payload, not an arbitrary type at
which a previously prepared raw value might decode. -/
def PreparedBindingResult (original repaired : State graph)
    (candidate : Handle graph) (payload : L.Ty) : Prop :=
  original.candidates.lookup candidate ≠ .fresh ∧
    repaired.candidates.lookup candidate ≠ .fresh ∧
    (∃ value, repaired.bindingResult candidate payload = .success value) ∧
    ∀ value, original.bindingResult candidate payload = .success value →
      repaired.bindingResult candidate payload = .success value

omit [DecidableEq Player] in
/-- Fixed physical candidate meanings transport the extracted typed tail
through operations that may discard logical old-generation records. -/
theorem PreparedBindingResult.rebase {original repaired nextOriginal nextRepaired : State graph}
    {candidate : Handle graph} {payload : L.Ty}
    (prepared : PreparedBindingResult original repaired candidate payload)
    (left : KeepsFixedCandidates original nextOriginal)
    (right : KeepsFixedCandidates repaired nextRepaired) :
    PreparedBindingResult nextOriginal nextRepaired candidate payload := by
  have first := left candidate prepared.1
  have second := right candidate prepared.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [first] using prepared.1
  · simpa only [second] using prepared.2.1
  · simpa only [State.bindingResult, second] using prepared.2.2.1
  · simpa only [State.bindingResult, first, second] using prepared.2.2.2

/-- Each actual signed binding is typed at its own event. A mistyped old raw
value is not required to preserve its decode at an unrelated event type. -/
def PreparedBindings (owner : Player) (original repaired : (app).Execution) : Prop :=
  ∀ message ∈ original.network.inputs, message.sender = owner →
    ∀ event candidate, message.payload.packet.call = .commitment event candidate →
      ∀ payload (outputEq : graph.outputLayout event = .binding owner payload)
        (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
          (graph.nodes event) = .bind owner payload),
        nodeView graph event = .bind owner payload outputEq codeEq →
          PreparedBindingResult original.application.current.native
            repaired.application.current.native candidate payload

/-- Initialization uses the same literal initial draw and has no submitted
binding to repair, including when that draw contains private bindings. -/
theorem preparedBindings_initial (owner : Player) (first second : PhaseRuntimeState graph) :
    PreparedBindings runtime leaks owner (ReactiveApplication.Execution.initial app first)
      (ReactiveApplication.Execution.initial app second) := by
  intro message member
  cases member

/-- Rebase only the persistent physical meanings. No equality of old logical
completion records, retired private snapshots, or semantic stores is needed. -/
theorem PreparedBindings.rebase {owner : Player}
    {original repaired nextOriginal nextRepaired : (app).Execution}
    (prepared : PreparedBindings runtime leaks owner original repaired)
    (inputs : nextOriginal.network.inputs = original.network.inputs)
    (left : KeepsFixedCandidates original.application.current.native
      nextOriginal.application.current.native)
    (right : KeepsFixedCandidates repaired.application.current.native
      nextRepaired.application.current.native) :
    PreparedBindings runtime leaks owner nextOriginal nextRepaired := by
  intro message member sender event candidate call payload outputEq codeEq node
  rw [inputs] at member
  exact (prepared message member sender event candidate call payload outputEq codeEq node).rebase
    left right

/-- Every actual environment command retains the typed meaning of every old
signed binding through arbitrary expiry, phase draining and generation reset. -/
theorem PreparedBindings.environment {owner : Player}
    {original repaired nextOriginal nextRepaired : (app).Execution}
    (prepared : PreparedBindings runtime leaks owner original repaired)
    (command : (app).Command)
    (left : nextOriginal ∈ (original.environmentStep app command).support)
    (right : nextRepaired ∈ (repaired.environmentStep app command).support) :
    PreparedBindings runtime leaks owner nextOriginal nextRepaired := by
  apply prepared.rebase
  · exact (app).environmentStep_inputs original nextOriginal command left
  · exact (phaseApplication_preservesFixedCandidates runtime leaks).environmentStep
      original nextOriginal command left
  · exact (phaseApplication_preservesFixedCandidates runtime leaks).environmentStep
      repaired nextRepaired command right

end Vegas.EventGraphRuntime.BindingShadow
