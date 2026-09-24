/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Expr.Simple
import Vegas.Pending.ReactiveNormalPolicy

/-! # Bounded responses retain errors and signaling

The menu contains every packet form over its declared value and handle domains.
These checks exercise semantic distinctions that a compiler-output-only menu
would miss. The assessment theorem establishes consistency, not optimality.
-/

noncomputable section

namespace VegasTests.ReactiveFiniteResponses

open GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

private abbrev inputs : Fin 0 → EventGraph.EventField Bool simpleExpr := Fin.elim0
private abbrev outputs : Fin 1 → EventGraph.EventField Bool simpleExpr :=
  fun _ => .binding false .bool

private abbrev graph : EventGraph Bool simpleExpr where
  inputCount := 0
  order := { eventCount := 1, predecessors := fun _ => ∅, predecessor_lt := by simp }
  inputLayout := inputs
  outputLayout := outputs
  nodes _ := EventGraph.EventCode.bind
    (layout := EventGraph.fieldLayout inputs outputs) false .bool
  reads_available := by
    intro event field member
    exact False.elim (Finset.notMem_empty field member)
  payoffs := []

private def runtime : EventGraphRuntime graph where
  deadline _ := 2

private def leaks : MessageNetwork.ObservationRule Bool (Payload graph) :=
  fun _ _ => FinDist.pure ∅

private abbrev app := runtime.reactiveApplication leaks

private def initial : app.Execution :=
  ReactiveApplication.Execution.initial app
    (State.initial (graph := graph) (fun input => nomatch input))

private def bounds : MessageBounds graph := by
  classical
  exact ⟨2, {⟨.bool, false⟩, ⟨.bool, true⟩, ⟨.int, 0⟩, ⟨.int, 1⟩}⟩

private abbrev menu := bounds.menu runtime leaks

/-- Malformed traffic remains a choice, even at an off-path information state. -/
theorem malformed_available (who : Bool) (past : List app.PlayerEntry)
    (view : app.PlayerView) (bit : Bool) :
    (⟨some (.submit ⟨.malformed ⟨.bool, bit⟩, none⟩)⟩ : app.Action) ∈
      menu.actions who past view := by
  classical
  rw [MessageBounds.menu_mem]
  refine ⟨⟨?_, trivial⟩, ?_⟩
  · cases bit <;> simp [MessageBounds.AllowsPacket, bounds]
  · change (⟨some (.submit
      ((⟨.malformed ⟨.bool, bit⟩, none⟩ : Submission graph).normalizeReactive who
        view.application))⟩ : app.Action) = _
    rw [Submission.normalizeReactive_none]

/-- Neither the wrong method nor the foreign handle nor the wrong type erases
a bounded packet from the response menu. -/
theorem invalid_opening_available (past : List app.PlayerEntry) (view : app.PlayerView) :
    (⟨some (.submit ⟨.opening 0 (true, .prepared 1) ⟨.int, 1⟩, none⟩)⟩ : app.Action) ∈
      menu.actions false past view := by
  classical
  rw [MessageBounds.menu_mem]
  refine ⟨⟨?_, trivial⟩, ?_⟩
  · simp [MessageBounds.AllowsPacket, MessageBounds.AllowsHandle, bounds]
  · change (⟨some (.submit
      ((⟨.opening 0 (true, .prepared 1) ⟨.int, 1⟩, none⟩ : Submission graph).normalizeReactive
        false view.application))⟩ : app.Action) = _
    rw [Submission.normalizeReactive_none]

/-- An arbitrary private annotation on a malformed packet has no semantic
effect. Its representation does not need to fit the public value alphabet. -/
theorem irrelevant_material_erased (raw : Raw simpleExpr) (who : Bool)
    (past : List app.PlayerEntry) (view : app.PlayerView) :
    (runtime.reactiveNormalization leaks).action who past view
        ⟨some (.submit ⟨.malformed ⟨.bool, true⟩, some raw⟩)⟩ =
      ⟨some (.submit ⟨.malformed ⟨.bool, true⟩, none⟩)⟩ := by
  simp [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
    Submission.normalizeReactive, openingEffective]

theorem arbitrary_irrelevant_material_admitted (raw : Raw simpleExpr) (who : Bool)
    (past : List app.PlayerEntry) (view : app.PlayerView) :
    (runtime.reactiveNormalization leaks).action who past view
        ⟨some (.submit ⟨.malformed ⟨.bool, true⟩, some raw⟩)⟩ ∈
      menu.actions who past view := by
  rw [irrelevant_material_erased]
  exact malformed_available who past view true

/-- A wrong-type fresh meaning is still fixed by submission. It is private
semantic data, even when the particular Boolean event cannot use it. -/
theorem wrong_type_meaning_retained :
    let response := runtime.reactiveBinding leaks false 0 .int (.success 1) 0
    (runtime.reactiveNormalization leaks).action false [] (initial.observe app false)
        response = response ∧
      response ∈ menu.actions false [] (initial.observe app false) ∧
      (initial.respond app false response).application.bindingResult
        (false, .prepared 0) .int = .success 1 := by
  classical
  have effective : openingEffective false (initial.observe app false).application
      (.commitment 0 (false, .prepared 0)) := ⟨rfl, rfl⟩
  have normal : (runtime.reactiveNormalization leaks).action false [] (initial.observe app false)
      (runtime.reactiveBinding leaks false 0 .int (.success 1) 0) =
        runtime.reactiveBinding leaks false 0 .int (.success 1) 0 := by
    change (⟨some (.submit
      ((⟨.commitment 0 (false, .prepared 0), some ⟨.int, 1⟩⟩ : Submission graph).normalizeReactive
        false (initial.observe app false).application))⟩ : app.Action) = _
    rw [Submission.normalizeReactive_effective _ _ _ effective]
    rfl
  refine ⟨normal, ?_,
    runtime.reactiveBinding_result leaks false 0 .int (.success 1) 0 initial rfl⟩
  rw [MessageBounds.menu_mem]
  refine ⟨⟨?_, ?_⟩, normal⟩
  · norm_num [reactiveBinding, MessageBounds.AllowsPacket, MessageBounds.AllowsHandle, bounds]
  · simp [MessageBounds.AllowsOpening, bounds]

/-- The finite instance has the genuine unopenable choice. Normalizing cannot
repair its missing opening after submission. -/
theorem unopenable_available_and_binding :
    let response := runtime.reactiveBinding leaks false 0 .bool .failure 0
    response ∈ menu.actions false [] (initial.observe app false) ∧
      (initial.respond app false response).application.candidates.lookup
        (false, .prepared 0) = .unopenable := by
  classical
  refine ⟨?_, rfl⟩
  rw [MessageBounds.menu_mem]
  refine ⟨⟨?_, trivial⟩, ?_⟩
  · norm_num [reactiveBinding, MessageBounds.AllowsPacket, MessageBounds.AllowsHandle, bounds]
  · change (⟨some (.submit
      ((⟨.commitment 0 (false, .prepared 0), none⟩ : Submission graph).normalizeReactive
        false (initial.observe app false).application))⟩ : app.Action) = _
    rw [Submission.normalizeReactive_none]
    rfl

/-- Different malformed messages are not collapsed into one public signal. -/
theorem malformed_packets_distinct :
    (initial.respond app false
      ⟨some (.submit ⟨.malformed ⟨.bool, false⟩, none⟩)⟩).network.pending ≠
      (initial.respond app false
        ⟨some (.submit ⟨.malformed ⟨.bool, true⟩, none⟩)⟩).network.pending := by
  intro same
  change [Message.mk (false, 0) (Payload.malformed (graph := graph) ⟨.bool, false⟩)] =
    [Message.mk (false, 0) (Payload.malformed (graph := graph) ⟨.bool, true⟩)] at same
  have raw : (⟨.bool, false⟩ : Raw simpleExpr) = ⟨.bool, true⟩ :=
    Payload.malformed.inj (Message.mk.inj (List.cons.inj same).1).2
  have := congrArg (fun value : Raw simpleExpr => value.as? .bool) raw
  simp [Raw.as?_mk] at this

theorem unknown_replay_excluded (id : MessageId Bool) :
    (⟨some (.replay id)⟩ : app.Action) ∉ menu.actions false [] (initial.observe app false) := by
  rw [MessageBounds.menu_mem]
  simp [ReactiveApplication.SubmissionNormalization.ReplayKnown,
    ReactiveApplication.ResponseMenu.knownPackets, initial,
    ReactiveApplication.Execution.initial, ReactiveApplication.Execution.observe,
    ReactiveApplication.outputs, MessageNetwork.observe, MessageNetwork.empty]

/-- Real replay eligibility uses remembered emissions; no numeric bound on
the envelope identifier is introduced by the finite syntax bounds. -/
theorem known_replay_retained (execution : app.Execution) (who : Bool)
    (valid : execution.InputRecall app) (message : Message Bool app.Payload)
    (known : message ∈ execution.network.known who) :
    (⟨some (.replay message.id)⟩ : app.Action) ∈
      menu.actions who (execution.recall who) (execution.observe app who) := by
  apply bounds.known_replay_available
  exact (ReactiveApplication.SubmissionNormalization.replayKnown_iff
    execution who valid message.id).mpr ⟨message, known, rfl⟩

theorem complete_menu_finite_histories (horizon : Nat) (scheduler : app.Scheduler) :
    Finite (menu.protocol (FinDist.pure initial.application) horizon scheduler).History :=
  inferInstance

theorem complete_menu_consistent_assessment (horizon : Nat) (scheduler : app.Scheduler) :
    GameTheory.Protocol.InformationModel.BehavioralAssessment.IsSequentiallyConsistent
      (menu.bayesAssessment (FinDist.pure initial.application) horizon scheduler)
      (menu.decisionInformationAntichain (FinDist.pure initial.application)
        horizon scheduler) :=
  menu.bayesAssessment_consistent _ _ _

end VegasTests.ReactiveFiniteResponses
