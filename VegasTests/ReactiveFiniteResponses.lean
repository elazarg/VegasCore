/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Expr.Simple
import Vegas.Pending.ReactiveNormalPolicy
import Vegas.Pending.ReactiveFiniteConsistency

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

private def leaks : MessageNetwork.ObservationRule Bool (WitnessedPacket graph) :=
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
    (⟨some (.submit ⟨⟨.malformed ⟨.bool, bit⟩, none⟩, .none⟩)⟩ : app.Action) ∈
      menu.actions who past view := by
  classical
  rw [MessageBounds.menu_mem]
  refine ⟨⟨⟨?_, trivial⟩, trivial⟩, ?_⟩
  · cases bit <;> simp [MessageBounds.AllowsPacket, bounds]
  · simp [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
      WitnessedSubmission.normalizeReactive, Submission.normalizeReactive_none,
      EvidenceRequest.normalizeKnown]


/-- Neither the wrong method nor the foreign handle nor the wrong type erases
a bounded packet from the response menu. -/
theorem invalid_opening_available (past : List app.PlayerEntry) (view : app.PlayerView) :
    (⟨some (.submit ⟨⟨.opening 0 (true, .prepared 1) ⟨.int, 1⟩, none⟩, .none⟩)⟩ : app.Action) ∈
      menu.actions false past view := by
  classical
  rw [MessageBounds.menu_mem]
  refine ⟨⟨⟨?_, trivial⟩, trivial⟩, ?_⟩
  · simp [MessageBounds.AllowsPacket, MessageBounds.AllowsHandle, bounds]
  · simp [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
      WitnessedSubmission.normalizeReactive, Submission.normalizeReactive_none,
      EvidenceRequest.normalizeKnown]


/-- An arbitrary private annotation on a malformed packet has no semantic
effect. Its representation does not need to fit the public value alphabet. -/
theorem irrelevant_material_erased (raw : Raw simpleExpr) (who : Bool)
    (past : List app.PlayerEntry) (view : app.PlayerView) :
    (runtime.reactiveNormalization leaks).action who past view
        ⟨some (.submit ⟨⟨.malformed ⟨.bool, true⟩, some raw⟩, .none⟩)⟩ =
      ⟨some (.submit ⟨⟨.malformed ⟨.bool, true⟩, none⟩, .none⟩)⟩ := by
  simp [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
    WitnessedSubmission.normalizeReactive, Submission.normalizeReactive,
    EvidenceRequest.normalizeKnown, openingEffective]

theorem arbitrary_irrelevant_material_admitted (raw : Raw simpleExpr) (who : Bool)
    (past : List app.PlayerEntry) (view : app.PlayerView) :
    (runtime.reactiveNormalization leaks).action who past view
        ⟨some (.submit ⟨⟨.malformed ⟨.bool, true⟩, some raw⟩, .none⟩)⟩ ∈
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
    simp only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
      reactiveBinding, WitnessedSubmission.normalizeReactive, EvidenceRequest.normalizeKnown]
    rw [Submission.normalizeReactive_effective false (initial.observe app false).application
      ⟨.commitment 0 (false, .prepared 0), some ⟨.int, 1⟩⟩ effective]
  refine ⟨normal, ?_,
    runtime.reactiveBinding_result leaks false 0 .int (.success 1) 0 initial rfl⟩
  rw [MessageBounds.menu_mem]
  refine ⟨⟨⟨?_, ?_⟩, trivial⟩, normal⟩
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
  refine ⟨⟨⟨?_, trivial⟩, trivial⟩, ?_⟩
  · norm_num [reactiveBinding, MessageBounds.AllowsPacket, MessageBounds.AllowsHandle, bounds]
  · simp [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
      reactiveBinding, WitnessedSubmission.normalizeReactive,
      Submission.normalizeReactive_none, EvidenceRequest.normalizeKnown]


/-- Different malformed messages are not collapsed into one public signal. -/
theorem malformed_packets_distinct :
    (initial.respond app false
      ⟨some (.submit ⟨⟨.malformed ⟨.bool, false⟩, none⟩, .none⟩)⟩).network.pending ≠
      (initial.respond app false
        ⟨some (.submit ⟨⟨.malformed ⟨.bool, true⟩, none⟩, .none⟩)⟩).network.pending := by
  intro same
  change [Message.mk (false, 0)
      (WitnessedPacket.mk (Payload.malformed (graph := graph) ⟨.bool, false⟩) none)] =
    [Message.mk (false, 0)
      (WitnessedPacket.mk (Payload.malformed (graph := graph) ⟨.bool, true⟩) none)] at same
  have raw : (⟨.bool, false⟩ : Raw simpleExpr) = ⟨.bool, true⟩ :=
    Payload.malformed.inj
      (congrArg WitnessedPacket.call (Message.mk.inj (List.cons.inj same).1).2)
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

/-- Evidence can accompany a call with no successful game effect. The request
is available independently of whether the owner actually has the certificate. -/
theorem owned_evidence_with_malformed_call (who : Bool) (past : List app.PlayerEntry)
    (view : app.PlayerView) (bit : Bool) :
    (⟨some (.submit ⟨⟨.malformed ⟨.bool, bit⟩, none⟩,
      .owned ⟨(who, .prepared 1), ⟨.bool, bit⟩⟩⟩)⟩ : app.Action) ∈
        menu.actions who past view := by
  classical
  rw [MessageBounds.menu_mem]
  refine ⟨⟨⟨?_, trivial⟩, ?_⟩, ?_⟩
  · cases bit <;> simp [MessageBounds.AllowsPacket, bounds]
  · cases bit <;>
      simp [MessageBounds.AllowsEvidence, MessageBounds.AllowsHandle, bounds]
  · simp [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
      WitnessedSubmission.normalizeReactive, Submission.normalizeReactive_none,
      EvidenceRequest.normalizeKnown]

/-- Any known certificate can be copied onto a fresh packet without bounding
the referenced envelope's serial number or requiring application acceptance. -/
theorem known_forward_retained (who : Bool) (past : List app.PlayerEntry)
    (view : app.PlayerView) (id : MessageId Bool)
    (known : ∃ message ∈ ReactiveApplication.ResponseMenu.knownPackets past view,
      message.id = id) :
    (⟨some (.submit ⟨⟨.malformed ⟨.bool, true⟩, none⟩, .forward id⟩)⟩ : app.Action) ∈
      menu.actions who past view := by
  classical
  rw [MessageBounds.menu_mem]
  refine ⟨⟨⟨?_, trivial⟩, known⟩, ?_⟩
  · simp [MessageBounds.AllowsPacket, bounds]
  · simp only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
      WitnessedSubmission.normalizeReactive, Submission.normalizeReactive_none]
    rw [EvidenceRequest.normalizeKnown_forward _ id known]

/-- Guessed reference integers do not create additional transmitted evidence.
The normal form still permits the original malformed public claim. -/
theorem unknown_forward_retains_call (id : MessageId Bool) :
    (runtime.reactiveNormalization leaks).action false [] (initial.observe app false)
        ⟨some (.submit ⟨⟨.malformed ⟨.bool, true⟩, none⟩, .forward id⟩)⟩ =
      ⟨some (.submit ⟨⟨.malformed ⟨.bool, true⟩, none⟩, .none⟩)⟩ := by
  have unknown : ¬ ∃ message ∈ ReactiveApplication.ResponseMenu.knownPackets
      ([] : List app.PlayerEntry) (initial.observe app false), message.id = id := by
    simp [ReactiveApplication.ResponseMenu.knownPackets, initial,
      ReactiveApplication.Execution.initial, ReactiveApplication.Execution.observe,
      ReactiveApplication.outputs, MessageNetwork.observe, MessageNetwork.empty]
  simpa only [Submission.normalizeReactive_none] using
    MessageBounds.unknown_forward_normalizes runtime leaks false [] (initial.observe app false)
      ⟨.malformed ⟨.bool, true⟩, none⟩ id unknown

theorem complete_menu_finite_histories (horizon : Nat) (scheduler : app.Scheduler) :
    Finite (menu.protocol (FinDist.pure initial.application) horizon scheduler).History :=
  inferInstance

theorem complete_menu_consistent_assessment (horizon : Nat) (scheduler : app.Scheduler) :
    GameTheory.Protocol.InformationModel.BehavioralAssessment.IsSequentiallyConsistent
      (menu.bayesAssessment (FinDist.pure initial.application) horizon scheduler)
      (menu.decisionInformationAntichain (FinDist.pure initial.application)
        horizon scheduler) :=
  menu.bayesAssessment_consistent _ _ _

private theorem values_covered : bounds.CoversOutputValues := by
  classical
  intro event
  change ∀ value : Bool, (⟨.bool, value⟩ : Raw simpleExpr) ∈ bounds.values
  intro bit
  cases bit <;> simp [bounds]

/-- All source policies fit, including their recovery responses after arbitrary
earlier deviations. The certificate is not restricted to first or honest play. -/
theorem all_compilers_admissible (scheduler : app.Scheduler) (horizon : Nat)
    (capacity : horizon ≤ 2) (who : Bool) (policy : graph.BehavioralPolicy who) :
    menu.Admissible (FinDist.pure initial.application) horizon scheduler who
      (runtime.compileReactivePolicy leaks who policy) := by
  simpa only [FinDist.map_pure, initial, ReactiveApplication.Execution.initial, menu, app] using
    bounds.compiledPolicy_admissible runtime leaks (FinDist.pure (fun input => nomatch input))
      horizon scheduler values_covered capacity who policy

/-- Uniform trembles can be applied to the actual compiled profile in the
complete finite game. Full mixing alone does not assert limiting optimality. -/
theorem compiled_perturbation_fullyMixed (scheduler : app.Scheduler)
    (profile : graph.BehavioralProfile) (weight : ℝ) (positive : 0 < weight)
    (atMostOne : weight ≤ 1) :
    GameTheory.Protocol.InformationModel.BehavioralAssessment.IsFullyMixed
      (menu.perturbedAssessment (FinDist.pure initial.application) 2 scheduler
        (fun who => menu.restrictPolicy (FinDist.pure initial.application) 2 scheduler who
          (runtime.compileReactivePolicy leaks who (profile who))
          (all_compilers_admissible scheduler 2 (by omega) who (profile who)))
        weight positive atMostOne) :=
  menu.perturbedAssessment_fullyMixed _ _ _ _ _ _ _

/-- The completion retains the actual compiled profile, including recovery.
The menu still contains all of the malformed and unopenable choices above. -/
theorem compiled_consistent_assessment (scheduler : app.Scheduler)
    (profile : graph.BehavioralProfile) :
    ∃ assessment : (menu.information (FinDist.pure initial.application)
        2 scheduler).BehavioralAssessment,
      assessment.strategy = (fun who => menu.restrictPolicy (FinDist.pure initial.application)
        2 scheduler who (runtime.compileReactivePolicy leaks who (profile who))
          (all_compilers_admissible scheduler 2 (by omega) who (profile who))) ∧
      assessment.IsSequentiallyConsistent
        (menu.decisionInformationAntichain (FinDist.pure initial.application) 2 scheduler) :=
  menu.exists_consistent_assessment _ _ _ _

private def usedZero : app.Execution :=
  initial.respond app false (runtime.reactiveBinding leaks false 0 .bool (.success true) 0)

/-- Reusing one submitted handle consumes no additional candidate. A
foreign handle reference cannot reserve that owner's candidate either. -/
theorem replay_and_foreign_submission_leave_fresh :
    ((usedZero.respond app false ⟨some (.replay (false, 0))⟩).respond app true
      ⟨some (.submit ⟨⟨.commitment 0 (false, .prepared 1),
        some ⟨.bool, false⟩⟩, .none⟩)⟩).application.candidates.lookup
      (false, .prepared 1) = .fresh := rfl

/-- Exhaustion is possible after all allotted responses; the supply theorem
guarantees a handle at an active decision, not an extra response past the horizon. -/
theorem two_responses_can_use_two_slots :
    let usedBoth := usedZero.respond app false
      (runtime.reactiveBinding leaks false 0 .bool .failure 1)
    ∀ serial : Fin 2, usedBoth.application.candidates.lookup
      (false, .prepared serial.val) ≠ .fresh := by
  intro usedBoth serial
  fin_cases serial <;> decide

end VegasTests.ReactiveFiniteResponses
