/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitTimingInformationProperPolicy
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.PhaseOpeningPolicy

/-! # Genuine prepared binding and truthful opening responses in the hidden-input runtime -/

noncomputable section

namespace Vegas.Examples.CommitTimingInformation

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem properPolicy_binding_response (value : Bool)
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool)
    (selected : app.Scheduler) (control : app.Control)
    (trace : (rawMenu.protocol initial horizon selected).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (event : graph.EventId) (binding : graph.outputLayout event = .binding who .bool)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ app.outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (emit : (PhaseSeedScheduler.serviceClocks runtime leaks
        ⟨control.execution.application.attempt, event⟩ who (control.execution.recall who)
          (control.execution.observe app who)).length = 1 ∨
      rule who ⟨control.execution.application.attempt, event⟩
        (PhaseSeedScheduler.serviceClocks runtime leaks
          ⟨control.execution.application.attempt, event⟩ who (control.execution.recall who)
            (control.execution.observe app who)) = true) :
    ∃ serial, serial < horizon ∧
      properPolicy value rule who (control.execution.recall who)
          (control.execution.observe app who) =
        PMF.pure (phaseBindingResponse runtime leaks who event .bool (.success value) serial) ∧
      reactiveFreshSlot (control.execution.observe app who).application.1 = some serial ∧
      control.execution.application.current.native.candidates.lookup (who, .prepared serial) =
        .fresh ∧
      (let next := control.execution.respond app who
        (phaseBindingResponse runtime leaks who event .bool (.success value) serial);
       next.application.current.native.bindingResult (who, .prepared serial) .bool) =
        .success value := by
  classical
  have compiledTrace := trace
  let results : List app.PlayerEntry → app.PlayerView →
      PMF (PublicationResult (simpleExpr.Val .bool)) :=
    fun past view => ((constantBindingLaw value) who event .bool binding past view).map
      PublicationResult.success
  have constant (past : List app.PlayerEntry) (view : app.PlayerView) :
      results past view = PMF.pure (.success value) := by
    simp only [results, constantBindingLaw, PMF.pure_map]
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon selected
    (rawMenu.toRawTrace initial horizon selected trace)
  have service := phaseCountServicePolicy_binding setup .concurrentReveals runtime leaks bounds
    (constantBindingLaw value) rule 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    0 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num)
    control.execution valid who event .bool binding request
  have send : properPolicy value rule who (control.execution.recall who)
      (control.execution.observe app who) =
      PhaseCount.phaseBindingPolicy runtime leaks bounds who event .bool results
        (control.execution.recall who) (control.execution.observe app who) := by
    change properPolicy value rule who _ _ = _ at service
    rw [service]
    dsimp only [PhaseCount.bindingServiceReference, PhaseCount.bindingServiceBase,
      PhaseCount.bindingResultEncoder]
    simp only [zero_add, mix_zero]
    split
    · rfl
    · rename_i notFirst
      have chosen := emit.resolve_left notFirst
      rw [ite_eq_left chosen]
  obtain ⟨serial, bounded, encoded, resultLaw⟩ :=
    PhaseCount.phaseBindingPolicy_of_history runtime leaks bounds who event .bool binding results
      rawMenu plan (setup.initialLaw.map encodeInputs) horizon selected (by rfl)
      control compiledTrace active request unsent (fun value => by
        exact Finset.mem_image.mpr ⟨value, Finset.mem_univ _, rfl⟩)
  have literal : PhaseCount.phaseBindingPolicy runtime leaks bounds who event .bool results
      (control.execution.recall who) (control.execution.observe app who) =
      PMF.pure (phaseBindingResponse runtime leaks who event .bool (.success value) serial) := by
    rw [encoded, constant, PMF.pure_map]
  have supported : phaseBindingResponse runtime leaks who event .bool (.success value) serial ∈
      (PhaseCount.phaseBindingPolicy runtime leaks bounds who event .bool results
        (control.execution.recall who) (control.execution.observe app who)).support := by
    rw [literal]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have selected : reactiveFreshSlot (control.execution.observe app who).application.1 =
      some serial := by
    unfold PhaseCount.phaseBindingPolicy at supported
    split at supported
    · have impossible := congrArg (fun response : app.Action => response.transmission)
        ((PMF.mem_support_pure_iff _ _).mp supported)
      cases impossible
    · rename_i freshSerial chosen
      split at supported
      · obtain ⟨result, _positive, equal⟩ := PMF.support_map .. ▸ supported
        have slots := congrArg (PhaseCandidates.responseCandidateSlot runtime leaks) equal
        change some freshSerial = some serial at slots
        exact chosen.trans slots
      · have impossible := congrArg (fun response : app.Action => response.transmission)
          ((PMF.mem_support_pure_iff _ _).mp supported)
        cases impossible
  have fresh : control.execution.application.current.native.candidates.lookup
      (who, .prepared serial) = .fresh :=
    reactiveFreshSlot_spec (control.execution.observe app who).application.1 serial selected
  refine ⟨serial, bounded, send.trans literal, selected, fresh, ?_⟩
  rw [literal, PMF.pure_map, constant] at resultLaw
  have supports := congrArg (fun law => law.support) resultLaw
  simpa only [PMF.support_pure, Set.singleton_eq_singleton_iff] using supports

/-- The actual protected opening response uses the stored successful value and
its accepted handle. It is derived from native history and remains the same
under all hidden alternatives in the information fiber. -/
theorem properPolicy_opening_response (prepared : Bool)
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool)
    (selected : app.Scheduler) (control : app.Control)
    (trace : (countedMenu.protocol initial horizon selected).Trace (some control))
    (who : Player) (event : graph.EventId)
    (binding : FieldRef graph.layout (.binding who .bool))
    (checks : List (GuardCheck graph.layout .bool))
    (outputEq : graph.outputLayout event = .publication .bool)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      EventCode.resolve (L := simpleExpr) (layout := graph.layout)
        who BaseTy.bool binding checks)
    (node : nodeView graph event = .resolve who .bool binding checks outputEq codeEq)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ app.outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (value : Bool)
    (stored : binding.get? control.execution.application.current.native.config.store =
      some (.success value)) :
    ∃ candidate, control.execution.application.current.native.accepted binding.field =
      some candidate ∧
      properPolicy prepared rule who (control.execution.recall who)
          (control.execution.observe app who) =
        PMF.pure (PhaseCount.phaseOpeningResponse runtime leaks event candidate
          ⟨.bool, value⟩) := by
  classical
  have compiledTrace := trace
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon selected
    (countedMenu.toRawTrace initial horizon selected trace)
  have service := phaseCountServicePolicy_opening setup .concurrentReveals runtime leaks bounds
    (constantBindingLaw prepared) rule 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    0 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num)
    control.execution valid who event .bool binding checks outputEq codeEq request
  obtain ⟨candidate, accepted, literal⟩ :=
    PhaseCount.phaseOpeningPolicy_of_history runtime leaks bounds plan
      (setup.initialLaw.map encodeInputs) horizon selected compiledTrace
      who event .bool binding checks
      outputEq codeEq node request unsent value stored
      (Finset.mem_image.mpr ⟨value, Finset.mem_univ _, rfl⟩) (fun _ _ => PMF.pure true)
  refine ⟨candidate, accepted, ?_⟩
  change properPolicy prepared rule who _ _ = _ at service
  rw [service]
  simp only [mix_zero]
  rw [literal, PMF.pure_map]
  rfl

end Vegas.Examples.CommitTimingInformation
