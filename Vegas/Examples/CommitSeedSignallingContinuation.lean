/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingTimingIncentives
import Vegas.Examples.CommitSeedSignallingCountedContinuation
import Vegas.Pending.PhaseOpeningPolicy

/-! # Literal proper responses at genuine native continuation sites -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- At every genuine unsent chosen binding callback the proper policy emits
one fresh typed TRUE declaration. The proof covers arbitrary raw past traffic. -/
theorem properPolicy_binding_response
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
      properPolicy rule who (control.execution.recall who)
          (control.execution.observe app who) =
        PMF.pure (phaseBindingResponse runtime leaks who event .bool (.success true) serial) ∧
      reactiveFreshSlot (control.execution.observe app who).application.1 = some serial ∧
      control.execution.application.current.native.candidates.lookup (who, .prepared serial) =
        .fresh ∧
      (let next := control.execution.respond app who
        (phaseBindingResponse runtime leaks who event .bool (.success true) serial);
       next.application.current.native.bindingResult (who, .prepared serial) .bool) =
        .success true := by
  classical
  let results : List app.PlayerEntry → app.PlayerView →
      PMF (PublicationResult (simpleExpr.Val .bool)) :=
    fun past view => (trueBindingLaw who event .bool binding past view).map
      PublicationResult.success
  have constant (past : List app.PlayerEntry) (view : app.PlayerView) :
      results past view = PMF.pure (.success true) := by
    simp only [results, trueBindingLaw, PMF.pure_map]
  have valid := raw_native_valid selected control
    (rawMenu.toRawTrace initial horizon selected trace)
  have service := phaseCountServicePolicy_binding setup .concurrentReveals runtime leaks bounds
    trueBindingLaw rule 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    0 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num)
    control.execution valid who event .bool binding request
  have send : properPolicy rule who (control.execution.recall who)
      (control.execution.observe app who) =
      PhaseCount.phaseBindingPolicy runtime leaks bounds who event .bool results
        (control.execution.recall who) (control.execution.observe app who) := by
    change properPolicy rule who _ _ = _ at service
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
      control trace active request unsent (fun value => by
        exact Finset.mem_image.mpr ⟨value, Finset.mem_univ _, rfl⟩)
  have literal : PhaseCount.phaseBindingPolicy runtime leaks bounds who event .bool results
      (control.execution.recall who) (control.execution.observe app who) =
      PMF.pure (phaseBindingResponse runtime leaks who event .bool (.success true) serial) := by
    rw [encoded, constant, PMF.pure_map]
  have supported : phaseBindingResponse runtime leaks who event .bool (.success true) serial ∈
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
theorem properPolicy_opening_response
    (rule : Player → CommitAttemptEvent graph → List Nat → Bool)
    (control : app.Control) (trace : countedProtocol.Trace (some control))
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
      properPolicy rule who (control.execution.recall who)
          (control.execution.observe app who) =
        PMF.pure (PhaseCount.phaseOpeningResponse runtime leaks event candidate
          ⟨.bool, value⟩) := by
  classical
  have valid := raw_native_valid scheduler control
    (countedMenu.toRawTrace initial horizon scheduler trace)
  have service := phaseCountServicePolicy_opening setup .concurrentReveals runtime leaks bounds
    trueBindingLaw rule 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    0 (by norm_num) (by norm_num) 0 (by norm_num) (by norm_num)
    control.execution valid who event .bool binding checks outputEq codeEq request
  obtain ⟨candidate, accepted, literal⟩ :=
    PhaseCount.phaseOpeningPolicy_of_history runtime leaks bounds plan
      (setup.initialLaw.map encodeInputs) horizon scheduler trace who event .bool binding checks
      outputEq codeEq node request unsent value stored
      (Finset.mem_image.mpr ⟨value, Finset.mem_univ _, rfl⟩) (fun _ _ => PMF.pure true)
  refine ⟨candidate, accepted, ?_⟩
  change properPolicy rule who _ _ = _ at service
  rw [service]
  simp only [mix_zero]
  rw [literal, PMF.pure_map]
  rfl

/-- The exact counted-history reflection is available for the concrete fixed
late deviation; assessed opponents are left unchanged on their raw inputs. -/
theorem fixedLateContinuation_counted_terminal_support
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (who : Player) (history : countedProtocol.History) (final : rawProtocol.History)
    (supported : final ∈ (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Function.update assessment.strategy who (fixedLateContinuation who))
      (countedInRaw.history initial horizon scheduler history)).support) :
    ∃ retained : countedProtocol.History,
      countedInRaw.history initial horizon scheduler retained = final := by
  exact raw_equilibrium_counted_deviation_terminal_support assessment equilibrium who
    (fixedLatePolicy who) (fixedLatePolicy_counted who) history final supported

end Vegas.Examples.CommitSeedSignalling
