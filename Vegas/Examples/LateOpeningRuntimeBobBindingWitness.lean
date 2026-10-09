/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobBindingInformation
import Vegas.Examples.LateOpeningRuntimeLateHistories
import Vegas.Examples.LateOpeningRuntimeProtectedOpening

/-! # A genuine failed-Alice first-binding decision

For every finite public lottery weight, the outside-option branch followed
by Alice's actual expiry reaches Bob's ready clock-three binding callback in
the complete bounded raw menu. The earlier pending-opening sample may be
either seen or unseen; the witness does not conceal its contents.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobBindingWitness

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeLateAcceptance LateOpeningRuntimeLateHistories
  LateOpeningRuntimeProtectedOpening LateOpeningRuntimeBobQuietPrefix
  LateOpeningRuntimeBobBindingService

/-- Every initialized type and first pending observation has an actual
failed-Alice binding representative, with a trace in the complete bounded
raw protocol and the truthful earlier silent Bob response. -/
theorem failed_binding_representative (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (seen : Bool) :
    ∃ decision : LateOpeningRuntimeBobBindingInformation.DecisionHistory weight nonnegative,
      Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
          (some ⟨14, some bob, decision.execution⟩)) ∧
        EventGraphRuntime.State.Invariant (graph := nativeGraph)
          (setup.eventInputs (sourceInitial bit label)) decision.execution.application := by
  obtain ⟨lotteryTrace⟩ := beforeLottery_trace weight nonnegative bit label 0 seen (Or.inl rfl)
  have rawLottery := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) lotteryTrace
  have unresolved : aliceEvent ∉
      (beforeLottery bit label 0 seen).application.config.cut.completed := by
    rw [beforeLottery_physical]
    change aliceEvent ∉ (∅ : Finset nativeGraph.EventId)
    decide
  obtain ⟨failed, expiry, failedStored, failedCursor⟩ := lottery_miss_expires weight nonnegative
    (latePlayers bit 0) (beforeLottery bit label 0 seen) rawLottery rfl unresolved
  have initialized : (beforeLottery bit label 0 seen).application.config.inputs =
      setup.eventInputs (sourceInitial bit label) := by
    rw [beforeLottery_physical]
    rfl
  obtain ⟨otherBit, otherLabel, valid⟩ := LateOpeningRuntimeReadout.history_initial_invariant
    LateOpeningRuntimeService.runtime leaks LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) ⟨18, none, _⟩ rawLottery
  have sameInputs := valid.reachable.inputs_eq.symm.trans initialized
  have validInitialized : EventGraphRuntime.State.Invariant (graph := nativeGraph)
      (setup.eventInputs (sourceInitial bit label))
        (beforeLottery bit label 0 seen).application := sameInputs ▸ valid
  have invariant := LateOpeningRuntimeService.runtime.reactiveStateInvariant leaks
    (setup.eventInputs (sourceInitial bit label))
  have failedValid := (ReactiveApplication.Invariant.policyInvariant app invariant
    (latePlayers bit 0)).runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      3 (beforeLottery bit label 0 seen) failed validInitialized expiry
  obtain ⟨failedTrace⟩ := rawMenu.trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit 0)
      (latePlayers_covered bit 0) 15 3 (beforeLottery bit label 0 seen) failed lotteryTrace expiry
  obtain ⟨initialBobTrace⟩ := bobObserved_first_trace weight nonnegative bit label seen
  have rawInitialBob := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) initialBobTrace
  have reached : failed ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit 0) 6 (bobObserved bit label 0 seen)).support := by
    rw [app.runRounds_add (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit 0) 3 3, beforeLottery_run, PMF.pure_bind]
    exact expiry
  have quiet : SilentRecall (bobObserved bit label 0 seen) := by
    intro entry member
    rw [bobObserved_first_recall] at member
    cases List.mem_singleton.mp member
    rfl
  have initiallyUnresolved : aliceEvent ∉
      (bobObserved bit label 0 seen).application.config.cut.completed := by
    change aliceEvent ∉ (∅ : Finset nativeGraph.EventId)
    decide
  obtain ⟨observed, sampled⟩ := (failed.environmentStep app (.activate bob)).support_nonempty
  obtain ⟨⟨observedTrace⟩, observedQuiet, ready, timely, _, _⟩ := binding_activation weight
    nonnegative (latePlayers bit 0) (bobObserved bit label 0 seen) failed observed rawInitialBob
      rfl initiallyUnresolved quiet reached sampled
  have selected : (.activate bob : app.Command) ∈ (LateOpeningRuntimeService.scheduler
      weight nonnegative failed.environmentRecall (failed.observeEnvironment app)).support := by
    change _ ∈ (stageChoice weight nonnegative failed.environmentRecall.length _).support
    rw [failedCursor]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨boundedTrace⟩ := rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 failed observed (.activate bob)
      failedTrace selected sampled
  have physical : observed.application = failed.application := by
    obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ sampled
    obtain ⟨sample, _, rfl⟩ := PMF.support_map .. ▸ supported
    rfl
  let decision : LateOpeningRuntimeBobBindingInformation.DecisionHistory weight nonnegative :=
    ⟨observed, observedTrace, observedQuiet, physical ▸ failedStored, ready, timely⟩
  exact ⟨decision, ⟨boundedTrace⟩, physical ▸ failedValid⟩

theorem failed_binding_class_nonempty (weight : ℝ) (nonnegative : 0 ≤ weight) :
    Nonempty (LateOpeningRuntimeBobBindingInformation.DecisionHistory weight nonnegative) := by
  obtain ⟨decision, _⟩ := failed_binding_representative weight nonnegative false 0 false
  exact ⟨decision⟩

/-- The failed-publication witness is a genuine assessment information site,
with an actual bounded representative of the complete raw protocol. -/
theorem failed_binding_information_representative (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (seen : Bool) :
    ∃ (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
      (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
        bob site.1)
      (decision : LateOpeningRuntimeBobBindingInformation.DecisionHistory weight nonnegative),
      representative.1.state = some ⟨14, some bob, decision.execution⟩ ∧
        EventGraphRuntime.State.Invariant (graph := nativeGraph)
          (setup.eventInputs (sourceInitial bit label)) decision.execution.application := by
  obtain ⟨decision, ⟨boundedTrace⟩, valid⟩ :=
    failed_binding_representative weight nonnegative bit label seen
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨14, some bob, decision.execution⟩, boundedTrace⟩
  have running : ¬ (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).terminal history.state := by
    change ¬ (14 = 0 ∧ some bob = none)
    simp
  obtain ⟨site, same⟩ :=
    (LateOpeningRuntimeNash.model weight nonnegative).exists_informationSite_of_active
      bob history running rfl
  exact ⟨site, ⟨history, same.symm⟩, decision, rfl, valid⟩

end Vegas.Examples.LateOpeningRuntimeBobBindingWitness
