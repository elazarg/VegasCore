/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobBindingInformation
import Vegas.Examples.LateOpeningRuntimeLateHistories
import Vegas.Examples.LateOpeningRuntimeProtectedOpening
import Vegas.Pending.ReactiveAssociationPersistence

/-! # A genuine failed-Alice first-binding decision

For every finite public lottery weight, the outside-option branch followed
by Alice's actual expiry reaches Bob's ready clock-three binding callback in
the complete bounded raw menu. The earlier pending-opening sample may be
either seen or unseen; the witness does not conceal its contents.
When the first sample disclosed the opening, its authentic certificate and
accepted association remain visible at the later binding decision.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobBindingWitness

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeLatePrefix
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
          (setup.eventInputs (sourceInitial bit label)) decision.execution.application ∧
        (seen = true → LateOpeningRuntimeService.runtime.bindingEvidenceObserved leaks
          (decision.execution.observe app bob) ⟨alice, .bool, aliceBinding, bit⟩) := by
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
  refine ⟨decision, ⟨boundedTrace⟩, physical ▸ failedValid, ?_⟩
  intro seenOpening
  subst seen
  have bindingValid : (beforeLottery bit label 0 true).application.BindingInvariant := by
    rw [beforeLottery_physical]
    exact State.BindingInvariant.copy (graph := nativeGraph)
      (before := State.initial (graph := nativeGraph) (setup.eventInputs (sourceInitial bit label)))
      (after := { initialPhysical bit label with clock := 2 })
      (State.initial_bindingInvariant (graph := nativeGraph)
        (setup.eventInputs (sourceInitial bit label))) rfl rfl rfl
  have certificate : LateOpeningRuntimeService.runtime.bindingEvidenceObserved leaks
      ((beforeLottery bit label 0 true).observe app bob)
        ⟨alice, .bool, aliceBinding, bit⟩ := by
    refine ⟨aliceCandidate, ?_, ?_⟩
    · change (beforeLottery bit label 0 true).application.accepted aliceBinding.field =
        some aliceCandidate
      rw [beforeLottery_physical]
      rfl
    · change (⟨aliceCandidate, ⟨.bool, bit⟩⟩ : OpeningFact nativeGraph) ∈
        (((beforeLottery bit label 0 true).network.observe bob).leaked ++
          ((beforeLottery bit label 0 true).network.observe bob).ledger).flatMap
            (fun message => message.payload.evidence.toList)
      rw [beforeLottery_bobNetwork]
      simp [openingMessage]
  have invariant := LateOpeningRuntimeService.runtime.observedBinding_policyInvariant leaks
    (latePlayers bit 0) bob ⟨alice, .bool, aliceBinding, bit⟩
  have retained := invariant.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    3 (beforeLottery bit label 0 true) failed ⟨bindingValid, certificate⟩ expiry
  exact (invariant.environment failed observed (.activate bob) retained sampled).2

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
          (setup.eventInputs (sourceInitial bit label)) decision.execution.application ∧
        (seen = true → LateOpeningRuntimeService.runtime.bindingEvidenceObserved leaks
          (decision.execution.observe app bob) ⟨alice, .bool, aliceBinding, bit⟩) := by
  obtain ⟨decision, ⟨boundedTrace⟩, valid, observed⟩ :=
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
  exact ⟨site, ⟨history, same.symm⟩, decision, rfl, valid, observed⟩

end Vegas.Examples.LateOpeningRuntimeBobBindingWitness
