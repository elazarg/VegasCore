/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLateResponseKernel
import Vegas.Examples.LateOpeningRuntimeAliceTremble
import Vegas.Examples.LateOpeningRuntimeRetryKernel

/-! # Actual final pending-opening classes for every admitted private alias

A genuine first submission need not use canonical private syntax. Its actual
bounded-menu history extends through either fair receiver sample and a quiet
receiver response to the final sender callback. The sender's entire private
submission recall is retained when the native retry bound is attached there.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeRetryWitness

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeLatePrefixKernel LateOpeningRuntimeLateResponseKernel
  LateOpeningRuntimeObservation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (bit : Bool) (label : Fin 3) (submission : app.Submission)
  (available : (⟨some submission⟩ : app.Action) ∈ rawMenu.actions alice
    ((firstLateDecision bit label).recall alice) ((firstLateDecision bit label).observe app alice))
  (seen : Bool)

include available in
theorem final_decision_trace :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨18, some alice,
          finalDecision bit label ⟨some submission⟩ (if seen then {(alice, 0)} else ∅)⟩)) := by
  let first := firstSent bit label ⟨some submission⟩
  let observed := first.sampledActivation app bob (if seen then {(alice, 0)} else ∅)
  let quiet := earlyQuiet bit label ⟨some submission⟩ (if seen then {(alice, 0)} else ∅)
  let waited := recorded quiet .wait quiet.application
  let ticked := clocked waited
  obtain ⟨firstTrace⟩ := LateOpeningRuntimeAliceFirstWitness.firstLateDecision_trace
    weight nonnegative bit label
  obtain ⟨sentTrace⟩ := rawMenu.trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 22 (firstLateDecision bit label)
      alice ⟨some submission⟩ firstTrace available
  have firstSample : observed ∈ (first.environmentStep app (.activate bob)).support := by
    have foreign : foreignPending bob first.network.pending = {(alice, 0)} := by
      rfl
    rw [ReactiveApplication.Execution.activation_samples]
    change observed ∈ ((leaks bob first.network.pending).map
      (first.sampledActivation app bob)).support
    rw [leaks_singleton bob _ (alice, 0) foreign, mix_map, PMF.pure_map, PMF.pure_map]
    cases seen
    · exact mem_support_mix_right (1 / 2) (by norm_num) (by norm_num) (by norm_num)
        (by simp only [PMF.mem_support_pure_iff]; rfl)
    · exact mem_support_mix_left (1 / 2) (by norm_num) (by norm_num) (by norm_num)
        (by simp only [PMF.mem_support_pure_iff]; rfl)
  obtain ⟨observedTrace⟩ := rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 21 first observed (.activate bob)
      sentTrace (by change _ ∈ (PMF.pure _).support; simp) firstSample
  obtain ⟨quietTrace⟩ := rawMenu.trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 21 observed bob ⟨none⟩ observedTrace
      (bounds.silent_available LateOpeningRuntimeService.runtime leaks bob _ _)
  have waitSelected : (.wait : app.Command) ∈ (LateOpeningRuntimeService.scheduler
      weight nonnegative quiet.environmentRecall (quiet.observeEnvironment app)).support := by
    change .wait ∈ (PMF.pure (latestAuthor bob _)).support
    have latest : latestAuthor bob (quiet.observeEnvironment app) = .wait := rfl
    rw [latest]
    simp
  obtain ⟨waitTrace⟩ := rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 20 quiet waited .wait quietTrace
      waitSelected (by rw [recorded_wait]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  obtain ⟨tickTrace⟩ := rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 19 waited ticked
      (.application .advanceClock) waitTrace
      (by change _ ∈ (PMF.pure _).support; simp)
      (by rw [recorded_clock]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  apply rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 18 ticked
      (finalDecision bit label ⟨some submission⟩ (if seen then {(alice, 0)} else ∅))
      (.activate alice) tickTrace
  · change _ ∈ (PMF.pure _).support
    simp
  · rw [recorded_activation ticked alice (by rfl)]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

variable (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
  (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label) submission)

def decisionHistory : LateOpeningRuntimeAliceDecision.DecisionHistory weight nonnegative where
  execution := finalDecision bit label ⟨some submission⟩ (if seen then {(alice, 0)} else ∅)
  trace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
      (final_decision_trace weight nonnegative bit label submission available seen).some
  bit := bit
  inputs := by
    have packets := genuine_first_pending weight nonnegative bit label submission genuine
      (if seen then {(alice, 0)} else ∅)
    exact packets
  pending := genuine_first_pending weight nonnegative bit label submission genuine
    (if seen then {(alice, 0)} else ∅)
  receipts := rfl
  ledger := rfl
  ready := by
    rw [genuine_first_physical weight nonnegative bit label submission genuine]
    change aliceEvent ∉ (∅ : Finset nativeGraph.EventId) ∧
      nativeGraph.order.predecessors aliceEvent ⊆ ∅
    decide
  timely := by
    rw [genuine_first_physical weight nonnegative bit label submission genuine]
    change 2 - 0 < 3
    decide
  bound := by rw [genuine_first_physical weight nonnegative bit label submission genuine]; rfl
  associated := by
    rw [genuine_first_physical weight nonnegative bit label submission genuine]
    rfl
  fixed := by rw [genuine_first_physical weight nonnegative bit label submission genuine]; rfl

/-- This native information class remembers the exact original raw
submission, including its private syntax. -/
theorem pending_information_representative :
    ∃ (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
      (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
        alice site.1),
      history.1.state = some ⟨18, some alice,
        (decisionHistory weight nonnegative bit label submission available seen
          genuine).execution⟩ := by
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨18, some alice,
      finalDecision bit label ⟨some submission⟩ (if seen then {(alice, 0)} else ∅)⟩,
        (final_decision_trace weight nonnegative bit label submission available seen).some⟩
  obtain ⟨site, information⟩ :=
    (LateOpeningRuntimeNash.model weight nonnegative).exists_informationSite_of_active
      alice history (by change ¬ (18 = 0 ∧ some alice = none); simp) rfl
  exact ⟨site, ⟨history, information.symm⟩, rfl⟩

include available genuine in
/-- The checked uniform native retry bound applies to the exact physical
continuation of every admitted genuine private first-submission alias. -/
theorem genuine_alias_response_close_quiet
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (error : ℝ)
    (bound : ∀ actual : LateOpeningRuntimeAliceTremble.PendingOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceTremble.emissionProbability
        weight nonnegative profile actual.1 ≤ error) :
    PMF.WithinTV error
      (finalResponseLaw weight nonnegative bit label ⟨some submission⟩
        (if seen then {(alice, 0)} else ∅)
          (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative) profile))
      (settlementKernel weight nonnegative
        ((finalDecision bit label ⟨some submission⟩
          (if seen then {(alice, 0)} else ∅)).respond app alice ⟨none⟩)) := by
  obtain ⟨site, history, current⟩ := pending_information_representative weight nonnegative
    bit label submission available seen genuine
  let decision := decisionHistory weight nonnegative bit label submission available seen genuine
  have close := LateOpeningRuntimeRetryKernel.response_close_quiet weight nonnegative site
    history decision current profile
  exact close.mono (bound ⟨site, decision, history, current⟩)

end Vegas.Examples.LateOpeningRuntimeRetryWitness
