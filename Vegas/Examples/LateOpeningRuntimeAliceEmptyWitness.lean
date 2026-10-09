/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceEmptyDecision

/-! # Actual empty final Alice callbacks

Each initialized bit and private label reaches a legal last Alice decision
when both earlier Alice responses and the early Bob response are silent.
The whole-fiber opening comparison therefore applies to real histories of
the complete bounded raw game.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceEmptyWitness

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance

theorem secondLateDecision_trace (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨18, some alice, secondLateDecision bit label 1 false⟩)) := by
  obtain ⟨observed⟩ := bobObserved_second_trace weight nonnegative bit label
  let e5 := bobObserved bit label 1 false
  let e6 := recorded e5 .wait e5.application
  let e7 := recorded e6 (.application .advanceClock)
    { e6.application with clock := e6.application.clock + 1 }
  have noBob : latestAuthor bob (e5.observeEnvironment app) = .wait := by
    rfl
  have noForeign : foreignPending alice e7.network.pending = ∅ := by
    rfl
  obtain ⟨waited⟩ := rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 20 e5 e6 .wait observed
      (by change .wait ∈ (PMF.pure (latestAuthor bob _)).support; rw [noBob]; simp)
      (by rw [recorded_wait]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  obtain ⟨ticked⟩ := rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 19 e6 e7
      (.application .advanceClock) waited (by
        change (.application .advanceClock : app.Command) ∈ (stageChoice weight nonnegative
          e6.environmentRecall.length (e6.observeEnvironment app)).support
        have cursor : e6.environmentRecall.length = 6 := rfl
        rw [cursor]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl)
      (by rw [recorded_clock]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  apply rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 18 e7
      (secondLateDecision bit label 1 false) (.activate alice) ticked
  · change (.activate alice : app.Command) ∈ (stageChoice weight nonnegative
      e7.environmentRecall.length (e7.observeEnvironment app)).support
    have cursor : e7.environmentRecall.length = 7 := rfl
    rw [cursor]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [recorded_activation e7 alice noForeign]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

private theorem secondLateDecision_physical (bit : Bool) (label : Fin 3) :
    (secondLateDecision bit label 1 false).application =
      { initialPhysical bit label with clock := 2 } :=
  beforeLottery_physical bit label 1 false

/-- An actual initialized native history realizes the empty-pool interface. -/
def decisionHistory (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) :
    LateOpeningRuntimeAliceEmptyDecision.DecisionHistory weight nonnegative where
  execution := secondLateDecision bit label 1 false
  trace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
      (secondLateDecision_trace weight nonnegative bit label).some
  bit := bit
  quiet := rfl
  pending := rfl
  ready := by
    rw [secondLateDecision_physical]
    change aliceEvent ∉ (∅ : Finset nativeGraph.EventId) ∧
      nativeGraph.order.predecessors aliceEvent ⊆ ∅
    decide
  timely := by
    rw [secondLateDecision_physical]
    change 2 - 0 < 3
    decide
  bound := by rw [secondLateDecision_physical]; rfl
  associated := by rw [secondLateDecision_physical]; rfl
  fixed := by rw [secondLateDecision_physical]; rfl

theorem empty_last_alice_class_nonempty (weight : ℝ) (nonnegative : 0 ≤ weight) :
    Nonempty (LateOpeningRuntimeAliceEmptyDecision.DecisionHistory weight nonnegative) :=
  ⟨decisionHistory weight nonnegative false 0⟩

end Vegas.Examples.LateOpeningRuntimeAliceEmptyWitness
