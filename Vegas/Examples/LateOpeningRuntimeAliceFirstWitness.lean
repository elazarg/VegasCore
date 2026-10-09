/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceFirstDecision

/-! # Initialized first late Alice information classes

Every initial bit and private label reaches an actual bounded first late
callback after protected silence. No Bob action or discretionary inclusion
has yet occurred.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceFirstWitness

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeLatePrefix

theorem firstLateDecision_trace (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨22, some alice, firstLateDecision bit label⟩)) := by
  let e0 := initialExecution bit label
  let activated := recorded e0 (.activate alice) e0.application
  let silent := activated.respond app alice ⟨none⟩
  let waited := recorded silent .wait silent.application
  let ticked := recorded waited (.application .advanceClock)
    { waited.application with clock := waited.application.clock + 1 }
  have first : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit 1) e0 = PMF.pure silent := by
    rw [fixed_round weight nonnegative (latePlayers bit 1) e0 activated 0 (.activate alice)
      rfl rfl (recorded_activation e0 alice (by rfl))]
    change (PMF.pure (⟨none⟩ : app.Action)).map (activated.respond app alice) = _
    exact PMF.pure_map _ _
  have second : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit 1) silent = PMF.pure waited := by
    rw [fixed_round weight nonnegative (latePlayers bit 1) silent waited 1 .wait
      rfl rfl (recorded_wait silent)]
    rfl
  have third : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit 1) waited = PMF.pure ticked := by
    rw [fixed_round weight nonnegative (latePlayers bit 1) waited ticked 2
      (.application .advanceClock) rfl rfl (recorded_clock waited)]
    rfl
  have prefixLaw : app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit 1) 3 e0 = PMF.pure ticked := by
    rw [ReactiveApplication.runRounds, first, PMF.pure_bind,
      ReactiveApplication.runRounds, second, PMF.pure_bind,
      ReactiveApplication.runRounds, third, PMF.pure_bind,
      ReactiveApplication.runRounds]
  obtain ⟨initialTrace⟩ := rawMenu.trace_initial initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (initialPhysical bit label)
      (initialPhysical_supported bit label)
  obtain ⟨before⟩ := rawMenu.trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit 1)
      (latePlayers_covered bit 1) 23 3 e0 ticked initialTrace
        (by rw [prefixLaw]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  apply rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 22 ticked
      (firstLateDecision bit label) (.activate alice) before
  · change (.activate alice : app.Command) ∈ (PMF.pure (.activate alice)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [recorded_activation ticked alice (by rfl)]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

/-- An actual initialized history realizes the full first late interface. -/
def decisionHistory (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) :
    LateOpeningRuntimeAliceFirstDecision.DecisionHistory weight nonnegative where
  execution := firstLateDecision bit label
  trace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
      (firstLateDecision_trace weight nonnegative bit label).some
  bit := bit
  quiet := rfl
  pending := rfl
  ready := by
    change aliceEvent ∉ (∅ : Finset nativeGraph.EventId) ∧
      nativeGraph.order.predecessors aliceEvent ⊆ ∅
    decide
  timely := by change 1 - 0 < 3; decide
  bound := rfl
  associated := rfl
  fixed := rfl

theorem first_alice_class_nonempty (weight : ℝ) (nonnegative : 0 ≤ weight) :
    Nonempty (LateOpeningRuntimeAliceFirstDecision.DecisionHistory weight nonnegative) :=
  ⟨decisionHistory weight nonnegative false 0⟩

end Vegas.Examples.LateOpeningRuntimeAliceFirstWitness
