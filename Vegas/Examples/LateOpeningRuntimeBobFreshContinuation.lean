/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobFreshBinding

/-! # Accepted publication after an arbitrary receiver prefix

The physical continuation publishes the selected answer after a fresh binding.
Earlier traffic is retained exactly; audit conclusions are separate because
accepted fallback commitments need not be canonical settled content.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobFreshContinuation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeBobService LateOpeningRuntimeBobAudit LateOpeningRuntimeBobBindingService
  LateOpeningRuntimeBobSafeContinuation LateOpeningRuntimeUtility
  LateOpeningRuntimeBobFreshBinding

theorem answer_opening_after_arbitrary_prefix (weight : ℝ)
    (nonnegative : 0 ≤ weight) (answer : Answer)
    (players : Player → app.Policy) (bobPolicy : players bob = answerPolicy answer)
    (execution next : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨13, none, execution⟩))
    (bound : execution.application.config.store (.inr bobBindEvent) = some (.success answer))
    (ready : execution.application.config.cut.Ready bobRevealEvent)
    (timer : execution.application.activatedAt bobRevealEvent = some 3)
    (clock : execution.application.clock = 3)
    (reached : next ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 2 execution).support) :
    ∃ origin candidate,
      Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
          (some ⟨11, none, next⟩)) ∧
        next.application.config.store (.inr bobRevealEvent) = some (.success answer) ∧
          ((openingMessage origin candidate answer).id, true) ∈ next.receipts ∧
            next.network.inputs = execution.network.inputs ++
              [(show Message Player app.Payload from openingMessage origin candidate answer)] := by
  obtain ⟨first, moved, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  simp only [ReactiveApplication.runRounds, PMF.bind_pure] at continued
  obtain ⟨command, selected, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
  have position : execution.environmentRecall.length = 13 := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) trace
    change execution.environmentRecall.length + 13 = 26 at counted
    omega
  have done : bobBindEvent ∈ execution.application.publicView.observation.completionOrder :=
    (execution.application.config.history_exact bobBindEvent).mpr (ready.2 (by decide))
  change command ∈ (stageChoice weight nonnegative execution.environmentRecall.length _).support
    at selected
  rw [position] at selected
  change command ∈ (PMF.pure (if bobBindEvent ∈
    execution.application.publicView.observation.completionOrder
      then (.activate bob : app.Command) else .wait)).support at selected
  rw [ite_eq_left done, PMF.mem_support_pure_iff] at selected
  subst command
  obtain ⟨observed, sampled, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  obtain ⟨⟨observedTrace⟩, physical, oldInputs, observedReady, observedTimely, observedClock⟩ :=
    optional_activation weight nonnegative execution observed trace ready clock timer sampled
  have observedBound : observed.application.config.store (.inr bobBindEvent) =
      some (.success answer) := physical ▸ bound
  obtain ⟨candidate, material, served, decision, emitted, law, published, accepted⟩ :=
    canonical_round weight nonnegative players 12 observed observedTrace answer observedBound
      observedReady observedTimely
  change first ∈ ((players bob (observed.recall bob) (observed.observe app bob)).map
    (observed.respond app bob)).support at resumed
  rw [bobPolicy, answerPolicy_opening answer observed observedReady observedClock, decision,
    PMF.pure_map, PMF.mem_support_pure_iff] at resumed
  subst first
  rw [law, PMF.mem_support_pure_iff] at continued
  subst next
  have servedReached : served ∈ (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players (observed.respond app bob ⟨some material⟩)).support := by
    rw [law]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 12 observed bob ⟨some material⟩
      observedTrace
  obtain ⟨servedTrace⟩ := app.raw_trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 11 _ served
      respondedTrace servedReached
  have inputs : served.network.inputs = execution.network.inputs ++
      [(show Message Player app.Payload from openingMessage observed candidate answer)] := by
    rw [protected_round_inputs weight nonnegative 12 observed observedTrace
      ⟨some material⟩ players served servedReached]
    change observed.network.inputs ++ [⟨(bob, observed.network.nextSerial bob),
      app.packet (app.submit observed.application bob material) bob
        (observed.network.known bob) material⟩] = _
    rw [emitted, oldInputs]
    rfl
  exact ⟨observed, candidate, ⟨servedTrace⟩, published, accepted, inputs⟩

/-- A selected answer is published despite arbitrary earlier receiver traffic. -/
theorem answer_fresh_continuation_publishes (weight : ℝ)
    (nonnegative : 0 ≤ weight) (answer : Answer)
    (players : Player → app.Policy) (bobPolicy : players bob = answerPolicy answer)
    (execution final : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (serial : Nat)
    (fresh : execution.application.candidates.lookup (bob, .prepared serial) = .fresh)
    (ready : execution.application.config.cut.Ready bobBindEvent)
    (timely : execution.application.WithinDeadline LateOpeningRuntimeService.runtime bobBindEvent)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14
        (execution.respond app bob (response serial answer))).support) :
    final.application.config.store (.inr bobRevealEvent) = some (.success answer) := by
  have whole := reached
  obtain ⟨bound, binding, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨served, law, boundValue, _, revealReady, timer, _⟩ := fresh_binding_round weight
    nonnegative 14 execution trace serial fresh ready timely answer
  rw [law players, PMF.mem_support_pure_iff] at binding
  subst bound
  obtain ⟨respondedTrace⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 execution bob
      (response serial answer) trace
  obtain ⟨boundTrace⟩ := app.raw_trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 13 _ served respondedTrace
      (by rw [law players]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have cursor : execution.environmentRecall.length = 12 := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) trace
    change execution.environmentRecall.length + 14 = 26 at counted
    omega
  have clock : execution.application.clock = 3 := by
    rw [clock_history weight nonnegative ⟨14, some bob, execution⟩ trace, cursor]
    decide
  rw [clock] at timer
  have boundClock : served.application.clock = 3 := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) boundTrace
    change served.environmentRecall.length + 13 = 26 at counted
    have position : served.environmentRecall.length = 13 := by omega
    rw [clock_history weight nonnegative ⟨13, none, served⟩ boundTrace, position]
    decide
  rw [app.runRounds_add (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 2 11] at rest
  obtain ⟨opened, opening, suffix⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ rest)
  obtain ⟨origin, candidate, ⟨openedTrace⟩, published, accepted, only⟩ :=
    answer_opening_after_arbitrary_prefix weight nonnegative answer players bobPolicy
      served opened boundTrace
      boundValue revealReady timer boundClock opening
  have late : 15 ≤ opened.environmentRecall.length := by
    have counted := app.raw_trace_horizon initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) openedTrace
    change opened.environmentRecall.length + 11 = 26 at counted
    omega
  have inputs := after_opening_inputs weight nonnegative answer players bobPolicy 11 0 opened final
    openedTrace late suffix
  have finalPublished := (ReactiveApplication.Invariant.policyInvariant app
    (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr bobRevealEvent)
      (.success answer)) players).runRounds
        (LateOpeningRuntimeService.scheduler weight nonnegative) 11 opened final published suffix
  exact finalPublished

end Vegas.Examples.LateOpeningRuntimeBobFreshContinuation
