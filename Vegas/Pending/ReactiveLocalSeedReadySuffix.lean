/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveFirstReadyClock
import Vegas.Pending.ReactiveLocalSeedExhaustionRun
import Vegas.Pending.ReactiveLocalSeedOwnerRecall

/-! # Actual local-controller suffixes starting at first readiness

Before its selected event is ready the local controller records no query.
Every supported run ending at a surviving ready event therefore has an actual
suffix starting with empty private local state at relative clock zero.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {LocalSeed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks LocalSeed owner event)

local notation "app" => runtime.reactiveApplication leaks

/-- A supported run reaching a surviving ready event contains an actual
clock-zero ready suffix; no scheduler seed was read before that suffix. -/
theorem runJoint_ready_suffix
    (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (inputs : graph.Inputs) (players : Player → (app).Policy)
    (owned : graph.actor? event = some owner)
    (localSeed : LocalSeed) (remainderSeed : RestSeed)
    (count : Nat) (execution next : (app).Execution)
    (after : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (valid : execution.application.Invariant inputs)
    (freshTimer : ∀ entered, execution.application.activatedAt event = some entered →
      entered = execution.application.clock)
    (positiveEmpty : runtime.ownerActivationQueries leaks event (execution.recall owner) = [])
    (readyAtEnd : ∃ entered, next.application.activatedAt event = some entered)
    (unfinished : event ∉ next.application.config.cut.completed)
    (reached : (next, after) ∈
      ((controller.implementation localLaw remainderLaw remainder).runJoint players count
        execution (initialMemory localSeed remainderSeed)).support) :
    ∃ beforeCount afterCount prior,
      beforeCount + afterCount = count ∧
      (prior, initialMemory localSeed remainderSeed) ∈
        ((controller.implementation localLaw remainderLaw remainder).runJoint players beforeCount
          execution (initialMemory localSeed remainderSeed)).support ∧
      (next, after) ∈
        ((controller.implementation localLaw remainderLaw remainder).runJoint players afterCount
          prior (initialMemory localSeed remainderSeed)).support ∧
      prior.application.activatedAt event = some prior.application.clock ∧
      prior.application.Invariant inputs ∧
      runtime.ownerActivationQueries leaks event (prior.recall owner) = [] := by
  classical
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      obtain ⟨entered, activated⟩ := readyAtEnd
      refine ⟨0, 0, next, rfl, ?_, ?_, ?_, valid, positiveEmpty⟩
      · exact (PMF.mem_support_pure_iff _ _).mpr rfl
      · exact (PMF.mem_support_pure_iff _ _).mpr rfl
      · rw [← freshTimer entered activated]
        exact activated
  | succ count ih =>
      cases activated : execution.application.activatedAt event with
      | some entered =>
          refine ⟨0, count + 1, execution, Nat.zero_add _, ?_, reached, ?_, valid, positiveEmpty⟩
          · exact (PMF.mem_support_pure_iff _ _).mpr rfl
          · rw [← freshTimer entered activated]
            exact activated
      | none =>
          have notReady : ¬ (execution.observeEnvironment app).application.EventReady event := by
            intro ready
            have readyCut := (execution.application.publicView_eventReady event).mp ready
            have present := (valid.activated_iff event).mpr ⟨readyCut, by simp [owned]⟩
            simp only [activated, Option.isSome_none, Bool.false_eq_true] at present
          have memoryEq : (controller.step remainder (initialMemory localSeed remainderSeed)
              execution.environmentRecall (execution.observeEnvironment app)).2 =
                initialMemory localSeed remainderSeed := by
            simp only [step, ite_eq_right notReady]
          rw [controller.runJoint_succ] at reached
          obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          rw [memoryEq] at later
          have first := runtime.reactive_dispatch_progress leaks inputs players execution middle
            _
            valid moved
          obtain ⟨ticks, rest⟩ := controller.runJoint_progress localLaw remainderLaw remainder
            inputs players count middle (initialMemory localSeed remainderSeed) next after
              first.invariant later
          have middleUnfinished : event ∉ middle.application.config.cut.completed :=
            fun completed => unfinished (rest.completed completed)
          have middleFresh : ∀ entered, middle.application.activatedAt event = some entered →
              entered = middle.application.clock := by
            intro entered present
            exact runtime.dispatch_newActivation_clock leaks inputs players execution middle _ event
              entered valid activated present middleUnfinished moved
          have middlePositive : runtime.ownerActivationQueries leaks event
              (middle.recall owner) = [] := by
            rw [runtime.dispatch_ownerActivationQueries leaks players execution middle _ owner
              event moved, positiveEmpty]
            have unavailable : ¬ execution.application.publicView.EventReady event := notReady
            simp only [unavailable, and_false, ↓reduceIte, List.append_nil]
          obtain ⟨beforeCount, afterCount, prior, total, earlier, suffix, origin, invariant,
            empty⟩ :=
            ih middle first.invariant middleFresh middlePositive later
          refine ⟨beforeCount + 1, afterCount, prior, ?_, ?_, suffix, origin, invariant, empty⟩
          · omega
          · rw [controller.runJoint_succ]
            rw [PMF.support_bind]
            exact Set.mem_iUnion₂.mpr ⟨middle, moved, by simpa only [memoryEq] using earlier⟩

end Vegas.EventGraphRuntime.LocalSeedController
