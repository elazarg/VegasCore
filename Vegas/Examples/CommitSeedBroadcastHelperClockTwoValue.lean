/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperClockThreeCallback
import Vegas.Examples.CommitSeedBroadcastProperClockThree

/-! # The actual proper clock-three continuation from the earlier helper input -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- WAIT at the observed bad clock-two input is followed by the actual eligible
clock-three callback. The native finish law is nonnegative against arbitrary
covered foreign policies, with all old own observations retained. -/
theorem proper_bad_clock_two_finish_value_nonnegative
    (seed : Seeds) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) (bad : seed.2 owner = false)
    (first : app.PlayerEntry) (word : execution.recall owner = [first])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (silent : first.action.transmission = none)
    (zero : first.beforeView.application.2.native.clock = 0)
    (players : Player → app.Policy) (selected : players owner = scheduledProperPolicy 3 owner)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view) :
    0 ≤ expect (app.finish initial horizon (family seed) players
      (some ⟨remaining, some owner, execution⟩)) (fun state => netPayoff state owner) := by
  classical
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have outputs := silent_own_outputs_of_history (family seed) _ raw owner (by
    intro entry member
    rw [word, List.mem_singleton] at member
    subst entry
    exact silent)
  have waited := scheduled_proper_clock_three_wait_at_two (family seed) remaining execution owner
    (countedInRaw.trace initial horizon (family seed) trace) request clock first word firstRequest
  have firstAction : first.action = (⟨none⟩ : app.Action) := by
    have eta : first.action = ⟨first.action.transmission⟩ := by cases first.action; rfl
    exact eta.trans (congrArg ReactiveApplication.Action.mk silent)
  have initialPast : (scheduledProperPolicy 3 owner).Consistent [first] := by
    apply ReactiveApplication.Policy.Consistent.snoc first .nil
    rw [scheduledProperPolicy, ite_eq_left ⟨firstRequest.1.symm, zero, by decide⟩,
      PMF.mem_support_pure_iff]
    exact firstAction
  let post := execution.respond app owner ⟨none⟩
  have postPast : (scheduledProperPolicy 3 owner).Consistent (post.recall owner) := by
    obtain ⟨emitted, recalled⟩ := app.respond_recall_entry execution owner (⟨none⟩ : app.Action)
    rw [recalled, word]
    apply ReactiveApplication.Policy.Consistent.snoc _ initialPast
    rw [← word, waited, PMF.mem_support_pure_iff]
  apply expect_nonneg
  intro state stateReached
  obtain ⟨after, afterReached, equal⟩ := PMF.support_map .. ▸ stateReached
  subst state
  have actual : after ∈ (app.runRounds (family seed) players remaining post).support := by
    change after ∈ ((app.resume players (some owner) execution).bind
      (app.runRounds (family seed) players remaining)).support at afterReached
    rwa [ReactiveApplication.resume, ReactiveApplication.invoke, selected, waited,
      PMF.pure_map, PMF.pure_bind] at afterReached
  have position := bad_firstLate_position seed remaining execution owner trace request clock bad
  have budget := (countedMenu.roundSupported_uniform initial horizon (family seed) trace).1
  change execution.environmentRecall.length + remaining = horizon at budget
  have rankBound := (seed.1.symm owner).isLt
  have enough : 7 ≤ remaining := by dsimp only [horizon] at budget; omega
  have split : remaining = 7 + (remaining - 7) := by omega
  rw [split, app.runRounds_add] at actual
  obtain ⟨middle, firstSeven, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ actual)
  obtain ⟨_enough, before, observed, action, _prior, _observed, _command, ⟨observedTrace⟩,
    observedRequest, observedClock, observedWord, chosen, middleEq⟩ :=
      helper_wait_reaches_clock_three seed remaining execution owner trace request clock bad
        outputs players covered middle firstSeven
  have observedPast : (scheduledProperPolicy 3 owner).Consistent (observed.recall owner) := by
    rw [observedWord]
    exact postPast
  have observedOutputs : app.outputs (observed.recall owner) = [] := by
    rw [observedWord]
    simp only [ReactiveApplication.Execution.respond, ite_true, ReactiveApplication.outputs,
      List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_nil]
    exact outputs
  have fromObserved : app.finished after ∈ (app.finish initial horizon (family seed) players
      (some ⟨remaining - 7, some owner, observed⟩)).support := by
    apply (PMF.mem_support_map_iff _ _ _).mpr
    refine ⟨after, ?_, rfl⟩
    rw [PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨middle, ?_, later⟩
    change middle ∈ ((players owner (observed.recall owner)
      (observed.observe app owner)).map (observed.respond app owner)).support
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨action, chosen, middleEq.symm⟩
  have survives := scheduled_proper_eligible_finish_survives 3 seed (remaining - 7) observed owner
    observedTrace observedRequest observedClock (by rw [bad]; rfl)
      (by rw [observedOutputs]; exact fun _ member => (List.not_mem_nil member).elim)
      players selected covered observedPast after fromObserved
  obtain ⟨finalTrace⟩ := countedMenu.finish_trace initial horizon (family seed) players covered
    (some ⟨remaining, some owner, execution⟩) trace (app.finished after) (by
      apply (PMF.mem_support_map_iff _ _ _).mpr
      exact ⟨after, afterReached, rfl⟩)
  rw [counted_fixed_endpoint_payoff seed after finalTrace owner, ite_eq_right survives.2]
  split <;> norm_num

end Vegas.Examples.CommitSeedBroadcast
