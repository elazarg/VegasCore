/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialResponses
import Interaction.ReactiveAnchoredTrace
import Interaction.ReactiveResponseAccounting
import Interaction.ReactivePolicyInvariant

/-! # Literal initial response prefixes retained by actual native late inputs -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem run_initial_response_prefix (seed : Seeds) (players : Player → app.Policy)
    (count : Nat) (execution : app.Execution) (late : 4 ≤ count)
    (reached : execution ∈ (app.runRounds (family seed) players count initialExecution).support) :
    ∃ first second third : app.Action, ∃ snapshot : app.EnvironmentEntry,
      execution.environmentRecall[3]? = some snapshot ∧
      snapshot.beforeView.network.inputs =
        (afterInitialResponses first second third).network.inputs ∧
      ∀ owner, (afterInitialResponses first second third).recall owner <+:
        execution.recall owner := by
  rw [show count = 3 + (count - 3) by omega, app.runRounds_add,
    first_three_rounds, PMF.bind_bind] at reached
  obtain ⟨first, _first, afterFirst⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  rw [PMF.bind_bind] at afterFirst
  obtain ⟨second, _second, afterSecond⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterFirst)
  rw [PMF.bind_map] at afterSecond
  obtain ⟨third, _third, afterThird⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterSecond)
  change execution ∈ (app.runRounds (family seed) players (count - 3)
    (afterInitialResponses first second third)).support at afterThird
  have future := afterThird
  rw [show count - 3 = (count - 4) + 1 by omega,
    ReactiveApplication.runRounds.eq_def] at afterThird
  obtain ⟨middle, moved, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterThird)
  obtain ⟨command, _selected, dispatched⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
  obtain ⟨later, recalled, _length⟩ :=
    app.runRounds_environmentRecall_append (family seed) players (count - 4) middle execution tail
  let snapshot : app.EnvironmentEntry :=
    ⟨(afterInitialResponses first second third).observeEnvironment app, command⟩
  have complete : execution.environmentRecall =
      (afterInitialResponses first second third).environmentRecall ++ [snapshot] ++ later := by
    rw [recalled, app.dispatch_environmentRecall players command _ middle dispatched]
  have found : execution.environmentRecall[3]? = some snapshot := by
    rw [complete]
    rfl
  let valid : app.Execution → Prop := fun current =>
    ∀ owner, (afterInitialResponses first second third).recall owner <+: current.recall owner
  have invariant : app.ServiceInvariant (family seed) valid := by
    constructor
    · intro before actor action previous owner
      exact (previous owner).trans (app.respond_recall_prefix before actor owner action)
    · intro before after selected previous _chosen stepped owner
      rw [app.environmentStep_recall before after selected stepped]
      exact previous owner
  refine ⟨first, second, third, snapshot, found, rfl, ?_⟩
  exact invariant.runRounds players (count - 3) (afterInitialResponses first second third)
    execution (fun _ => List.prefix_refl _) future

/-- Every actual late decision retains the three original raw responses and
their exact public initial snapshot, including all hidden preparation aliases.
This consumes the initialized native kernel, not an asserted prefix witness. -/
theorem original_initial_response_prefix (seed : Seeds) (remaining : Nat)
    (execution : app.Execution) (owner : Player)
    (trace : (app.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (late : 5 ≤ execution.environmentRecall.length) :
    ∃ first second third : app.Action, ∃ snapshot : app.EnvironmentEntry,
      execution.environmentRecall[3]? = some snapshot ∧
      snapshot.beforeView.network.inputs =
        (afterInitialResponses first second third).network.inputs ∧
      ∀ observer, (afterInitialResponses first second third).recall observer <+:
        execution.recall observer := by
  let fallback : Player → app.Policy := fun _ => app.silentPolicy
  let players := ReactiveApplication.anchoredPolicy execution fallback
  have actual := ReactiveApplication.anchored_of_trace initial horizon (family seed) execution
    fallback trace ⟨remaining, some owner, execution⟩ rfl (fun _ => List.prefix_refl _)
  obtain ⟨_bounded, _strict, before, beforeReached, command, _selected, _actor, moved⟩ := actual
  have initialized : before ∈ (app.runRounds (family seed) players
      (horizon - remaining - 1) initialExecution).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
      using beforeReached
  have appended := app.environmentStep_environmentRecall before execution command moved
  have previousLength : 4 ≤ before.environmentRecall.length := by
    have lengths := congrArg List.length appended
    simp only [List.length_append, List.length_singleton] at lengths
    omega
  have countLength := app.runRounds_environmentRecall_length (family seed) players
    (horizon - remaining - 1) initialExecution before initialized
  change before.environmentRecall.length = 0 + (horizon - remaining - 1) at countLength
  obtain ⟨first, second, third, snapshot, found, inputs, records⟩ :=
    run_initial_response_prefix seed players (horizon - remaining - 1) before
      (by omega) initialized
  refine ⟨first, second, third, snapshot, ?_, inputs, ?_⟩
  · rw [appended, List.getElem?_append_left (by omega : 3 < before.environmentRecall.length)]
    exact found
  · intro observer
    rw [app.environmentStep_recall before execution command moved]
    exact records observer

end Vegas.Examples.CommitSeedBroadcast
