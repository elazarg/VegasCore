/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastAudit
import Vegas.Examples.CommitSeedBroadcastInitialQuiet
import Interaction.ReactiveSchedulerBeforeResponse
import Interaction.ReactiveRoundTrace

/-! # A supported original family decision is a genuine installed-scheduler decision -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open EventGraphRuntime Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

/-- The full physical control is retained. The construction uses the original
joint seed realization before the response, including its command likelihood. -/
theorem counted_fixed_decision_mixed (seed : Seeds) (supportedSeed : seed ∈ nativeSeedLaw.support)
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩)) :
    Nonempty (countedProtocol.Trace (some ⟨remaining, some owner, execution⟩)) := by
  classical
  obtain ⟨budget, count, before, command, position, prior, selected, actor, moved⟩ :=
    countedMenu.roundSupported_uniform initial horizon (family seed) trace
  have initialized : before ∈ (app.runRounds (family seed) countedMenu.uniformResponses count
      initialExecution).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
      using prior
  have joint := app.schedulerMixture_beforeResponse_joint nativeSeedLaw family
    countedMenu.uniformResponses count initialState
  have paired : (command, execution, seed) ∈ (nativeSeedLaw.bind fun chosen =>
      (app.runRounds (family chosen) countedMenu.uniformResponses count initialExecution).bind
        fun current => (family chosen current.environmentRecall
          (current.observeEnvironment app)).bind fun selectedCommand =>
            (current.environmentStep app selectedCommand).map
              fun next => (selectedCommand, next, chosen)).support := by
    rw [PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨seed, supportedSeed, ?_⟩
    rw [PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨before, initialized, ?_⟩
    rw [PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨command, selected, ?_⟩
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨execution, moved, rfl⟩
  change (nativeSeedLaw.bind fun chosen =>
    (app.runRounds (family chosen) countedMenu.uniformResponses count initialExecution).bind
      fun current => (family chosen current.environmentRecall
        (current.observeEnvironment app)).bind fun selectedCommand =>
          (current.environmentStep app selectedCommand).map
            fun next => (selectedCommand, next, chosen)) =
    (app.runRounds scheduler countedMenu.uniformResponses count initialExecution).bind
      (fun current => (scheduler current.environmentRecall
        (current.observeEnvironment app)).bind fun selectedCommand =>
          (current.environmentStep app selectedCommand).bind fun next =>
            (implementation.posterior next.environmentRecall).map
              fun chosen => (selectedCommand, next, chosen)) at joint
  rw [joint, PMF.support_bind] at paired
  obtain ⟨actual, actualReached, selectedPair⟩ := Set.mem_iUnion₂.mp paired
  obtain ⟨actualCommand, actualSelected, observedPair⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ selectedPair)
  obtain ⟨observed, actualMoved, tagged⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ observedPair)
  obtain ⟨chosen, _posterior, same⟩ := PMF.support_map .. ▸ tagged
  have commandEq : actualCommand = command := congrArg Prod.fst same
  have observedEq : observed = execution := congrArg (fun output => output.2.1) same
  subst actualCommand
  subst observed
  have supported : actual ∈ (app.roundsFrom initial scheduler countedMenu.uniformResponses
      count).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
      using actualReached
  obtain ⟨priorTrace⟩ := countedMenu.trace_roundsFrom initial horizon scheduler
    countedMenu.uniformResponses (fun who past view response chosen =>
      (countedMenu.uniformResponses_support who past view response).mp chosen)
      count (by omega) actual supported
  have enough : horizon - count = remaining + 1 := by
    change execution.environmentRecall.length + remaining = horizon at budget
    change execution.environmentRecall.length = count + 1 at position
    omega
  rw [enough] at priorTrace
  obtain ⟨result⟩ := countedMenu.trace_environment initial horizon scheduler remaining actual
    execution command priorTrace actualSelected actualMoved
  rw [actor] at result
  exact ⟨result⟩

end Vegas.Examples.CommitSeedBroadcast
