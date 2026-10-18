/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastAllGoodAdmission
import Vegas.Examples.CommitSeedBroadcastProperTimingValue

/-! # Original admission of the whole initialized proper clock-two policy -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- A genuine terminal counted history whose focal word follows the proper
clock-two policy admits that owner's good original seed. Foreign recorded
responses and policies are unrestricted. -/
theorem proper_clock_two_consistent_good_original_admission
    (seed : Seeds) (owner : Player) (good : seed.2 owner = true)
    (final : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0, none, final⟩))
    (consistent : (scheduledProperPolicy 2 owner).Consistent (final.recall owner)) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final := by
  classical
  have horizonAccount := app.raw_trace_horizon initial horizon (family seed)
    (countedMenu.toRawTrace initial horizon (family seed) trace)
  have length : final.environmentRecall.length = horizon := by simpa using horizonAccount
  have actual := (countedMenu.roundSupported_uniform initial horizon (family seed) trace).2
  change final ∈ (app.roundsFrom initial (family seed) countedMenu.uniformResponses
    final.environmentRecall.length).support at actual
  rw [length] at actual
  have reached : final ∈ (app.runRounds (family seed) countedMenu.uniformResponses horizon
      initialExecution).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
      using actual
  have covered : ∀ who past view action,
      action ∈ (countedMenu.uniformResponses who past view).support →
        action ∈ countedMenu.actions who past view := by
    intro who past view action supported
    exact (countedMenu.uniformResponses_support who past view action).mp supported
  have transmits : FirstLateOwnerTransmits seed final owner := by
    intro remaining execution trace request clock _empty first word _firstRequest silent _zero
      entry recorded viewed
    obtain ⟨after, decomposition⟩ := recorded
    have faithful := consistent
    rw [decomposition, ← List.singleton_append, ← List.append_assoc] at faithful
    have chosen := ((scheduledProperPolicy 2 owner).consistent_snoc_iff
      (execution.recall owner) entry).mp (ReactiveApplication.Policy.Consistent.of_append faithful)
    have supported : entry.action ∈ (scheduledProperPolicy 2 owner
        (execution.recall owner) (execution.observe app owner)).support := by
      simpa only [viewed] using chosen.2
    have outputs := silent_own_outputs_of_history (family seed)
      ⟨remaining, some owner, execution⟩
      (countedMenu.toRawTrace initial horizon (family seed) trace) owner (by
        intro previous member
        rw [word, List.mem_singleton] at member
        exact member ▸ silent)
    obtain ⟨serial, _bounded, literal, _slot, _fresh, _result⟩ := proper_original_clock_response
      (family seed) remaining execution owner
        (countedInRaw.trace initial horizon (family seed) trace) request 2 clock
        (by rw [outputs]; exact fun _ member => (List.not_mem_nil member).elim)
    rw [scheduledProperPolicy, ite_eq_right (fun enabled => by
      have zero : execution.application.current.native.clock = 0 := enabled.2.1
      omega), literal, PMF.mem_support_pure_iff] at supported
    rw [supported]
    exact Option.some_ne_none _
  exact good_original_admission seed owner good countedMenu.uniformResponses covered final
    transmits reached (original_bindings_resolved seed ⟨0, none, final⟩
      (countedMenu.toRawTrace initial horizon (family seed) trace) (by rw [length]; decide))

/-- On every good own seed, the whole initialized proper policy obtains
original admission against arbitrary counted foreign strategies. This derives
the eligible response from actual policy consistency at its literal input. -/
theorem initialized_proper_clock_two_good_original_admission
    (seed : Seeds) (owner : Player) (good : seed.2 owner = true)
    (players : Player → app.Policy) (selected : players owner = scheduledProperPolicy 2 owner)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players horizon initialExecution).support) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final := by
  have consistency := (app.consistentRecall_policyInvariant players).runRounds (family seed)
    horizon initialExecution final (fun _ => .nil) reached
  obtain ⟨trace⟩ := countedMenu.trace_roundsFrom initial horizon (family seed) players covered
    horizon le_rfl final (by
      simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
        using reached)
  simp only [Nat.sub_self] at trace
  exact proper_clock_two_consistent_good_original_admission seed owner good final trace
    (by simpa only [selected] using consistency owner)

end Vegas.Examples.CommitSeedBroadcast
