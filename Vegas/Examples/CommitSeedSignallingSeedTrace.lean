/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingRuntime
import Interaction.ReactiveAnchoredTrace
import Interaction.ReactiveRawRoundTrace

/-! # Original supported scheduler seeds on every legal raw history -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- Every legal mixed-scheduler history, with arbitrary unbounded raw actions,
is the same physical control under an original supported scheduler seed.
The anchored response policy only witnesses this already recorded history. -/
theorem raw_trace_fixed_seed (current : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some current)) :
    ∃ seeds ∈ seedPrior.support,
      Nonempty ((app.protocol initial horizon (family seeds)).Trace (some current)) := by
  rcases current with ⟨remaining, active, execution⟩
  let fallback : Player → app.Policy := fun _ => app.silentPolicy
  let players := ReactiveApplication.anchoredPolicy execution fallback
  have actual := ReactiveApplication.anchored_of_trace initial horizon scheduler execution
    fallback trace ⟨remaining, active, execution⟩ rfl (fun _ => List.prefix_refl _)
  obtain ⟨seeds, posterior⟩ :=
    (implementation.posterior execution.environmentRecall).support_nonempty
  cases active with
  | none =>
      have bounded := actual.1
      change remaining ≤ horizon at bounded
      have reached : execution ∈ (app.runRounds scheduler players (horizon - remaining)
          initialExecution).support := by
        simpa only [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind,
          initialExecution] using actual.2
      have fixed := app.schedulerMixture_run_of_posterior_support seedPrior family players
        (horizon - remaining) initialState execution seeds reached posterior
      refine ⟨seeds, fixed.1, ?_⟩
      have rounds : execution ∈
          (app.roundsFrom initial (family seeds) players (horizon - remaining)).support := by
        simpa only [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind,
          initialExecution] using fixed.2
      obtain ⟨fixedTrace⟩ := app.raw_trace_roundsFrom initial horizon (family seeds) players
        (horizon - remaining) (by omega) execution rounds
      have distance : horizon - (horizon - remaining) = remaining := by omega
      rw [distance] at fixedTrace
      exact ⟨fixedTrace⟩
  | some owner =>
      obtain ⟨bounded, strict, before, beforeSupport, command, selected, actor, moved⟩ := actual
      change remaining ≤ horizon at bounded
      change remaining < horizon at strict
      have reached : before ∈
          (app.runRounds scheduler players (horizon - remaining - 1) initialExecution).support := by
        simpa only [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind,
          initialExecution] using beforeSupport
      obtain ⟨supported, original, originalSupport, originalSelected, originalMoved⟩ :=
        app.schedulerMixture_decision_of_posterior_support seedPrior family players
          (horizon - remaining - 1) initialState before execution command seeds reached selected
          moved posterior
      refine ⟨seeds, supported, ?_⟩
      have rounds : original ∈
          (app.roundsFrom initial (family seeds) players (horizon - remaining - 1)).support := by
        simpa only [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind,
          initialExecution] using originalSupport
      obtain ⟨beforeTrace⟩ := app.raw_trace_roundsFrom initial horizon (family seeds) players
        (horizon - remaining - 1) (by omega) original rounds
      have distance : horizon - (horizon - remaining - 1) = remaining + 1 := by omega
      rw [distance] at beforeTrace
      obtain ⟨fixedTrace⟩ := app.raw_trace_environment initial horizon (family seeds) remaining
        original execution command beforeTrace originalSelected originalMoved
      rw [actor] at fixedTrace
      exact ⟨fixedTrace⟩

end Vegas.Examples.CommitSeedSignalling
