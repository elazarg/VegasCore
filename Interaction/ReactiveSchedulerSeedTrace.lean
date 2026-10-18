/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSchedulerSeedSupport
import Interaction.ReactiveAnchoredTrace
import Interaction.ReactiveRawRoundTrace

/-! # Original scheduler seeds realizing whole legal raw histories -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal Seed : Type} [DecidableEq Principal]
  (app : ReactiveApplication Principal)

/-- Every legal raw history of an initialized behavioral scheduler mixture
is the same physical control under one original supported seed. This also
retains an active decision before its response, not only idle round boundaries. -/
theorem schedulerMixture_trace_fixed_seed (prior : PMF Seed)
    (family : Seed → app.Scheduler) (state : app.State) (horizon : Nat)
    (current : app.Control)
    (trace : (app.protocol (PMF.pure state) horizon
      (app.schedulerMixture prior family).scheduler).Trace (some current)) :
    ∃ seed ∈ prior.support,
      Nonempty ((app.protocol (PMF.pure state) horizon (family seed)).Trace (some current)) := by
  rcases current with ⟨remaining, active, execution⟩
  let fallback : Principal → app.Policy := fun _ => app.silentPolicy
  let players := app.anchoredPolicy execution fallback
  have actual := anchored_of_trace (PMF.pure state) horizon
    (app.schedulerMixture prior family).scheduler execution fallback trace
      ⟨remaining, active, execution⟩ rfl (fun _ => List.prefix_refl _)
  obtain ⟨seed, posterior⟩ :=
    ((app.schedulerMixture prior family).posterior execution.environmentRecall).support_nonempty
  cases active with
  | none =>
      have bounded := actual.1
      change remaining ≤ horizon at bounded
      have reached : execution ∈ (app.runRounds (app.schedulerMixture prior family).scheduler
          players (horizon - remaining) (Execution.initial app state)).support := by
        simpa only [roundsFrom, PMF.pure_bind] using actual.2
      have fixed := app.schedulerMixture_run_of_posterior_support prior family players
        (horizon - remaining) state execution seed reached posterior
      refine ⟨seed, fixed.1, ?_⟩
      have rounds : execution ∈
          (app.roundsFrom (PMF.pure state) (family seed) players
            (horizon - remaining)).support := by
        simpa only [roundsFrom, PMF.pure_bind] using fixed.2
      obtain ⟨fixedTrace⟩ := app.raw_trace_roundsFrom (PMF.pure state) horizon (family seed)
        players (horizon - remaining) (by omega) execution rounds
      have distance : horizon - (horizon - remaining) = remaining := by omega
      rw [distance] at fixedTrace
      exact ⟨fixedTrace⟩
  | some owner =>
      obtain ⟨bounded, strict, before, beforeSupport, command, selected, actor, moved⟩ := actual
      change remaining ≤ horizon at bounded
      change remaining < horizon at strict
      have reached : before ∈ (app.runRounds (app.schedulerMixture prior family).scheduler
          players (horizon - remaining - 1) (Execution.initial app state)).support := by
        simpa only [roundsFrom, PMF.pure_bind] using beforeSupport
      obtain ⟨supported, original, originalSupport, originalSelected, originalMoved⟩ :=
        app.schedulerMixture_decision_of_posterior_support prior family players
          (horizon - remaining - 1) state before execution command seed reached selected
            moved posterior
      refine ⟨seed, supported, ?_⟩
      have rounds : original ∈ (app.roundsFrom (PMF.pure state) (family seed) players
          (horizon - remaining - 1)).support := by
        simpa only [roundsFrom, PMF.pure_bind] using originalSupport
      obtain ⟨beforeTrace⟩ := app.raw_trace_roundsFrom (PMF.pure state) horizon (family seed)
        players (horizon - remaining - 1) (by omega) original rounds
      have distance : horizon - (horizon - remaining - 1) = remaining + 1 := by omega
      rw [distance] at beforeTrace
      obtain ⟨fixedTrace⟩ := app.raw_trace_environment (PMF.pure state) horizon (family seed)
        remaining original execution command beforeTrace originalSelected originalMoved
      rw [actor] at fixedTrace
      exact ⟨fixedTrace⟩

end Interaction.ReactiveApplication
