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
theorem schedulerMixture_trace_of_posterior_support (prior : PMF Seed)
    (family : Seed → app.Scheduler) (initial : PMF app.State) (horizon : Nat)
    (current : app.Control)
    (trace : (app.protocol initial horizon
      (app.schedulerMixture prior family).scheduler).Trace (some current))
    (seed : Seed)
    (posterior : seed ∈ ((app.schedulerMixture prior family).posterior
      current.execution.environmentRecall).support) :
    seed ∈ prior.support ∧
      Nonempty ((app.protocol initial horizon (family seed)).Trace (some current)) := by
  rcases current with ⟨remaining, active, execution⟩
  let fallback : Principal → app.Policy := fun _ => app.silentPolicy
  let players := app.anchoredPolicy execution fallback
  have actual := anchored_of_trace initial horizon
    (app.schedulerMixture prior family).scheduler execution fallback trace
      ⟨remaining, active, execution⟩ rfl (fun _ => List.prefix_refl _)
  cases active with
  | none =>
      have bounded := actual.1
      change remaining ≤ horizon at bounded
      obtain ⟨state, stateMem, reached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ actual.2)
      have fixed := app.schedulerMixture_run_of_posterior_support prior family players
        (horizon - remaining) state execution seed reached posterior
      refine ⟨fixed.1, ?_⟩
      have rounds : execution ∈
          (app.roundsFrom initial (family seed) players
            (horizon - remaining)).support := by
        rw [roundsFrom, PMF.support_bind]
        exact Set.mem_iUnion₂.mpr ⟨state, stateMem, fixed.2⟩
      obtain ⟨fixedTrace⟩ := app.raw_trace_roundsFrom initial horizon (family seed)
        players (horizon - remaining) (by omega) execution rounds
      have distance : horizon - (horizon - remaining) = remaining := by omega
      rw [distance] at fixedTrace
      exact ⟨fixedTrace⟩
  | some owner =>
      obtain ⟨bounded, strict, before, beforeSupport, command, selected, actor, moved⟩ := actual
      change remaining ≤ horizon at bounded
      change remaining < horizon at strict
      obtain ⟨state, stateMem, reached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ beforeSupport)
      obtain ⟨supported, original, originalSupport, originalSelected, originalMoved⟩ :=
        app.schedulerMixture_decision_of_posterior_support prior family players
          (horizon - remaining - 1) state before execution command seed reached selected
            moved posterior
      refine ⟨supported, ?_⟩
      have rounds : original ∈ (app.roundsFrom initial (family seed) players
          (horizon - remaining - 1)).support := by
        rw [roundsFrom, PMF.support_bind]
        exact Set.mem_iUnion₂.mpr ⟨state, stateMem, originalSupport⟩
      obtain ⟨beforeTrace⟩ := app.raw_trace_roundsFrom initial horizon (family seed)
        players (horizon - remaining - 1) (by omega) original rounds
      have distance : horizon - (horizon - remaining - 1) = remaining + 1 := by omega
      rw [distance] at beforeTrace
      obtain ⟨fixedTrace⟩ := app.raw_trace_environment initial horizon (family seed)
        remaining original execution command beforeTrace originalSelected originalMoved
      rw [actor] at fixedTrace
      exact ⟨fixedTrace⟩

end Interaction.ReactiveApplication
