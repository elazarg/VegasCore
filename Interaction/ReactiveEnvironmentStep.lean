/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveApplication

/-! # Primitive effects of a supported environment step -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- Eliminate the actual environment-step law into its four primitive effects.
The activation and application branches retain their sample-support hypotheses;
every branch records the command against the original public observation. -/
theorem environmentStep_cases (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support)
    {predicate : app.Command → app.Execution → Prop}
    (wait : predicate .wait { execution with environmentRecall :=
      execution.environmentRecall ++ [⟨execution.observeEnvironment app, .wait⟩] })
    (activate : ∀ who selected,
      selected ∈ (app.observePending who execution.network.pending).support →
      predicate (.activate who) { execution with
        network := execution.network.learn who selected
        environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment app, .activate who⟩] })
    (includeCase : ∀ id, predicate (.include id)
      { execution.includePending app id with environmentRecall :=
        execution.environmentRecall ++ [⟨execution.observeEnvironment app, .include id⟩] })
    (application : ∀ command state,
      state ∈ (app.environment execution.application command).support →
      predicate (.application command) { execution with
        application := state
        environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment app, .application command⟩] }) :
    predicate command next := by
  cases command with
  | wait =>
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact wait
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨selected, sampled, rfl⟩ := PMF.support_map .. ▸ supported
      exact activate who selected sampled
  | «include» id =>
      simp only [Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact includeCase id
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      exact application command state changed

end Interaction.ReactiveApplication
