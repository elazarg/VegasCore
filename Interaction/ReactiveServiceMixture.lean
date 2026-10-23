/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveSchedulerImplementation
import Interaction.ReactiveResponseAccounting

/-! # Actual service invariants of an original-seed scheduler mixture -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal Seed : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)
  (prior : PMF Seed) (family : Seed → app.Scheduler)

omit [DecidableEq Principal] in
/-- Every posterior original seed supported after an actual command already
supported that same command before it. No new seed is allocated by conditioning. -/
theorem schedulerMixture_posterior_snoc_support (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (command : app.Command)
    (chosen : command ∈ ((app.schedulerMixture prior family).scheduler past view).support)
    (seed : Seed)
    (supported : seed ∈ ((app.schedulerMixture prior family).posterior
      (past ++ [⟨view, command⟩])).support) :
    seed ∈ ((app.schedulerMixture prior family).posterior past).support ∧
      command ∈ (family seed past view).support := by
  let implementation := app.schedulerMixture prior family
  let joint := (implementation.posterior past).bind fun seed =>
    implementation.respond seed (past, view)
  have positive : command ∈ (joint.map Prod.fst).support := by
    simpa only [SchedulerImplementation.scheduler_eq] using chosen
  rw [SchedulerImplementation.posterior_snoc] at supported
  obtain ⟨pair, pairSupport, seedEq⟩ := PMF.support_map .. ▸ supported
  have pairValid := mem_support_fiberPosterior positive pairSupport
  change pair.1 = command ∧ pair ∈ joint.support at pairValid
  obtain ⟨original, originalSupport, responseSupport⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ pairValid.2)
  obtain ⟨actual, actualSupport, same⟩ := PMF.support_map .. ▸ responseSupport
  change (actual, original) = pair at same
  have originalEq : original = seed := (congrArg Prod.snd same).trans seedEq
  have actualEq : actual = command := (congrArg Prod.fst same).trans pairValid.1
  subst original
  subst actual
  exact ⟨originalSupport, actualSupport⟩

/-- Seedwise actual service invariants pass to the behavioralized scheduler
while retaining every supported original seed and its entire current predicate. -/
theorem ServiceInvariant.schedulerMixture
    (predicate : Seed → app.Execution → Prop)
    (invariant : ∀ seed, app.ServiceInvariant (family seed) (predicate seed)) :
    app.ServiceInvariant (app.schedulerMixture prior family).scheduler
      (fun execution => ∀ seed ∈ ((app.schedulerMixture prior family).posterior
        execution.environmentRecall).support, predicate seed execution) where
  respond execution who action valid := by
    intro seed supported
    rw [app.respond_environmentRecall] at supported
    exact (invariant seed).respond execution who action (valid seed supported)
  environment execution next command valid selected reached := by
    intro seed supported
    rw [app.environmentStep_environmentRecall execution next command reached] at supported
    obtain ⟨previous, actualCommand⟩ := app.schedulerMixture_posterior_snoc_support prior family
      execution.environmentRecall (execution.observeEnvironment app) command selected seed supported
    exact (invariant seed).environment execution next command (valid seed previous)
      actualCommand reached

end Interaction.ReactiveApplication
