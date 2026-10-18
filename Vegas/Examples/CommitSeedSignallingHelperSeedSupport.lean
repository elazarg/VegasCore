/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperFirstCallback
import Interaction.ReactiveSchedulerBeforeResponse

/-! # Genuine helper prefixes and activations under the original seed posterior -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player)

/-- A supported immutable original seed and its actual prefix remain in the
behavioral scheduler's joint posterior. The existing joint realization law
retains the original seed at the actual prefix boundary. -/
theorem helper_fixed_prefix_supported (players : Player → app.Policy) (count : Nat)
    (execution next : app.Execution) (seed : Seeds)
    (supportedSeed : seed ∈ (implementation.posterior execution.environmentRecall).support)
    (reached : next ∈ (app.runRounds (family seed) players count execution).support) :
    next ∈ (app.runRounds scheduler players count execution).support ∧
      seed ∈ (implementation.posterior next.environmentRecall).support := by
  have joint := implementation.realizeJoint players count execution
  change ((implementation.posterior execution.environmentRecall).bind fun chosen =>
    (app.schedulerMixture seedPrior family).runJoint players count execution chosen) =
      (app.runRounds scheduler players count execution).bind (fun final =>
        (implementation.posterior final.environmentRecall).map (Prod.mk final)) at joint
  simp only [app.schedulerMixture_runJoint] at joint
  have paired : (next, seed) ∈ ((implementation.posterior execution.environmentRecall).bind
      fun chosen => (app.runRounds (family chosen) players count execution).map
        fun final => (final, chosen)).support := by
    rw [PMF.support_bind]
    apply Set.mem_iUnion₂.mpr
    refine ⟨seed, supportedSeed, ?_⟩
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨next, reached, rfl⟩
  rw [joint, PMF.support_bind] at paired
  obtain ⟨actual, actualReached, posterior⟩ := Set.mem_iUnion₂.mp paired
  obtain ⟨chosen, supported, same⟩ := PMF.support_map .. ▸ posterior
  have first : actual = next := congrArg Prod.fst same
  have second : chosen = seed := congrArg Prod.snd same
  subst actual
  subst chosen
  exact ⟨actualReached, supported⟩

/-- A supported original seed supports its actual command in the behavioral
scheduler and remains in the posterior after that command is recorded. -/
theorem helper_fixed_command_supported (execution : app.Execution) (seed : Seeds)
    (supportedSeed : seed ∈ (implementation.posterior execution.environmentRecall).support)
    (command : app.Command)
    (selected : command ∈ (family seed execution.environmentRecall
      (execution.observeEnvironment app)).support) :
    command ∈ (scheduler execution.environmentRecall (execution.observeEnvironment app)).support ∧
      seed ∈ (implementation.posterior (execution.environmentRecall ++
        [⟨execution.observeEnvironment app, command⟩])).support := by
  have joint := implementation.command_disintegrate execution
    (fun actual memory => PMF.pure (actual, memory))
  simp only [implementation, ReactiveApplication.schedulerMixture, PMF.bind_map] at joint
  change ((implementation.posterior execution.environmentRecall).bind fun memory =>
    (family memory execution.environmentRecall (execution.observeEnvironment app)).map
      fun actual => (actual, memory)) =
    (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind (fun actual =>
      (implementation.posterior (execution.environmentRecall ++
        [⟨execution.observeEnvironment app, actual⟩])).map (Prod.mk actual)) at joint
  have paired : (command, seed) ∈ ((implementation.posterior execution.environmentRecall).bind
      fun memory =>
        (family memory execution.environmentRecall (execution.observeEnvironment app)).map
        fun actual => (actual, memory)).support := by
    rw [PMF.support_bind]
    apply Set.mem_iUnion₂.mpr
    refine ⟨seed, supportedSeed, ?_⟩
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨command, selected, rfl⟩
  rw [joint, PMF.support_bind] at paired
  obtain ⟨actual, actualSelected, updated⟩ := Set.mem_iUnion₂.mp paired
  obtain ⟨memory, memorySupported, same⟩ := PMF.support_map .. ▸ updated
  have first : actual = command := congrArg Prod.fst same
  have second : memory = seed := congrArg Prod.snd same
  subst actual
  subst memory
  exact ⟨actualSelected, memorySupported⟩

/-- The actual fixed-seed prefix and its complete activation give the same
genuine counted decision under the installed scheduler. The original seed
remains supported after the activation's own environment record. -/
theorem helper_fixed_activation_counted_trace (seed : Seeds)
    (remaining count : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨(remaining + 1) + count, none, execution⟩))
    (supportedSeed : seed ∈ (implementation.posterior execution.environmentRecall).support)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (next : app.Execution)
    (reached : next ∈ (app.runRounds (family seed) players count execution).support)
    (who : Player)
    (selected : (.activate who : app.Command) ∈ (family seed next.environmentRecall
      (next.observeEnvironment app)).support) :
    Nonempty (countedProtocol.Trace
      (some ⟨remaining, some who, completeActivation next who⟩)) ∧
      seed ∈ (implementation.posterior
        (completeActivation next who).environmentRecall).support := by
  obtain ⟨mixed, retained⟩ := helper_fixed_prefix_supported players count execution next seed
    supportedSeed reached
  obtain ⟨beforeTrace⟩ := countedMenu.trace_runRounds initial horizon scheduler players covered
    (remaining + 1) count execution next trace mixed
  obtain ⟨chosen, posterior⟩ := helper_fixed_command_supported next seed retained
    (.activate who) selected
  have activated : completeActivation next who ∈
      (next.environmentStep app (.activate who)).support := by
    rw [completeActivation_law]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨activeTrace⟩ := countedMenu.trace_environment initial horizon scheduler remaining next
    (completeActivation next who) (.activate who) beforeTrace chosen activated
  exact ⟨⟨activeTrace⟩, posterior⟩

end Vegas.Examples.CommitSeedSignalling
