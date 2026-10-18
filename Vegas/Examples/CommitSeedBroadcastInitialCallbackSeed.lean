/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialCallbackPrefix
import Vegas.Examples.CommitSeedBroadcastPosteriorTrace
import Interaction.ReactiveSchedulerTranscript

/-! # The unchanged original seed posterior at quiet initial decisions -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem initial_alice_choose (seed : Seeds) :
    choose seed initialExecution.environmentRecall (initialExecution.observeEnvironment app) =
      .activate alice := by
  have chosen : choose seed initialExecution.environmentRecall
      (initialExecution.observeEnvironment app) ∈ (family seed initialExecution.environmentRecall
        (initialExecution.observeEnvironment app)).support :=
    (PMF.mem_support_pure_iff _ _).mpr rfl
  rwa [initial_alice_choice, PMF.mem_support_pure_iff] at chosen

private theorem initial_bob_choose (seed : Seeds) (first : app.Action) :
    choose seed (initialAliceCallback.respond app alice first).environmentRecall
      ((initialAliceCallback.respond app alice first).observeEnvironment app) = .activate bob := by
  have chosen : choose seed (initialAliceCallback.respond app alice first).environmentRecall
      ((initialAliceCallback.respond app alice first).observeEnvironment app) ∈
        (family seed (initialAliceCallback.respond app alice first).environmentRecall
          ((initialAliceCallback.respond app alice first).observeEnvironment app)).support :=
    (PMF.mem_support_pure_iff _ _).mpr rfl
  rwa [initial_bob_choice, PMF.mem_support_pure_iff] at chosen

private theorem initial_carol_choose (seed : Seeds) (first second : app.Action) :
    choose seed ((initialBobCallback first).respond app bob second).environmentRecall
      (((initialBobCallback first).respond app bob second).observeEnvironment app) =
        .activate carol := by
  have chosen : choose seed ((initialBobCallback first).respond app bob second).environmentRecall
      (((initialBobCallback first).respond app bob second).observeEnvironment app) ∈
        (family seed ((initialBobCallback first).respond app bob second).environmentRecall
          (((initialBobCallback first).respond app bob second).observeEnvironment app)).support :=
    (PMF.mem_support_pure_iff _ _).mpr rfl
  rwa [initial_carol_choice, PMF.mem_support_pure_iff] at chosen

private theorem quiet_initial_command_consistent (seed : Seeds) (owner : Player) :
    app.commandConsistentFrom choose seed [] (initialCallback owner).environmentRecall := by
  fin_cases owner
  · exact ⟨initial_alice_choose seed, trivial⟩
  · exact ⟨initial_alice_choose seed, initial_bob_choose seed ⟨none⟩, trivial⟩
  · exact ⟨initial_alice_choose seed, initial_bob_choose seed ⟨none⟩,
      initial_carol_choose seed ⟨none⟩ ⟨none⟩, trivial⟩

/-- Observing a quiet initial callback has not inspected any original service
coordinate. Its actual retained scheduler posterior is the initialized law. -/
theorem quiet_initial_original_seed_posterior (owner : Player) :
    implementation.posterior (initialCallback owner).environmentRecall = nativeSeedLaw := by
  obtain ⟨seed, supported⟩ := nativeSeedLaw.support_nonempty
  have positive : ∃ seed ∈ {seed | app.commandConsistentFrom choose seed []
      (initialCallback owner).environmentRecall}, seed ∈ nativeSeedLaw.support :=
    ⟨seed, quiet_initial_command_consistent seed owner, supported⟩
  change (app.schedulerMixture nativeSeedLaw (fun seed past view =>
    PMF.pure (choose seed past view))).posterior
      (initialCallback owner).environmentRecall = nativeSeedLaw
  rw [app.schedulerMixture_posterior_eq_filter nativeSeedLaw choose _ positive]
  exact filter_of_support_subset nativeSeedLaw _ positive
    (fun seed _ => quiet_initial_command_consistent seed owner)

end Vegas.Examples.CommitSeedBroadcast
