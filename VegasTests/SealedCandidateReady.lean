/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateReady
import Vegas.Compile.SealedCandidateProgress
import VegasTests.SealedResolutionPolicy

/-! # Actual candidate policies continue after defaults

The environment advances the clock twice before the player is polled. The
first commitment defaults and its reveal publishes null. Every graph policy
then prepares a value at the next commitment, whose declared reads include
that defaulted public result. The execution starts at the real initial state.
-/

noncomputable section

namespace VegasTests.SealedCandidateReady

open Vegas Vegas.EventGraph Interaction Interaction.MessageApplication
open GameTheory.Math.Probability PendingStages
open SealedResolutionPolicy (runtime missingCommit secondGuard)

private abbrev app := runtime.candidateApplication

private def clockOnly : app.EnvironmentPolicy := fun _ _ =>
  FinDist.pure (.application ⟨()⟩)

private def initial : app.PolicyExecution :=
  PolicyExecution.initial app (State.initial app runtime.candidateInitial)

private def clocks (players : PendingStages.Player → app.PlayerPolicy) :
    FinDist app.PolicyExecution :=
  app.runPolicies players clockOnly [.environment, .environment] initial

private theorem clocks_observation (players : PendingStages.Player → app.PlayerPolicy) :
    (clocks players).map (fun next =>
      (next.native.application.visible, next.principalHistory 0)) =
      FinDist.pure (missingCommit.visible, []) := by
  simp [clocks, MessageApplication.runPolicies, invoke, clockOnly,
    environmentPolicyStep, advance, EnvironmentPolicyCommand.toAction,
    MessageApplication.step, app, SealedResolution.candidateApplication,
    SealedResolution.host, initial, PolicyExecution.initial]
  rfl

/-- A supported initialized execution witnesses honest progress after a
timeout, for every graph policy and without an honest-opponent hypothesis. -/
theorem prepares_after_default (policy : CommitPolicy graph 0)
    (players : PendingStages.Player → app.PlayerPolicy)
    (hplayer : players 0 = runtime.candidatePlayerPolicy
      (supported.resolvingPolicy none 2 0 policy)) :
    ∃ execution ∈ (clocks players).support,
      execution.native.application.visible.timeouts = [0] ∧
      ∀ command ∈ (players 0 (execution.principalHistory 0)
          (State.observe app execution.native 0)).support,
        ∃ value : Value, command = .privateCommand ⟨(2, value)⟩ ∧
          execution.native.application.service.lookup (0, 2) = .fresh := by
  obtain ⟨execution, hactual⟩ := (clocks players).support_nonempty
  have hobs : (execution.native.application.visible, execution.principalHistory 0) ∈
      ((clocks players).map (fun next =>
        (next.native.application.visible, next.principalHistory 0))).support := by
    rw [FinDist.support_map]
    exact ⟨execution, hactual, rfl⟩
  rw [clocks_observation, FinDist.mem_support_pure] at hobs
  have hvisible : execution.native.application.visible = missingCommit.visible :=
    congrArg Prod.fst hobs
  have hhistory : execution.principalHistory 0 = [] := congrArg Prod.snd hobs
  refine ⟨execution, hactual, ?_, ?_⟩
  · erw [hvisible]
    rfl
  · intro command hcommand
    obtain ⟨selected, hbound, hnotDone, _, hphase⟩ :=
      supported.candidatePolicy_progress_of_ready none 2 0 policy players clockOnly hplayer
        [.environment, .environment] execution hactual (node 2)
        (by erw [hvisible]; decide) (by erw [hvisible]; decide)
        (Or.inl ⟨secondGuard, rfl⟩) command hcommand
    have hselected : selected = node 2 := by
      apply Fin.ext
      have hcases : selected.val = 0 ∨ selected.val = 1 ∨ selected.val = 2 := by
        have : selected.val ≤ 2 := hbound
        omega
      rcases hcases with hzero | hone | htwo
      · erw [hvisible, hzero] at hnotDone
        contradiction
      · erw [hvisible, hone] at hnotDone
        contradiction
      · exact htwo
    subst selected
    erw [hhistory] at hphase
    cases hphase with
    | registration guard hsem value hcache =>
        exact ⟨value, rfl, supported.candidatePolicy_registration_fresh none 2 0 policy
          players clockOnly hplayer [.environment, .environment] execution hactual
          2 value hcommand⟩
    | commitment guard hsem value hcache => cases hcache
    | opening producer guard hreveal hproducer value hcache => cases hcache

end VegasTests.SealedCandidateReady
