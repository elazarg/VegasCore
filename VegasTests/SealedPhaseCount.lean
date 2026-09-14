/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPhaseCount
import VegasTests.SealedResolutionPolicy

/-! # Actual registration charges after a source default

The checked multistage source performs a real registration at its second
commitment. Its one-step trace witnesses that the phase predicate is inhabited;
the general counting theorem rules out every different registration position.
-/

noncomputable section

namespace VegasTests.SealedPhaseCount

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction Interaction.MessageApplication
open GameTheory.Math.Probability PendingStages SealedResolutionPolicy

private def initial : app.PolicyExecution :=
  PolicyExecution.initial app (State.initial app missingCommit)

private def registered : app.PolicyExecution :=
  { initial with
    native.application.service := (initial.native.application.service.sealValue 0 2 none).state
    principalHistory := fun other => if other = 0 then
      [⟨view missingCommit, .privateCommand ⟨(2, none)⟩⟩] else []
    nativeTrace := [.privateCommand 0 ⟨(2, none)⟩] }

private def trace : app.PolicyTrace := .step initial (.finish registered)

private def graphPolicy : CommitPolicy graph 0 :=
  compileSourcePolicy core source.core.fresh SealedPolicy.initialBuild rfl 0
    (SourceGraph.repeatPolicy (FinDist.pure none) 0)

private def players : PendingStages.Player → app.PlayerPolicy := fun _ =>
  supported.resolvingPolicy none 2 0 graphPolicy

private theorem registration_step :
    registered ∈ (app.playerStep 0 initial (.privateCommand ⟨(2, none)⟩)).support := by
  simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
    FinDist.pure_bind, FinDist.mem_support_pure]
  rfl

private theorem registration_command :
    .privateCommand ⟨(2, none)⟩ ∈
      (players 0 (initial.principalHistory 0) (State.observe app initial.native 0)).support := by
  change .privateCommand ⟨(2, none)⟩ ∈
    (SealedPolicy.compilation.compileResolvingPolicy none 2 0
      (SourceGraph.repeatPolicy (FinDist.pure none) 0) [] (view missingCommit)).support
  rw [missing_commit_continues, FinDist.mem_support_pure]

private theorem supported_trace (environment : app.EnvironmentPolicy) :
    trace ∈ (app.tracePolicies players environment [.player 0] initial).support := by
  simp only [tracePolicies, invoke, FinDist.support_bind, Set.mem_iUnion,
    FinDist.support_map, Set.mem_image]
  refine ⟨registered, ⟨_, registration_command, registration_step⟩,
    .finish registered, FinDist.mem_support_pure.mpr rfl, rfl⟩

/-- A positive witness through the actual policy and native step. -/
theorem actual_registration : supported.RegistrationAt none 2 trace 0 graphPolicy 2 0 :=
  ⟨none, registration_command, registration_step⟩

/-- The only registration position is the one actually executed, including
when queries extend beyond the trace's final checkpoint. -/
theorem registration_position_iff (index : Nat) :
    supported.RegistrationAt none 2 trace 0 graphPolicy 2 index ↔ index = 0 := by
  constructor
  · intro hindex
    let environment : app.EnvironmentPolicy := fun _ _ => FinDist.pure .wait
    exact supported.registrationAt_unique none 2 players environment [.player 0] initial trace
      (by intro owner slot; rfl) (supported_trace environment) 0 graphPolicy 2 index 0
      hindex actual_registration
  · rintro rfl
    exact actual_registration

end VegasTests.SealedPhaseCount
