/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolutionLaws
import Interaction.SealedResolutionPolicy
import Interaction.SealedResolutionBinding
import Interaction.SealedResolutionFirstTimeout

/-! # Nullable continuation and deadline boundary regressions

Two sequential commit/reveal pairs suffice to check that a missing first
commitment resolves, that its reveal becomes null, and that a later player's
valid messages still execute. A separate run locks a non-null value and then
misses its reveal: public resolution changes, private storage does not.
-/

namespace InteractionTests.SealedResolution

open Interaction

private def runtime : SealedResolution Bool (Option Bool) :=
  ⟨⟨[⟨.commit false, []⟩, ⟨.reveal false 0, [0]⟩,
      ⟨.commit true, [0, 1]⟩, ⟨.reveal true 2, [0, 1, 2]⟩]⟩, none, 2⟩

private def missedCommit := runtime.tick (runtime.tick runtime.initial)

private def parallelRuntime : SealedResolution Bool (Option Bool) :=
  ⟨⟨[⟨.commit false, []⟩, ⟨.commit true, []⟩,
      ⟨.commit false, [0, 1]⟩]⟩, none, 2⟩

/-- One scan can expire several independently ready nodes, but a dependent
node that becomes ready in that scan keeps its full positive window. -/
theorem simultaneous_timeouts_leave_newly_ready_node_live :
    let after := parallelRuntime.tick (parallelRuntime.tick parallelRuntime.initial)
    after.visible.timeouts = [0, 1] ∧
      after.visible.firstReady? 2 = some 2 ∧ after.visible.completed 2 = false := by
  decide

/-- The generic first-timeout lemma applies to every expired node in the
same actual clock step, rather than selecting only the first list entry. -/
theorem simultaneous_timeout_prerequisites_before
    (node : Nat)
    (hnode : node ∈ (parallelRuntime.tick
      (parallelRuntime.tick parallelRuntime.initial)).visible.timeouts) :
    ∃ rule timestamp,
      parallelRuntime.program.rules[node]? = some rule ∧
      (parallelRuntime.tick parallelRuntime.initial).visible.firstReady? node = some timestamp ∧
      timestamp + parallelRuntime.window ≤
        (parallelRuntime.tick parallelRuntime.initial).visible.clock + 1 ∧
      rule.requires.all (SealedProgram.done
        (parallelRuntime.tick parallelRuntime.initial).visible.events) = true :=
  parallelRuntime.tick_first_timeout_ready_before (by decide)
    (parallelRuntime.tick parallelRuntime.initial)
    (SealedResolution.PublicState.ReadySound.initial parallelRuntime).tick
    (by decide) node hnode

private def zeroWindowRuntime : SealedResolution Bool (Option Bool) :=
  ⟨⟨[⟨.commit false, []⟩, ⟨.commit true, [0]⟩]⟩, none, 0⟩

/-- Positivity is necessary: a zero-window scan can expire a node whose
prerequisite was itself only completed by timeout in that same scan. -/
theorem zero_window_breaks_prior_normal_readiness :
    (zeroWindowRuntime.tick zeroWindowRuntime.initial).visible.timeouts = [0, 1] ∧
      SealedProgram.done zeroWindowRuntime.initial.visible.events 0 = false := by
  decide

theorem initial_readiness :
    runtime.initial.visible.firstReady? 0 = some 0 ∧
      runtime.initial.visible.firstReady? 1 = none ∧
      runtime.initial.visible.firstReady? 2 = none := by decide

theorem deadline_not_before_boundary :
    (runtime.tick runtime.initial).visible.timeouts = [] := by decide

theorem missing_commit_resolves_without_registration :
    missedCommit.visible.timeouts = [0] ∧
      missedCommit.service.lookup (false, 0) = none ∧
      SealedProgram.accepted? missedCommit.visible.events 0 = none ∧
      missedCommit.visible.published? 1 = some none ∧
      missedCommit.visible.firstReady? 2 = some 2 := by decide

/-- Even arbitrary subsequent commands cannot make an execution that has
already timed out look timeout-free. -/
theorem timeout_cannot_be_erased
    (players : Bool → runtime.messageApplication.PlayerPolicy)
    (environment : runtime.messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Bool))
    (final : runtime.messageApplication.PolicyExecution)
    (hfinal : final ∈ (runtime.messageApplication.runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial _
        (MessageApplication.State.initial _ missedCommit))).support) :
    final.native.application.visible.timeouts ≠ [] := by
  intro hclear
  have hbefore := runtime.runPolicies_clear_before players environment schedule _ final
    hfinal hclear
  have hrecorded : missedCommit.visible.timeouts = [0] := rfl
  change missedCommit.visible.timeouts = [] at hbefore
  rw [hrecorded] at hbefore
  contradiction

private def registerLater : SealedResolution.ApplicationState Bool (Option Bool) :=
  { missedCommit with service := (missedCommit.service.sealValue true 2 (some true)).state }

private def laterAccepted :=
  runtime.handle registerLater ⟨(true, 0), .commitment 2 (true, 2)⟩

private def laterOpened := laterAccepted.bind fun state =>
  runtime.handle state ⟨(true, 1), .opening 3 (true, 2) (some true)⟩

theorem later_play_survives_default :
    (laterOpened.map fun state =>
      (state.visible.published? 1, state.visible.published? 3, state.visible.timeouts)) =
        some (some none, some (some true), [0]) := by decide

theorem late_commit_rejected :
    (runtime.handle missedCommit ⟨(false, 1), .commitment 0 (false, 0)⟩).isNone = true := by
  decide

private def registered : SealedResolution.ApplicationState Bool (Option Bool) :=
  { runtime.initial with
    service := (runtime.initial.service.sealValue false 0 (some true)).state }

private def accepted := runtime.handle registered ⟨(false, 0), .commitment 0 (false, 0)⟩

private def missedOpening := accepted.map fun state => runtime.tick (runtime.tick state)

theorem missing_opening_preserves_locked_value :
    (missedOpening.map fun state =>
      (state.service.lookup (false, 0), state.visible.published? 1, state.visible.timeouts)) =
        some (some (some true), some none, [1]) := by decide

theorem late_opening_rejected :
    (missedOpening.bind fun state =>
      runtime.handle state ⟨(false, 1), .opening 1 (false, 0) (some true)⟩).isNone = true := by
  decide

private def sealedNull : SealedResolution.ApplicationState Bool (Option Bool) :=
  { runtime.initial with service := (runtime.initial.service.sealValue false 0 none).state }

theorem sealed_null_is_occupied_not_absent :
    sealedNull.service.lookup (false, 0) = some none ∧
      (runtime.handle sealedNull ⟨(false, 0), .commitment 0 (false, 0)⟩).isSome = true ∧
      (runtime.handle sealedNull ⟨(false, 0), .cleartext 0 none⟩).isNone = true := by decide

noncomputable section

open MessageApplication GameTheory.Math.Probability

private def retryPolicy : runtime.messageApplication.PlayerPolicy := fun history _ =>
  FinDist.pure (.privateCommand ⟨(0, if history.isEmpty then none else some true)⟩)

/-- The first registered null remains a populated private cache after public
timeout resolution and a retry carrying a different value. -/
theorem retry_after_timeout_retains_cache :
    ((runtime.messageApplication.runPolicies (fun _ => retryPolicy)
      (fun _ _ => FinDist.pure (.application ⟨()⟩))
      [.player false, .environment, .environment, .player false]
      (PolicyExecution.initial _ (State.initial _ runtime.initial))).map fun final =>
        (final.native.application.service.lookup (false, 0),
          (runtime.program.registrationEncoding 0).cachedValue runtime.messageApplication
            (final.principalHistory false), final.native.application.visible.timeouts)) =
      FinDist.pure (some none, some none, [0]) := by
  simp only [runPolicies, invoke, retryPolicy, playerStep, environmentPolicyStep, advance,
    PlayerCommand.toAction, EnvironmentPolicyCommand.toAction, MessageApplication.step,
    SealedResolution.messageApplication, FinDist.pure_bind, FinDist.map_pure]
  rfl

end

end InteractionTests.SealedResolution
