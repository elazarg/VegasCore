/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.RestrictedInformation
import Vegas.Examples.MonitoredGuessing.NativeHistory

/-! # Exhaustive restricted receiver checkpoints

The full-support reference policy reaches every legal restricted history.
Its actual calendar evaluation therefore classifies every receiver decision,
without adding a second execution semantics or assuming conformance of a run.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem reference_early_alice (bit : Bool) :
    restrictedMenu.uniformResponses alice ((aliceActivated bit).recall alice)
      ((aliceActivated bit).observe nativeApp alice) = FinDist.pure nativeSilent := by
  apply FinDist.eq_pure_of_support_subset_singleton
  intro response member
  have available := (restrictedMenu.uniformResponses_support alice _ _ response).mp member
  have permitted : restrictedMenu.actions alice ((aliceActivated bit).recall alice)
      ((aliceActivated bit).observe nativeApp alice) = {nativeSilent} := by
    classical
    simp [restrictedMenu, ordinaryActions, alice, bob, watcher, aliceActivated, nativeStart,
      ReactiveApplication.Execution.initial, ReactiveApplication.Execution.observe,
      nativeApp, reactiveApplication, State.publicView, nativeInitial, State.initial]
  rw [permitted, Finset.mem_singleton] at available
  exact available

theorem reference_quiet_watcher (bit : Bool) :
    restrictedMenu.uniformResponses watcher ((watcherActivated bit nativeSilent ∅).recall watcher)
      ((watcherActivated bit nativeSilent ∅).observe nativeApp watcher) =
        FinDist.pure nativeSilent := by
  apply FinDist.eq_pure_of_support_subset_singleton
  intro response member
  have available := (restrictedMenu.uniformResponses_support watcher _ _ response).mp member
  have permitted : restrictedMenu.actions watcher
      ((watcherActivated bit nativeSilent ∅).recall watcher)
      ((watcherActivated bit nativeSilent ∅).observe nativeApp watcher) = {nativeSilent} := by
    classical
    simp only [restrictedMenu, ↓reduceIte]
    rfl
  rw [permitted, Finset.mem_singleton] at available
  exact available

theorem reference_quiet_prefix (bit : Bool) :
    nativeRuntime.runInteractionPlan nativeLeaks restrictedMenu.uniformResponses nativeNetwork
      [.player alice, .player watcher, .wire, .grant bobPublication] (nativeStart bit) =
        FinDist.pure (quietGranted bit) := by
  have wire : nativeRuntime.interactionInstruction nativeLeaks nativeNetwork
      (watcherRespond bit nativeSilent ∅ nativeSilent).environmentRecall
      ((watcherRespond bit nativeSilent ∅ nativeSilent).observeEnvironment nativeApp) .wire =
      FinDist.pure .wait := by
    simp only [interactionInstruction, nativeNetwork, FinDist.map_pure]
    rfl
  have aliceStep : nativeRuntime.interactionStep nativeLeaks restrictedMenu.uniformResponses
      nativeNetwork (.player alice) (nativeStart bit) =
        FinDist.pure (ambientRespond bit nativeSilent) := by
    simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
      ReactiveApplication.dispatch, initial_activation]
    change (restrictedMenu.uniformResponses alice ((aliceActivated bit).recall alice)
      ((aliceActivated bit).observe nativeApp alice)).map _ = _
    rw [reference_early_alice, FinDist.map_pure]
    rfl
  have watcherStep : nativeRuntime.interactionStep nativeLeaks restrictedMenu.uniformResponses
      nativeNetwork (.player watcher) (ambientRespond bit nativeSilent) =
        FinDist.pure (watcherRespond bit nativeSilent ∅ nativeSilent) := by
    simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
      ReactiveApplication.dispatch, quiet_watcher_activation]
    change (restrictedMenu.uniformResponses watcher
      ((watcherActivated bit nativeSilent ∅).recall watcher)
      ((watcherActivated bit nativeSilent ∅).observe nativeApp watcher)).map _ = _
    rw [reference_quiet_watcher, FinDist.map_pure]
    rfl
  rw [runInteractionPlan, aliceStep, FinDist.pure_bind,
    runInteractionPlan, watcherStep, FinDist.pure_bind]
  rw [runInteractionPlan]
  change ((nativeRuntime.interactionInstruction nativeLeaks nativeNetwork _ _ .wire).bind _).bind
    _ = _
  rw [wire]
  simp only [FinDist.pure_bind, ReactiveApplication.dispatch, quiet_wire]
  rw [show (ReactiveApplication.Command.wait : nativeApp.Command).actor? nativeApp = none
    from rfl, ReactiveApplication.resume, FinDist.pure_bind]
  simp only [runInteractionPlan, interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch, quiet_grant]
  rw [show (ReactiveApplication.Command.application (.grant bobPublication) :
    nativeApp.Command).actor? nativeApp = none from rfl,
    ReactiveApplication.resume, FinDist.pure_bind]

theorem reference_rounds_four :
    nativeApp.roundsFrom nativeInitialLaw nativeScheduler restrictedMenu.uniformResponses 4 =
      (FinDist.uniformOfFintype (α := Bool)).map (quietGranted) := by
  rw [ReactiveApplication.roundsFrom, nativeInitialLaw, FinDist.bind_map]
  rw [FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro bit _
  have rounds := native_segment_rounds restrictedMenu.uniformResponses []
    [.player alice, .player watcher, .wire, .grant bobPublication] (nativePlan.drop 4)
    rfl (nativeStart bit) rfl
  exact rounds.trans (reference_quiet_prefix bit)

/-- This covers every legal C history with Bob active, not just the source
compiler's chosen behavioral profile. -/
theorem bob_control (control : nativeApp.Control)
    (trace : restrictedArena.Trace (some control)) (active : control.actor = some bob) :
    ∃ bit, control = ⟨9, some bob, quietBob bit⟩ := by
  have supported := restrictedMenu.roundSupported_uniform nativeInitialLaw nativeHorizon
    nativeScheduler trace
  rcases control with ⟨remaining, actor, execution⟩
  change actor = some bob at active
  subst actor
  obtain ⟨accounted, count, prior, command, position, priorMem, selected, acting, moved⟩ :=
    supported
  have countEq : count = 4 :=
    (nativeApp.roundsFrom_recall nativeInitialLaw nativeScheduler restrictedMenu.uniformResponses
      count prior priorMem).symm.trans
      (native_unique_bob_activation prior.environmentRecall
        (prior.observeEnvironment nativeApp) command selected acting)
  subst count
  rw [reference_rounds_four, FinDist.support_map] at priorMem
  obtain ⟨bit, _, rfl⟩ := priorMem
  have commandEq : command = .activate bob := FinDist.mem_support_pure.mp selected
  subst command
  rw [quiet_bob_activation, FinDist.mem_support_pure] at moved
  change execution = quietBob bit at moved
  subst execution
  have remainingEq : remaining = 9 := by
    change 5 + remaining = 14 at accounted
    omega
  subst remaining
  exact ⟨bit, rfl⟩

theorem bob_site_input (site : restrictedModel.InformationSite bob) : site.1 = quietBobInfo := by
  obtain ⟨history, _, _⟩ := site.2
  have active := InformationModel.InformationSite.active restrictedModel site history
  rcases history with ⟨⟨state, trace⟩, observed⟩
  cases state with
  | none => cases active
  | some control =>
      obtain ⟨bit, same⟩ := bob_control control trace active
      subst control
      exact observed.symm.trans ((restrictedMenu.info nativeInitialLaw nativeHorizon
        nativeScheduler bob trace).trans (bob_input bit))

end Vegas.Examples.MonitoredGuessing.Restricted
