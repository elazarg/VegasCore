/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionReadBound
import VegasTests.PendingSource

/-! # Native registration and acceptance hiding for a checked two-player source

The source's first two choices precede every disclosure. The second player's
arbitrary randomized native policy therefore has the same stopped registration
law for all assignments to the honest player's choice, under any randomized
full-pool environment and finite invocation sequence. The same independence
holds for its complete local input through public acceptance, including the
interval after private registration.
-/

noncomputable section

namespace VegasTests.SealedResolutionReadBound

open Vegas Vegas.EventGraph Interaction Interaction.MessageApplication
open GameTheory.Math.Probability PendingSource

abbrev Value := Option Bool
abbrev runtime := sealedFragment.resolvingRuntime none 3
abbrev app := runtime.messageApplication

private theorem no_honest_known_before_second (who : PendingSource.Player) (hwho : who ≠ 1)
    (index : Fin graph.nodeCount)
    (hknown : sealedFragment.knownBefore 1 (node 1) (who, index.val)) :
    False := by
  rcases hknown with hwhoEq | ⟨opening, requires, hbefore, hrule⟩
  · exact hwho hwhoEq
  · have hopening : opening = 0 := by
      change opening < 1 at hbefore
      omega
    subst opening
    change some (SealedRule.mk (.commit 0) []) =
      some (SealedRule.mk (.reveal who index.val) requires) at hrule
    cases hrule

theorem hidden_first_choice (leftValues rightValues : Fin graph.nodeCount → Value)
    (deviator : app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation PendingSource.Player)) :
    sealedFragment.resolvingBindingLaw none 3 leftValues 1 (node 1)
        deviator environment schedule =
      sealedFragment.resolvingBindingLaw none 3 rightValues 1 (node 1)
        deviator environment schedule := by
  obtain ⟨guard, hguard, _⟩ := node1_commit
  apply sealedFragment.resolvingBindingLaw_read_bound none 3 1 (node 1) guard hguard
    leftValues rightValues ?_ deviator environment schedule
  intro who hwho index hknown
  exact False.elim (no_honest_known_before_second who hwho index hknown)

/-- Independence holds through public acceptance, rather than ending at the
focal player's private preparation. The observation includes its full history. -/
theorem hidden_until_acceptance (leftValues rightValues : Fin graph.nodeCount → Value)
    (deviator : app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation PendingSource.Player)) :
    sealedFragment.resolvingAcceptanceLaw none 3 leftValues 1 (node 1)
        deviator environment schedule =
      sealedFragment.resolvingAcceptanceLaw none 3 rightValues 1 (node 1)
        deviator environment schedule := by
  obtain ⟨guard, hguard, _⟩ := node1_commit
  apply sealedFragment.resolvingAcceptanceLaw_read_bound none 3 1 (node 1) guard hguard
    leftValues rightValues ?_ deviator environment schedule
  intro who hwho index hknown
  exact False.elim (no_honest_known_before_second who hwho index hknown)

/-- Private preparation does not close the acceptance cut or release a later
opening. Public acceptance is a distinct transition. -/
theorem registration_is_not_acceptance :
    let initial := PolicyExecution.initial app (State.initial app runtime.initial)
    let prepared : app.PolicyExecution := { initial with
      native.application.service := (IdealCommitments.empty.sealValue 1 1 (some true)).state }
    sealedFragment.bindingCut none 3 1 (node 1) prepared = true ∧
      sealedFragment.acceptanceCut none 3 (node 1) prepared = false ∧
      sealedFragment.compile.openingReady prepared.native.application.visible.events 0 2 = false :=
  ⟨rfl, rfl, rfl⟩

private def prepareThenSubmit : app.PlayerPolicy := fun history _ =>
  FinDist.pure (if history.isEmpty then .privateCommand ⟨(1, some true)⟩
    else .submit (.commitment 1 (1, 1)))

/-- The cut actually waits past private preparation and pending submission,
and retains the two commands and the accepted event in the player's input. -/
theorem acceptance_retains_preparation_and_submission :
    (sealedFragment.resolvingAcceptanceLaw none 3 (fun _ => some false) 1 (node 1)
      prepareThenSubmit (fun _ _ => FinDist.pure (.include (1, 0)))
      [.player 1, .player 1, .environment]).map
        (fun input => (input.1.length, input.2.application.events)) =
      FinDist.pure (2, [.accepted 1 (1, 1)]) := by
  simp only [SealedFragment.resolvingAcceptanceLaw, tracePolicies, invoke,
    SealedFragment.resolvingValuePlayers, GameTheory.Profile.update_same,
    prepareThenSubmit, playerStep, environmentPolicyStep, advance, PlayerCommand.toAction,
    EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
    FinDist.map_pure, PolicyExecution.initial, List.isEmpty_nil, List.isEmpty_cons,
    List.nil_append, ↓reduceIte, Bool.false_eq_true]
  rfl

/-- This witness actually submits and delivers an opaque pending commitment
before the focal registration; there is no inclusion or opening in the trace. -/
theorem registration_after_pending_delivery :
    sealedFragment.resolvingBindingLaw none 3 (fun _ => some false) 1 (node 1)
        (fun _ _ => FinDist.pure (.privateCommand ⟨(1, some true)⟩))
        (fun _ _ => FinDist.pure (.deliver 1 (0, 0)))
        [.player 0, .player 0, .environment, .player 1] = FinDist.pure (some (some true)) := by
  let initial := PolicyExecution.initial app (State.initial app runtime.initial)
  let registered : app.PolicyExecution :=
    { initial with
      native := { initial.native with
        application.service := (IdealCommitments.empty.sealValue 0 0 (some false)).state }
      principalHistory := fun who => if who = 0 then
        [⟨State.observe app initial.native 0, .privateCommand ⟨(0, some false)⟩⟩] else []
      nativeTrace := [.privateCommand 0 ⟨(0, some false)⟩] }
  have hfirst : sealedFragment.resolvingPolicy none 3 0
      (sealedFragment.valuePolicy (fun _ => some false) 0)
      [] (State.observe app initial.native 0) =
        FinDist.pure (.privateCommand ⟨(0, some false)⟩ : app.PlayerCommand) := by
    change sealedFragment.commitCommand 0 (sealedFragment.valuePolicy (fun _ => some false) 0)
      (node 0) _ rfl [] _ = _
    unfold SealedFragment.commitCommand
    simp only [ChoiceEncoding.cachedValue_nil]
    exact FinDist.map_pure _ _
  have hregistered : app.playerStep 0 initial (.privateCommand ⟨(0, some false)⟩) =
      FinDist.pure registered := by
    simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
      FinDist.pure_bind]
    rfl
  have hsecond : sealedFragment.resolvingPolicy none 3 0
      (sealedFragment.valuePolicy (fun _ => some false) 0)
      (registered.principalHistory 0) (State.observe app registered.native 0) =
        FinDist.pure (.submit (.commitment 0 (0, 0)) : app.PlayerCommand) := rfl
  simp only [SealedFragment.resolvingBindingLaw, tracePolicies, invoke,
    SealedFragment.resolvingValuePlayers, GameTheory.Profile.update_same,
    GameTheory.Profile.update_of_ne _ _ (show (0 : PendingSource.Player) ≠ 1 by decide)]
  erw [hfirst]
  simp only [FinDist.pure_bind]
  erw [hregistered]
  simp only [FinDist.pure_bind]
  erw [hsecond]
  simp only [playerStep, environmentPolicyStep, advance, PlayerCommand.toAction,
    EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind, FinDist.map_pure]
  rfl

end VegasTests.SealedResolutionReadBound

/-- info: 'VegasTests.SealedResolutionReadBound.hidden_first_choice' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedResolutionReadBound.hidden_first_choice
