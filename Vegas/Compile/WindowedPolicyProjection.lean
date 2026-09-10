/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedExecutionProjection

/-! # Exact policy-run projection for deadline-independent traffic

The comparison retains all command choices and random kernels. Activation
metadata is erased from both current observations and every remembered view.
It embeds selected policies; it does not back-translate arbitrary window-aware
deviations. The player-step projection itself is unconditional; the
deadline-independent traffic condition is needed at environment admission.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem advance_erase (runtime : WindowedApplication P L)
    (execution : runtime.application.PolicyExecution) (action : Option runtime.application.Action)
    (hstate : runtime.Consistent execution.native.application)
    (hsafe : execution.native.pool.Satisfies (fun message => message.payload.DeadlineIndependent)) :
    (runtime.application.advance execution action).map
      (fun advanced => (runtime.eraseState advanced.1, advanced.2.map runtime.eraseAction)) =
    runtime.image.orderedApplication.advance (runtime.eraseExecution execution)
      (action.map runtime.eraseAction) := by
  cases action with
  | none => simp only [MessageApplication.advance, Option.map_none, FinDist.map_pure]; rfl
  | some action =>
      simp only [MessageApplication.advance, Option.map_some, FinDist.map_bind, FinDist.map_pure]
      dsimp only [eraseExecution]
      rw [← runtime.step_erase execution.native action hstate hsafe, FinDist.bind_map]
      apply FinDist.bind_congr
      intro next _
      simp only [List.map_append, List.map_cons, List.map_nil]

/-- Raw player steps commute with activation erasure, including private
preparation and arbitrary submissions. No deadline or pool restriction is
needed: players do not directly execute the admission handler. -/
theorem playerStep_erase (runtime : WindowedApplication P L) (who : P)
    (execution : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand) :
    (runtime.application.playerStep who execution command).map
      runtime.eraseExecution =
    runtime.image.orderedApplication.playerStep who (runtime.eraseExecution execution)
      (runtime.erasePlayerCommand command) := by
  have haction :
      (PlayerCommand.toAction runtime.application who command).map runtime.eraseAction =
      PlayerCommand.toAction runtime.image.orderedApplication who
        (runtime.erasePlayerCommand command) := by
    cases command <;> rfl
  have hadvance :
      (runtime.application.advance execution (PlayerCommand.toAction runtime.application who
        command)).map (fun advanced =>
          (runtime.eraseState advanced.1, advanced.2.map runtime.eraseAction)) =
      runtime.image.orderedApplication.advance (runtime.eraseExecution execution)
        ((PlayerCommand.toAction runtime.application who command).map runtime.eraseAction) := by
    cases command <;>
      simp only [PlayerCommand.toAction, MessageApplication.advance, MessageApplication.step,
        Option.map_some, Option.map_none, eraseAction, FinDist.pure_bind, FinDist.map_pure,
        eraseExecution, List.map_append, List.map_cons, List.map_nil] <;> rfl
  simp only [MessageApplication.playerStep, FinDist.map_bind, FinDist.map_pure]
  rw [← haction, ← hadvance, FinDist.bind_map]
  apply FinDist.bind_congr
  intro advanced _
  simp only [eraseExecution]
  congr 2
  funext other
  by_cases heq : other = who
  · subst other
    simp only [↓reduceIte, List.map_append, List.map_cons,
      List.map_nil, erasePlayerEntry, erase_observe]
  · simp only [heq, ↓reduceIte]

/-- Erasing a supported raw player step gives a supported step in any ambient
application image. Images differ at admission, which player steps do not run. -/
theorem playerStep_erased_support
    (runtime : WindowedApplication P L) (image : ApplicationImage P L) (actor : P)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand)
    (hstep : next ∈ (runtime.application.playerStep actor execution command).support) :
    runtime.eraseExecution next ∈ (image.application.playerStep actor
      (runtime.eraseExecution execution) (runtime.erasePlayerCommand command)).support := by
  have hstepEq : runtime.image.orderedApplication.playerStep actor
      (runtime.eraseExecution execution) (runtime.erasePlayerCommand command) =
      image.application.playerStep actor (runtime.eraseExecution execution)
        (runtime.erasePlayerCommand command) := by
    cases command <;> rfl
  rw [← hstepEq, ← runtime.playerStep_erase actor execution command, FinDist.support_map]
  exact Set.mem_image_of_mem _ hstep

private theorem environmentStep_erase (runtime : WindowedApplication P L)
    (execution : runtime.application.PolicyExecution)
    (command : runtime.image.orderedApplication.EnvironmentPolicyCommand)
    (hstate : runtime.Consistent execution.native.application)
    (hsafe : execution.native.pool.Satisfies (fun message => message.payload.DeadlineIndependent)) :
    (runtime.application.environmentPolicyStep execution
      (runtime.liftEnvironmentCommand command)).map runtime.eraseExecution =
    runtime.image.orderedApplication.environmentPolicyStep
      (runtime.eraseExecution execution) command := by
  have haction :
      (EnvironmentPolicyCommand.toAction runtime.application
        (runtime.liftEnvironmentCommand command)).map runtime.eraseAction =
      EnvironmentPolicyCommand.toAction runtime.image.orderedApplication command := by
    cases command <;> rfl
  simp only [MessageApplication.environmentPolicyStep, FinDist.map_bind, FinDist.map_pure]
  rw [← haction, ← runtime.advance_erase execution _ hstate hsafe, FinDist.bind_map]
  apply FinDist.bind_congr
  intro advanced _
  congr 1
  simp only [eraseExecution, List.map_append, List.map_cons, List.map_nil,
    eraseEnvironmentEntry, erase_environmentView, erase_lift_environmentCommand]

/-- One invocation of observation-erased policies has precisely the original
projected law. No restriction on the environment's clock commands is needed. -/
theorem invoke_erase (runtime : WindowedApplication P L)
    (players : P → runtime.image.orderedApplication.PlayerPolicy)
    (environment : runtime.image.orderedApplication.EnvironmentPolicy)
    (execution : runtime.application.PolicyExecution) (invocation : @Invocation P)
    (hstate : runtime.Consistent execution.native.application)
    (hsafe : execution.native.pool.Satisfies (fun message => message.payload.DeadlineIndependent)) :
    (runtime.application.invoke (fun who => runtime.liftPlayerPolicy (players who))
      (runtime.liftEnvironmentPolicy environment) execution invocation).map runtime.eraseExecution =
    runtime.image.orderedApplication.invoke players environment
      (runtime.eraseExecution execution) invocation := by
  cases invocation with
  | player who =>
      simp only [MessageApplication.invoke, liftPlayerPolicy, FinDist.map_bind,
        FinDist.bind_map, erase_observe]
      apply FinDist.bind_congr
      intro command _
      simpa only [erase_lift_playerCommand] using
        playerStep_erase runtime who execution (runtime.liftPlayerCommand command)
  | environment =>
      simp only [MessageApplication.invoke, liftEnvironmentPolicy, FinDist.map_bind,
        FinDist.bind_map, erase_environmentView]
      apply FinDist.bind_congr
      intro command _
      exact environmentStep_erase runtime execution command hstate hsafe

/-- Lifting deadline-independent policies preserves the complete projected
execution law, including native traffic, receipts, and polling histories.
The source policies and environment are fixed; the concrete strategy space
still includes policies that inspect activation metadata or submit expiry. -/
theorem runPolicies_erase (runtime : WindowedApplication P L)
    (players : P → runtime.image.orderedApplication.PlayerPolicy)
    (environment : runtime.image.orderedApplication.EnvironmentPolicy)
    (hsubmit : ∀ (execution : runtime.image.orderedApplication.PolicyExecution) who payload,
      .submit payload ∈ (players who (execution.principalHistory who)
        (MessageApplication.State.observe runtime.image.orderedApplication
          execution.native who)).support → payload.DeadlineIndependent)
    (schedule : List (@Invocation P)) (execution : runtime.application.PolicyExecution)
    (hstate : runtime.Consistent execution.native.application)
    (hsafe : execution.native.pool.Satisfies (fun message => message.payload.DeadlineIndependent)) :
    (runtime.application.runPolicies (fun who => runtime.liftPlayerPolicy (players who))
      (runtime.liftEnvironmentPolicy environment) schedule execution).map runtime.eraseExecution =
    runtime.image.orderedApplication.runPolicies players environment schedule
      (runtime.eraseExecution execution) := by
  have hsubmitLifted : ∀ (current : runtime.application.PolicyExecution) who payload,
      .submit payload ∈ (runtime.liftPlayerPolicy (players who) (current.principalHistory who)
        (MessageApplication.State.observe runtime.application current.native who)).support →
      ∀ serial, ApplicationImage.Payload.DeadlineIndependent
        (⟨(who, serial), payload⟩ : Message P runtime.application.Payload).payload := by
    intro current who payload hcommand serial
    simp only [liftPlayerPolicy, FinDist.support_map, Set.mem_image] at hcommand
    obtain ⟨command, hcommand, heq⟩ := hcommand
    have herased := congrArg runtime.erasePlayerCommand heq
    rw [erase_lift_playerCommand] at herased
    change command = .submit payload at herased
    subst command
    exact hsubmit (runtime.eraseExecution current) who payload hcommand
  apply MessageApplication.runPolicies_map_of_invoke
    (fun who => runtime.liftPlayerPolicy (players who))
    (runtime.liftEnvironmentPolicy environment) players environment runtime.eraseExecution
    (fun current => current.native.pool.Satisfies
      (fun message => message.payload.DeadlineIndependent) ∧
      runtime.Consistent current.native.application) ?_ ?_ schedule execution ⟨hsafe, hstate⟩
  · intro current invocation next hgood hnext
    apply runtime.application.runPolicies_message_application_invariant
      (fun message => message.payload.DeadlineIndependent) runtime.Consistent
      (fun state who command h => by cases command; exact h)
      (fun state message next h _ hnext => runtime.handle_consistent state next message h hnext)
      (fun state command next h hnext =>
        runtime.environmentStep_consistent state next command h hnext)
      (fun who => runtime.liftPlayerPolicy (players who))
      (runtime.liftEnvironmentPolicy environment) hsubmitLifted
      [invocation] current next hgood.1 hgood.2
    simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hnext
  · intro current invocation hgood
    exact runtime.invoke_erase players environment current invocation hgood.2 hgood.1

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.runPolicies_erase' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_erase
