/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceEvaluation
import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactiveMessageReadout
import Interaction.ReactivePublication

/-! # Application observations during arbitrary response windows

A finite roster of player activations can change private candidate catalogues,
network traffic and response recall. Before an inclusion or application command,
it preserves the graph configuration and public application view. This holds for
every raw response and passive sample, including repeated commitment attempts.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- No response or passive observation advances an application event. This
does not erase any pending traffic, candidate changes, or private recall. -/
theorem player_window_application (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (visits : List Player)
    (initial final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support) :
    final.application.config = initial.application.config ∧
      final.application.publicView = initial.application.publicView := by
  let app := runtime.reactiveApplication leaks
  induction visits generalizing initial with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨rfl, rfl⟩
  | cons who rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map,
        PMF.bind_bind, Function.comp_def] at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨action, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have remaining := ih _ reached
      have unchanged := runtime.reactive_respond_application leaks
        (initial.sampledActivation app who sample) who action
      exact ⟨remaining.1.trans unchanged.1, remaining.2.trans unchanged.2⟩

/-- An arbitrary response roster has no inclusion action, so its pending
submissions cannot change the public ledger. -/
theorem player_window_ledger (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (visits : List Player)
    (initial final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support) :
    final.network.ledger = initial.network.ledger := by
  let app := runtime.reactiveApplication leaks
  induction visits generalizing initial with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | cons who rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map,
        PMF.bind_bind, Function.comp_def] at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨action, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact (ih _ reached).trans (app.respond_ledger (initial.sampledActivation app who sample)
        who action)

/-- Every service command retains prior own responses, including arbitrary
network-selected commands and application changes. -/
theorem interactionPlan_recall_mono (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (initial final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network plan initial).support)
    (who : Player) : initial.recall who ⊆ final.recall who := by
  let app := runtime.reactiveApplication leaks
  induction plan generalizing initial with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact List.Subset.refl _
  | cons instruction rest ih =>
      obtain ⟨middle, first, reached⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      apply List.Subset.trans ?_ (ih middle reached)
      obtain ⟨command, _, first⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ first)
      unfold ReactiveApplication.dispatch at first
      obtain ⟨activated, environment, response⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ first)
      have recall := app.environmentStep_recall initial activated command environment
      change middle ∈ (app.resume players (command.actor? app) activated).support at response
      cases actor : command.actor? app with
      | none =>
          rw [actor] at response
          cases (PMF.mem_support_pure_iff _ _).mp response
          rw [recall]
      | some active =>
          rw [actor] at response
          obtain ⟨action, _, rfl⟩ := PMF.support_map .. ▸ response
          rw [← recall]
          exact app.respond_recall_mono activated active who action

end Vegas.EventGraphRuntime
