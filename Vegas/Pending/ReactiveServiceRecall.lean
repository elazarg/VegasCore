/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveServiceEvaluation
import Interaction.ReactiveHistory
import Interaction.ReactiveAllocation
import Interaction.ReactivePolicyInvariant

/-! # Own-response prefixes during actual service execution

Every supported service execution retains each player's earlier response
record. This applies to arbitrary network choices, including activations, and
therefore also to every suffix of a restricted reveal block.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Supported physical responses and environment commands preserve the same
execution predicate throughout an actual service plan. -/
theorem runInteractionPlan_preserves (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (predicate : (runtime.reactiveApplication leaks).Execution → Prop)
    (invariant : (runtime.reactiveApplication leaks).PolicyInvariant players predicate)
    (plan : List (ServiceInstruction graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (valid : predicate execution)
    (supported : next ∈ (runtime.runInteractionPlan leaks players network plan execution).support) :
    predicate next := by
  induction plan generalizing execution with
  | nil => cases FinDist.mem_support_pure.mp supported; exact valid
  | cons instruction rest ih =>
      obtain ⟨middle, stepped, continued⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      obtain ⟨command, _selected, moved⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ stepped)
      exact ih middle (invariant.dispatch command execution middle valid moved) continued

theorem runInteractionPlan_serials (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (initial final : (runtime.reactiveApplication leaks).Execution)
    (serials : initial.network.SerialsBeforeNext)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network plan initial).support) :
    final.network.SerialsBeforeNext := by
  let app := runtime.reactiveApplication leaks
  induction plan generalizing initial with
  | nil => cases FinDist.mem_support_pure.mp reached; exact serials
  | cons instruction rest ih =>
      obtain ⟨middle, stepped, continued⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      apply ih middle ?_ continued
      obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ stepped)
      obtain ⟨activated, observed, responded⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ moved)
      have valid := (app.serialsBeforeNextInvariant (fun _ _ => FinDist.pure command)).environment
        initial activated command serials (FinDist.mem_support_pure.mpr rfl) observed
      cases actor : command.actor? app with
      | none =>
          change middle ∈ (app.resume players (command.actor? app) activated).support at responded
          rw [actor] at responded
          cases FinDist.mem_support_pure.mp responded
          exact valid
      | some who =>
          change middle ∈ (app.resume players (command.actor? app) activated).support at responded
          rw [actor] at responded
          obtain ⟨response, _, rfl⟩ := FinDist.support_map .. ▸ responded
          exact (app.serialsBeforeNextInvariant (fun _ _ => FinDist.pure .wait)).respond
            activated who response valid

/-- The added entry records the actual local view and physical response. Its
emitted envelope is retained by the execution, including for replay aliases. -/
theorem response_recall_entry (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action) :
    ∃ entry, (execution.respond (runtime.reactiveApplication leaks) who response).recall who =
      execution.recall who ++ [entry] ∧
      entry.beforeView = execution.observe (runtime.reactiveApplication leaks) who ∧
      entry.action = response := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      refine ⟨⟨_, _, none⟩, ?_, rfl, rfl⟩
      simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
      rfl
  | some transmission =>
      cases transmission with
      | submit submission =>
          let app := runtime.reactiveApplication leaks
          refine ⟨⟨execution.observe app who, ⟨some (.submit submission)⟩,
            some (execution.network.submit who (app.packet
              (app.submit execution.application who submission) who
              (execution.network.known who) submission)).1⟩, ?_, rfl, rfl⟩
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
          rfl
      | replay id =>
          refine ⟨⟨_, ⟨some (.replay id)⟩, (execution.network.replay who id).1⟩,
            ?_, rfl, rfl⟩
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
          rfl

theorem interactionStep_recall_prefix (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (instruction : ServiceInstruction graph)
    (before after : (runtime.reactiveApplication leaks).Execution)
    (supported : after ∈ (runtime.interactionStep leaks players network instruction
      before).support) (who : Player) :
    before.recall who <+: after.recall who := by
  let app := runtime.reactiveApplication leaks
  obtain ⟨command, _selected, moved⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨activated, observed, responded⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ moved)
  have prior := app.environmentStep_recall before activated command observed
  cases actor : command.actor? app with
  | none =>
      change after ∈ (app.resume players (command.actor? app) activated).support at responded
      rw [actor] at responded
      cases FinDist.mem_support_pure.mp responded
      rw [prior]
  | some owner =>
      change after ∈ (app.resume players (command.actor? app) activated).support at responded
      rw [actor] at responded
      obtain ⟨response, _chosen, rfl⟩ := FinDist.support_map .. ▸ responded
      rw [← prior]
      exact app.respond_recall_prefix activated owner who response

theorem runInteractionPlan_recall_prefix (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (before after : (runtime.reactiveApplication leaks).Execution)
    (supported : after ∈ (runtime.runInteractionPlan leaks players network plan
      before).support) (who : Player) :
    before.recall who <+: after.recall who := by
  induction plan generalizing before with
  | nil => cases FinDist.mem_support_pure.mp supported; rfl
  | cons instruction rest ih =>
      obtain ⟨middle, stepped, continued⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      exact (runtime.interactionStep_recall_prefix leaks players network instruction
        before middle stepped who).trans (ih middle continued)

theorem runInteractionPlan_inputRecall
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (plan : List (ServiceInstruction graph))
    (initial final : (runtime.reactiveApplication leaks).Execution)
    (valid : initial.InputRecall (runtime.reactiveApplication leaks))
    (reached : final ∈ (runtime.runInteractionPlan leaks players network plan
      initial).support) : final.InputRecall (runtime.reactiveApplication leaks) := by
  let app := runtime.reactiveApplication leaks
  have preserved : app.PolicyInvariant players (fun execution => execution.InputRecall app) := {
    respond := fun execution who action valid _ =>
      app.respond_inputRecall execution who action valid
    environment := app.environment_inputRecall }
  exact runtime.runInteractionPlan_preserves leaks players network _ preserved plan
    initial final valid reached

end Vegas.EventGraphRuntime
