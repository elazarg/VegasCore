/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSubmissionAudit
import Interaction.ReactiveRounds

/-! # Submission identity throughout the reactive round evaluator

Each dispatch records an activation before invoking its response. This is the
same freshness argument as for protocol histories, exposed for the exact round
evaluator used by concrete services. Arbitrary player policies are allowed.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

theorem submissionAudit_dispatch (project : app.LocalObservation → app.PublicObservation)
    (agrees : ∀ state who, project (app.observePlayer state who) = app.observePublic state)
    (players : Principal → app.Policy) (command : app.Command)
    (execution next : app.Execution) (audit : execution.SubmissionAudit app project)
    (recall : execution.InputRecall app) (serials : execution.network.SerialsBeforeNext)
    (reached : next ∈ (app.dispatch players command execution).support) :
    next.SubmissionAudit app project ∧ next.InputRecall app ∧
      next.network.SerialsBeforeNext := by
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  have middleAudit := app.submissionAudit_environment project execution middle command moved
    audit serials
  have middleRecall := app.environment_inputRecall execution middle command recall moved
  have middleSerials :=
    (app.serialsBeforeNextInvariant (fun _ _ => FinDist.pure command)).environment
    execution middle command serials (FinDist.mem_support_pure.mpr rfl) moved
  cases active : command.actor? app with
  | none =>
      simp only [resume, active] at resumed
      cases FinDist.mem_support_pure.mp resumed
      exact ⟨middleAudit, middleRecall, middleSerials⟩
  | some who =>
      simp only [resume, active] at resumed
      obtain ⟨action, _, rfl⟩ := FinDist.support_map .. ▸ resumed
      exact ⟨app.submissionAudit_respond project agrees middle who action middleAudit
        (app.submissionOrigin_next_none middle who middleRecall middleSerials)
        (app.activationAudit_environment execution middle command moved 0 who active),
        app.respond_inputRecall middle who action middleRecall,
        (app.serialsBeforeNextInvariant (fun _ _ => FinDist.pure .wait)).respond
          middle who action middleSerials⟩

theorem submissionAudit_runRounds (project : app.LocalObservation → app.PublicObservation)
    (agrees : ∀ state who, project (app.observePlayer state who) = app.observePublic state)
    (scheduler : app.Scheduler) (players : Principal → app.Policy) (count : Nat)
    (execution next : app.Execution) (audit : execution.SubmissionAudit app project)
    (recall : execution.InputRecall app) (serials : execution.network.SerialsBeforeNext)
    (reached : next ∈ (app.runRounds scheduler players count execution).support) :
    next.SubmissionAudit app project ∧ next.InputRecall app ∧
      next.network.SerialsBeforeNext := by
  induction count generalizing execution with
  | zero =>
      cases FinDist.mem_support_pure.mp reached
      exact ⟨audit, recall, serials⟩
  | succ count ih =>
      obtain ⟨middle, stepped, rest⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ stepped)
      obtain ⟨middleAudit, middleRecall, middleSerials⟩ := app.submissionAudit_dispatch project
        agrees players command execution middle audit recall serials dispatched
      exact ih middle middleAudit middleRecall middleSerials rest

end Interaction.ReactiveApplication
