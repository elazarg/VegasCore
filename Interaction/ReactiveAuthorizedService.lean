/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSubmissionAudit

/-! # An observable submission-authorization monitor

The monitor replaces an unauthorized inclusion command with a wait. That wait
consumes the same service step; it does not include the envelope or create a
rejection receipt. Broadcasts, replay, activations, and passive observations
retain their existing semantics. This is an ideal service with public traffic
recall, not an implementation of ledger-verifiable submission certificates.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def SubmissionPermitted
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (history : List app.EnvironmentEntry) (message : Message Principal app.Payload) : Prop :=
  ∃ observation, app.submissionObservation? history message.id = some observation ∧
    condition observation message

theorem submissionPermitted_iff_authorized
    (project : app.LocalObservation → app.PublicObservation)
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (execution : app.Execution) (message : Message Principal app.Payload)
    (audited : execution.AuditedSubmission app project message) :
    app.SubmissionPermitted condition execution.environmentRecall message ↔
      execution.AuthorizedAtSubmission app
        (fun view packet => condition (project view.application) packet) message := by
  obtain ⟨entry, found, emitted, observed⟩ := audited
  rw [app.authorizedAtSubmission_iff _ execution message entry found]
  simp [SubmissionPermitted, observed, emitted]

/-- Inclusion is admitted only for the actual pending envelope and its original
public submission observation. An unknown identifier also becomes a wait. -/
def authorizedCommand
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (history : List app.EnvironmentEntry) (view : app.EnvironmentView) :
    app.Command → app.Command := by
  classical
  exact fun
  | .include id => match view.network.pending.find? (fun message => message.id = id) with
      | none => .wait
      | some message => if app.SubmissionPermitted condition history message
          then .include id else .wait
  | command => command

def authorizedScheduler
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (scheduler : app.Scheduler) : app.Scheduler :=
  fun history view => (scheduler history view).map (app.authorizedCommand condition history view)

theorem authorizedCommand_include
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (history : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (command : app.Command) (id : MessageId Principal)
    (included : app.authorizedCommand condition history view command = .include id) :
    command = .include id ∧ ∃ message,
      view.network.pending.find? (fun packet => packet.id = id) = some message ∧
        app.SubmissionPermitted condition history message := by
  cases command <;> simp only [authorizedCommand] at included
  all_goals try cases included
  case «include» prior =>
    split at included
    · cases included
    · rename_i message found
      split at included
      · cases included
        exact ⟨rfl, message, found, by assumption⟩
      · cases included

/-- Authorization never adds a new inclusion opportunity. -/
theorem authorizedScheduler_atMostOnce
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (scheduler : app.Scheduler) (once : app.AtMostOnce scheduler) :
    app.AtMostOnce (app.authorizedScheduler condition scheduler) := by
  intro history view id selected
  obtain ⟨command, supported, same⟩ := FinDist.support_map .. ▸ selected
  have original := (app.authorizedCommand_include condition history view command id same).1
  exact once history view id (original ▸ supported)

variable [Inhabited app.Memory]

/-- At an active response, a new envelope is checked against the current public
application observation. Earlier silent activations cannot make it premature. -/
theorem submissionPermitted_fresh_history
    (project : app.LocalObservation → app.PublicObservation)
    (agrees : ∀ state who, project (app.observePlayer state who) = app.observePublic state)
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (who : Principal) (active : control.actor = some who) (payload : app.Payload) :
    app.SubmissionPermitted condition control.execution.environmentRecall
        ⟨(who, control.execution.network.nextSerial who), payload⟩ ↔
      condition (app.observePublic control.execution.application)
        ⟨(who, control.execution.network.nextSerial who), payload⟩ := by
  have activated := (app.submissionAudit_history project agrees initial horizon scheduler
    trace).2 who active
  simp [SubmissionPermitted, activated]

/-- The public monitor enforces the private-recall specification at every legal
prefix, independently of earlier deviations, leaks, or scheduler adaptivity. -/
theorem authorizedScheduler_requiresAuthorization
    (project : app.LocalObservation → app.PublicObservation)
    (agrees : ∀ state who, project (app.observePlayer state who) = app.observePublic state)
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    app.RequiresSubmissionAuthorization
      (fun view message => condition (project view.application) message) initial horizon
      (app.authorizedScheduler condition scheduler) := by
  intro control trace _ _ message _ pending selected _
  obtain ⟨command, _, same⟩ := FinDist.support_map .. ▸ selected
  obtain ⟨_, found, equal, permitted⟩ := app.authorizedCommand_include condition
    control.execution.environmentRecall (control.execution.observeEnvironment app)
    command message.id same
  change control.execution.network.lookup message.id = some found at equal
  rw [pending] at equal
  cases Option.some.inj equal
  exact (app.submissionPermitted_iff_authorized project condition control.execution message
    ((app.submissionAudit_history project agrees initial horizon _ trace).1.lookup
      message.id message pending)).mp permitted

end Interaction.ReactiveApplication
