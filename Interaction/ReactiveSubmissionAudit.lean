/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAuthorization

/-! # Recovering submission observations from public activation history

An activation records the public application observation and the next envelope
serial. Exactly one response follows it. For an issued identifier, the last
matching activation is therefore its original submission observation. Silence
may replace a tentative observation; submission advances the serial permanently.
The reconstruction uses neither private recall nor passive observation samples.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def EnvironmentEntry.activationObservation? (entry : app.EnvironmentEntry)
    (id : MessageId Principal) : Option app.PublicObservation :=
  match entry.command with
  | .activate who => if who = id.1 ∧ entry.beforeView.network.nextSerial who = id.2
      then some entry.beforeView.application else none
  | _ => none

/-- The most recent activation at the identifier's allocation counter. -/
def submissionObservation? (history : List app.EnvironmentEntry) (id : MessageId Principal) :
    Option app.PublicObservation :=
  history.foldl (fun prior entry => (entry.activationObservation? app id).or prior) none

theorem submissionObservation_append (history : List app.EnvironmentEntry)
    (entry : app.EnvironmentEntry) (id : MessageId Principal) :
    app.submissionObservation? (history ++ [entry]) id =
      (entry.activationObservation? app id).or (app.submissionObservation? history id) := by
  simp [submissionObservation?, List.foldl_append]

theorem activationObservation_issued (execution : app.Execution) (command : app.Command)
    (id : MessageId Principal) (issued : id.2 < execution.network.nextSerial id.1) :
    (⟨execution.observeEnvironment app, command⟩ : app.EnvironmentEntry).activationObservation?
      app id = none := by
  cases command <;> simp only [EnvironmentEntry.activationObservation?]
  case activate who =>
    split
    · rename_i same
      simp only [Execution.observeEnvironment, MessageNetwork.publicView] at same
      rw [← same.1, same.2] at issued
      exact (Nat.lt_irrefl _ issued).elim
    · rfl

def Execution.AuditedSubmission (project : app.LocalObservation → app.PublicObservation)
    (execution : app.Execution) (message : Message Principal app.Payload) : Prop :=
  ∃ entry, execution.submissionOrigin? app message.id = some entry ∧
    entry.emitted = some message ∧
    app.submissionObservation? execution.environmentRecall message.id =
      some (project entry.beforeView.application)

def Execution.SubmissionAudit (project : app.LocalObservation → app.PublicObservation)
    (execution : app.Execution) : Prop :=
  execution.network.Satisfies (execution.AuditedSubmission app project)

theorem auditedSubmission_eq_of_id
    (project : app.LocalObservation → app.PublicObservation) (execution : app.Execution)
    (first second : Message Principal app.Payload)
    (left : execution.AuditedSubmission app project first)
    (right : execution.AuditedSubmission app project second) (same : first.id = second.id) :
    first = second := by
  obtain ⟨firstEntry, firstFound, firstEmitted, _⟩ := left
  obtain ⟨secondEntry, secondFound, secondEmitted, _⟩ := right
  rw [same, secondFound] at firstFound
  cases Option.some.inj firstFound
  exact Option.some.inj (firstEmitted.symm.trans secondEmitted)

/-- An audited pending envelope is recovered exactly by its identifier, even
when rebroadcasting has left several copies in the pending list. -/
theorem Execution.SubmissionAudit.lookup_of_mem
    (project : app.LocalObservation → app.PublicObservation) (execution : app.Execution)
    (audit : execution.SubmissionAudit app project) (message : Message Principal app.Payload)
    (pending : message ∈ execution.network.pending) :
    execution.network.lookup message.id = some message := by
  cases found : execution.network.lookup message.id with
  | none =>
      have excluded := List.find?_eq_none.mp found message pending
      simp at excluded
  | some selected =>
      have same : selected.id = message.id := by
        simpa only [decide_eq_true_eq] using List.find?_some found
      exact congrArg some (app.auditedSubmission_eq_of_id project execution selected message
        (audit.lookup message.id selected found) (audit.pending message pending) same)

def Control.ActivationAudit (control : app.Control) : Prop :=
  ∀ who, control.actor = some who →
    app.submissionObservation? control.execution.environmentRecall
      (who, control.execution.network.nextSerial who) =
        some (app.observePublic control.execution.application)

theorem auditedSubmission_respond (project : app.LocalObservation → app.PublicObservation)
    (execution : app.Execution) (who : Principal) (action : app.Action)
    (message : Message Principal app.Payload)
    (valid : execution.AuditedSubmission app project message) :
    (execution.respond app who action).AuditedSubmission app project message := by
  obtain ⟨entry, found, emitted, observed⟩ := valid
  refine ⟨entry, app.submissionOrigin_respond execution who action message.id entry found,
    emitted, ?_⟩
  rw [app.respond_environmentRecall]
  exact observed

theorem submissionAudit_respond (project : app.LocalObservation → app.PublicObservation)
    (agrees : ∀ state who, project (app.observePlayer state who) = app.observePublic state)
    (execution : app.Execution) (who : Principal) (action : app.Action)
    (valid : execution.SubmissionAudit app project)
    (fresh : execution.submissionOrigin? app (who, execution.network.nextSerial who) = none)
    (activated : app.submissionObservation? execution.environmentRecall
      (who, execution.network.nextSerial who) = some (app.observePublic execution.application)) :
    (execution.respond app who action).SubmissionAudit app project := by
  have prior := valid.mono (app.auditedSubmission_respond project execution who action)
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact prior
  | some transmission =>
      cases transmission with
      | replay id => exact prior.replay who id
      | submit material =>
          apply prior.submit who
            (app.packet (app.submit execution.application who material) who
              (execution.network.known who) material)
          refine ⟨_, app.submissionOrigin_submit execution who material fresh, rfl, ?_⟩
          rw [app.respond_environmentRecall]
          simpa only [Execution.observe, agrees] using activated

theorem submissionObservation_environment (execution next : app.Execution)
    (command : app.Command) (reached : next ∈ (execution.environmentStep app command).support)
    (id : MessageId Principal) (issued : id.2 < execution.network.nextSerial id.1) :
    app.submissionObservation? next.environmentRecall id =
      app.submissionObservation? execution.environmentRecall id := by
  obtain ⟨updated, _, rfl⟩ := FinDist.support_map .. ▸ reached
  rw [app.submissionObservation_append,
    app.activationObservation_issued execution command id issued]
  rfl

theorem submissionAudit_environment (project : app.LocalObservation → app.PublicObservation)
    (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support)
    (valid : execution.SubmissionAudit app project)
    (serials : execution.network.SerialsBeforeNext) : next.SubmissionAudit app project := by
  have prior : execution.network.Satisfies (next.AuditedSubmission app project) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals
      intros
      obtain ⟨entry, found, emitted, observed⟩ := by
        first | apply valid.pending; assumption | apply valid.ledger; assumption
              | apply valid.leaked; assumption | apply valid.inputs; assumption
      refine ⟨entry, ?_, emitted, ?_⟩
      · rw [app.submissionOrigin_environment execution next command reached]
        exact found
      · rw [app.submissionObservation_environment execution next command reached]
        · exact observed
        · first | apply serials.pending; assumption | apply serials.ledger; assumption
                | apply serials.leaked; assumption | apply serials.inputs; assumption
  cases command with
  | wait =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact prior
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact prior.learn who selected
  | «include» id =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      change (execution.includePending app id).network.Satisfies _
      rw [app.includePending_network]
      exact prior.includePending id
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact prior

theorem activationAudit_environment (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support) (remaining : Nat) :
    (⟨remaining, command.actor? app, next⟩ : app.Control).ActivationAudit app := by
  intro who active
  cases command <;> try cases active
  case activate actor =>
    obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
    obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
    rw [submissionObservation_append]
    simp [EnvironmentEntry.activationObservation?, Execution.observeEnvironment,
      MessageNetwork.publicView, MessageNetwork.learn]

def submissionAudit (project : app.LocalObservation → app.PublicObservation) :
    app.ProtocolState → Prop
  | none => True
  | some control => control.execution.SubmissionAudit app project ∧ control.ActivationAudit app

theorem submissionAudit_transition (project : app.LocalObservation → app.PublicObservation)
    (agrees : ∀ state who, project (app.observePlayer state who) = app.observePublic state)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (before after : app.ProtocolState) (joint : Principal → Option app.Action)
    (trace : (app.protocol initial horizon scheduler).Trace before)
    (valid : app.submissionAudit project before)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    app.submissionAudit project after := by
  cases before with
  | none =>
      obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ reached
      exact ⟨MessageNetwork.Satisfies.empty, by intro who impossible; cases impossible⟩
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases FinDist.mem_support_pure.mp reached
          exact ⟨app.submissionAudit_respond project agrees execution who _ valid.1
            (app.submissionOrigin_next_none_history initial horizon scheduler _ trace who)
            (valid.2 who rfl), by intro observer impossible; cases impossible⟩
      | none =>
          cases remaining with
          | zero => cases FinDist.mem_support_pure.mp reached; exact valid
          | succ remaining =>
              obtain ⟨command, _, supported⟩ :=
                Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
              obtain ⟨next, moved, rfl⟩ := FinDist.support_map .. ▸ supported
              exact ⟨app.submissionAudit_environment project execution next command moved valid.1
                (app.serialsBeforeNext_history scheduler initial horizon trace),
                app.activationAudit_environment execution next command moved remaining⟩

/-- Public reconstruction is exact at every legal prefix, after arbitrary
player responses and arbitrary supported scheduler decisions. -/
theorem submissionAudit_history (project : app.LocalObservation → app.PublicObservation)
    (agrees : ∀ state who, project (app.observePlayer state who) = app.observePublic state)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    ∀ {state} (_trace : (app.protocol initial horizon scheduler).Trace state),
      app.submissionAudit project state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      app.submissionAudit_transition project agrees initial horizon scheduler _ _ joint prior
        (submissionAudit_history project agrees initial horizon scheduler prior) reached

end Interaction.ReactiveApplication
