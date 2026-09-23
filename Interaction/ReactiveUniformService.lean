/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAuthorizedService
import Interaction.PendingSelection

/-! # Fixed service windows with authorized uniform inclusion

A calendar chooses activation, selection, application, and wait opportunities.
Each selection draws uniformly from authorized, distinct, unpublished identifiers
matching its fixed eligibility predicate. Empty selection consumes its turn as
a wait. The calendar is independent of player responses; observations remain
private samples of foreign pending traffic. Timing, completion, and incentives
of a particular calendar require separate application proofs.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def authorizedEligibility
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (history : List app.EnvironmentEntry) (eligible : Message Principal app.Payload → Bool)
    (message : Message Principal app.Payload) : Bool := by
  classical
  exact eligible message && decide (app.SubmissionPermitted condition history message)

def authorizedUniform
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (history : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (eligible : Message Principal app.Payload → Bool) : FinDist (Option (MessageId Principal)) :=
  MessageNetwork.uniformPending (fun message =>
    app.authorizedEligibility condition history eligible message &&
      !(view.network.ledger.any fun prior => prior.id = message.id)) view.network.pending

theorem authorizedUniform_supported
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (history : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (eligible : Message Principal app.Payload → Bool) (id : MessageId Principal)
    (supported : some id ∈ (app.authorizedUniform condition history view eligible).support) :
    ∃ message ∈ view.network.pending, message.id = id ∧ eligible message = true ∧
      app.SubmissionPermitted condition history message ∧ view.Unpublished app id := by
  obtain ⟨message, pending, allowed, same⟩ :=
    MessageNetwork.uniformPending_supported _ _ id supported
  simp only [authorizedEligibility, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at allowed
  refine ⟨message, pending, same, allowed.1.1, allowed.1.2, ?_⟩
  intro included
  obtain ⟨prior, member, identified⟩ := List.mem_map.mp included
  have seen : (view.network.ledger.any fun prior => prior.id = message.id) = true :=
    List.any_eq_true.mpr ⟨prior, member, by simp only [same, identified, decide_true]⟩
  have absent := allowed.2
  rw [seen] at absent
  cases absent

inductive UniformInstruction where
  | activate (who : Principal)
  | select (eligible : Message Principal app.Payload → Bool)
  | application (command : app.EnvironmentCommand)
  | wait

def uniformInstruction
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (history : List app.EnvironmentEntry) (view : app.EnvironmentView) :
    app.UniformInstruction → FinDist app.Command
  | .activate who => FinDist.pure (.activate who)
  | .select eligible => (app.authorizedUniform condition history view eligible).map
      (fun selected => selected.elim .wait .include)
  | .application command => FinDist.pure (.application command)
  | .wait => FinDist.pure .wait

def uniformScheduler
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (calendar : Nat → app.UniformInstruction) : app.Scheduler :=
  fun history view => app.uniformInstruction condition history view (calendar history.length)

theorem uniformInstruction_include
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (history : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (instruction : app.UniformInstruction) (id : MessageId Principal)
    (included : .include id ∈ (app.uniformInstruction condition history view instruction).support) :
    ∃ message ∈ view.network.pending, message.id = id ∧
      app.SubmissionPermitted condition history message ∧ view.Unpublished app id := by
  cases instruction with
  | activate who => cases FinDist.mem_support_pure.mp included
  | application command => cases FinDist.mem_support_pure.mp included
  | wait => cases FinDist.mem_support_pure.mp included
  | select eligible =>
      obtain ⟨selected, supported, same⟩ := FinDist.support_map .. ▸ included
      cases selected with
      | none => cases same
      | some candidate =>
          cases same
          obtain ⟨message, pending, identified, _, permitted, unpublished⟩ :=
            app.authorizedUniform_supported condition history view eligible id supported
          exact ⟨message, pending, identified, permitted, unpublished⟩

theorem uniformScheduler_atMostOnce
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (calendar : Nat → app.UniformInstruction) :
    app.AtMostOnce (app.uniformScheduler condition calendar) := by
  intro history view id supported
  obtain ⟨_, _, _, _, unpublished⟩ :=
    app.uniformInstruction_include condition history view _ id supported
  exact unpublished

variable [Inhabited app.Memory]

theorem uniformScheduler_requiresAuthorization
    (project : app.LocalObservation → app.PublicObservation)
    (agrees : ∀ state who, project (app.observePlayer state who) = app.observePublic state)
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (initial : FinDist app.State) (horizon : Nat) (calendar : Nat → app.UniformInstruction) :
    app.RequiresSubmissionAuthorization
      (fun view message => condition (project view.application) message) initial horizon
      (app.uniformScheduler condition calendar) := by
  intro control trace _ _ message _ pending selected _
  obtain ⟨candidate, member, identified, permitted, _⟩ := app.uniformInstruction_include condition
    control.execution.environmentRecall (control.execution.observeEnvironment app)
    _ message.id selected
  have audit := (app.submissionAudit_history project agrees initial horizon _ trace).1
  have current := audit.lookup message.id message pending
  have same := app.auditedSubmission_eq_of_id project control.execution candidate message
    (audit.pending candidate member) current identified
  subst candidate
  exact (app.submissionPermitted_iff_authorized project condition control.execution message
    current).mp permitted

end Interaction.ReactiveApplication
