/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveHistory
import Interaction.ReactiveProvenance
import Interaction.ReactiveAllocation

/-! # Authorization at an envelope's original submission

Authorization refers to the first actual submission of an identifier, using
the recorded pre-submission view. It cannot be renewed by replay, later
application changes, or private memory. The acceptance contract is a semantic
obligation on a service, not permission for a scheduler to inspect private
recall. A concrete certificate implementation must establish that obligation.
All player responses and passive observations remain available.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def PlayerEntry.submitsId (entry : app.PlayerEntry) (id : MessageId Principal) : Bool :=
  match entry.action.transmission with
  | some (.submit _) => entry.emitted.any fun message => message.id = id
  | _ => false

/-- The first submission, rather than the most recent transmission or replay. -/
def Execution.submissionOrigin? (execution : app.Execution) (id : MessageId Principal) :
    Option app.PlayerEntry :=
  (execution.recall id.1).find? fun entry => entry.submitsId app id

/-- The condition is checked against the author's view before the original
submission. Equality of envelopes also authenticates the payload being checked. -/
def Execution.AuthorizedAtSubmission
    (condition : app.PlayerView → Message Principal app.Payload → Prop)
    (execution : app.Execution) (message : Message Principal app.Payload) : Prop :=
  ∃ entry, execution.submissionOrigin? app message.id = some entry ∧
    entry.emitted = some message ∧ condition entry.beforeView message

theorem submissionOrigin_emitted (execution : app.Execution) (id : MessageId Principal)
    (entry : app.PlayerEntry) (found : execution.submissionOrigin? app id = some entry) :
    ∃ message, entry.emitted = some message ∧ message.id = id := by
  have selected := List.find?_some found
  cases choice : entry.action.transmission with
  | none => simp [PlayerEntry.submitsId, choice] at selected
  | some transmitted =>
      cases transmitted with
      | replay prior => simp [PlayerEntry.submitsId, choice] at selected
      | submit material =>
          cases emitted : entry.emitted with
          | none => simp [PlayerEntry.submitsId, choice, emitted] at selected
          | some message =>
              exact ⟨message, rfl, by
                simpa [PlayerEntry.submitsId, choice, emitted] using selected⟩

/-- A newly allocated identifier has no earlier submission origin. -/
theorem submissionOrigin_next_none (execution : app.Execution) (who : Principal)
    (recall : execution.InputRecall app) (serials : execution.network.SerialsBeforeNext) :
    execution.submissionOrigin? app (who, execution.network.nextSerial who) = none := by
  cases found : execution.submissionOrigin? app (who, execution.network.nextSerial who) with
  | none => rfl
  | some entry =>
      obtain ⟨message, emitted, identified⟩ := app.submissionOrigin_emitted execution _ entry found
      have output : message ∈ app.outputs (execution.recall who) :=
        List.mem_filterMap.mpr ⟨entry, List.mem_of_find?_eq_some found, emitted⟩
      rw [← recall who] at output
      obtain ⟨input, member, same⟩ := List.mem_filterMap.mp output
      split at same
      · have bound := serials.inputs input member
        have equal := Option.some.inj same
        change input.envelope.id.2 < execution.network.nextSerial input.envelope.id.1 at bound
        rw [equal, identified] at bound
        exact False.elim (Nat.lt_irrefl _ bound)
      · cases same

theorem submissionOrigin_prefix (before after : app.Execution) (id : MessageId Principal)
    (entry : app.PlayerEntry) (retained : before.recall id.1 <+: after.recall id.1)
    (found : before.submissionOrigin? app id = some entry) :
    after.submissionOrigin? app id = some entry := by
  obtain ⟨suffix, same⟩ := retained
  simp only [Execution.submissionOrigin?, ← same, List.find?_append]
  change (before.submissionOrigin? app id).or _ = _
  rw [found]
  rfl

theorem submissionOrigin_respond (execution : app.Execution) (who : Principal)
    (action : app.Action) (id : MessageId Principal) (entry : app.PlayerEntry)
    (found : execution.submissionOrigin? app id = some entry) :
    (execution.respond app who action).submissionOrigin? app id = some entry :=
  app.submissionOrigin_prefix execution _ id entry
    (app.respond_recall_prefix execution who id.1 action) found

theorem submissionOrigin_environment (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support)
    (id : MessageId Principal) :
    next.submissionOrigin? app id = execution.submissionOrigin? app id := by
  simp only [Execution.submissionOrigin?, app.environmentStep_recall execution next command reached]

theorem authorizedAtSubmission_iff
    (condition : app.PlayerView → Message Principal app.Payload → Prop)
    (execution : app.Execution) (message : Message Principal app.Payload) (entry : app.PlayerEntry)
    (found : execution.submissionOrigin? app message.id = some entry) :
    execution.AuthorizedAtSubmission app condition message ↔
      entry.emitted = some message ∧ condition entry.beforeView message := by
  simp [Execution.AuthorizedAtSubmission, found]

theorem submissionOrigin_submit (execution : app.Execution) (who : Principal)
    (memory : app.Memory) (material : app.Submission)
    (fresh : execution.submissionOrigin? app (who, execution.network.nextSerial who) = none) :
    (execution.respond app who ⟨memory, some (.submit material)⟩).submissionOrigin? app
      (who, execution.network.nextSerial who) =
        some ⟨execution.observe app who, ⟨memory, some (.submit material)⟩,
          some ⟨(who, execution.network.nextSerial who), app.packet material⟩⟩ := by
  simp only [Execution.submissionOrigin?] at fresh ⊢
  simp only [Execution.respond, MessageNetwork.submit, ↓reduceIte, List.find?_append, fresh]
  simp [PlayerEntry.submitsId]

/-- Authorization admits fresh packets submitted after the condition holds.
This does not assert that a scheduler will include them. -/
theorem authorizedAtSubmission_submit
    (condition : app.PlayerView → Message Principal app.Payload → Prop)
    (execution : app.Execution) (who : Principal) (memory : app.Memory) (material : app.Submission)
    (fresh : execution.submissionOrigin? app (who, execution.network.nextSerial who) = none)
    (allowed : condition (execution.observe app who)
      ⟨(who, execution.network.nextSerial who), app.packet material⟩) :
    (execution.respond app who ⟨memory, some (.submit material)⟩).AuthorizedAtSubmission
      app condition ⟨(who, execution.network.nextSerial who), app.packet material⟩ :=
  ⟨_, app.submissionOrigin_submit execution who memory material fresh, rfl, allowed⟩

variable [Inhabited app.Memory]

theorem submissionOrigin_next_none_history (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control)) (who : Principal) :
    control.execution.submissionOrigin? app
      (who, control.execution.network.nextSerial who) = none :=
  app.submissionOrigin_next_none control.execution who
    (app.history_inputRecall initial horizon scheduler trace)
    (app.serialsBeforeNext_history scheduler initial horizon trace)

theorem submissionOrigin_reaches (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler)
    {first last : (app.protocol initial horizon scheduler).History} {fuel : Nat}
    (path : (app.protocol initial horizon scheduler).ReachesWithin fuel first last)
    (before after : app.Control) (firstEq : first.state = some before)
    (lastEq : last.state = some after) (id : MessageId Principal) (entry : app.PlayerEntry)
    (found : before.execution.submissionOrigin? app id = some entry) :
    after.execution.submissionOrigin? app id = some entry :=
  app.submissionOrigin_prefix before.execution after.execution id entry
    (app.reaches_recall_prefix initial horizon scheduler path before after firstEq lastEq id.1)
    found

/-- A fixed envelope's authorization cannot change along any legal suffix,
even when the application condition later becomes true. -/
theorem authorizedAtSubmission_reaches_iff
    (condition : app.PlayerView → Message Principal app.Payload → Prop)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    {first last : (app.protocol initial horizon scheduler).History} {fuel : Nat}
    (path : (app.protocol initial horizon scheduler).ReachesWithin fuel first last)
    (before after : app.Control) (firstEq : first.state = some before)
    (lastEq : last.state = some after) (message : Message Principal app.Payload)
    (entry : app.PlayerEntry)
    (found : before.execution.submissionOrigin? app message.id = some entry) :
    after.execution.AuthorizedAtSubmission app condition message ↔
      before.execution.AuthorizedAtSubmission app condition message := by
  rw [app.authorizedAtSubmission_iff condition _ message entry
    (app.submissionOrigin_reaches initial horizon scheduler path before after firstEq lastEq
      message.id entry found), app.authorizedAtSubmission_iff condition _ message entry found]

/-- A semantic service contract at every initialized legal prefix. It constrains
successful application effects; rejected inclusions, raw transmissions, and
passive observations remain legal. Implementation requires observable evidence
of the original submission condition, not access to this proof's private recall. -/
def RequiresSubmissionAuthorization
    (condition : app.PlayerView → Message Principal app.Payload → Prop)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler) : Prop :=
  ∀ (control : app.Control),
    (app.protocol initial horizon scheduler).Trace (some control) →
    control.actor = none →
    0 < control.remaining →
    ∀ (message : Message Principal app.Payload) (next : app.State),
      control.execution.network.lookup message.id = some message →
      .include message.id ∈ (scheduler control.execution.environmentRecall
        (control.execution.observeEnvironment app)).support →
      app.handle control.execution.application message = some next →
      control.execution.AuthorizedAtSubmission app condition message

/-- Under the contract, an unauthorized envelope can never be accepted later.
New submissions with new identifiers remain possible. -/
theorem unauthorized_not_accepted
    (condition : app.PlayerView → Message Principal app.Payload → Prop)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (contract : app.RequiresSubmissionAuthorization condition initial horizon scheduler)
    {first last : (app.protocol initial horizon scheduler).History} {fuel : Nat}
    (path : (app.protocol initial horizon scheduler).ReachesWithin fuel first last)
    (before after : app.Control) (firstEq : first.state = some before)
    (lastEq : last.state = some after) (inactive : after.actor = none)
    (running : 0 < after.remaining)
    (message : Message Principal app.Payload) (entry : app.PlayerEntry)
    (found : before.execution.submissionOrigin? app message.id = some entry)
    (denied : ¬before.execution.AuthorizedAtSubmission app condition message)
    (pending : after.execution.network.lookup message.id = some message)
    (selected : .include message.id ∈ (scheduler after.execution.environmentRecall
      (after.execution.observeEnvironment app)).support) :
    app.handle after.execution.application message = none := by
  cases effect : app.handle after.execution.application message with
  | none => rfl
  | some next =>
      have trace : (app.protocol initial horizon scheduler).Trace (some after) :=
        lastEq ▸ last.trace
      exact False.elim (denied ((app.authorizedAtSubmission_reaches_iff condition initial horizon
        scheduler path before after firstEq lastEq message entry found).mp
          (contract after trace inactive running message next pending selected effect)))

end Interaction.ReactiveApplication
