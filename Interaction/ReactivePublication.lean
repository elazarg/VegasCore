/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessagePublication
import Interaction.ReactiveServiceInvariant

/-! # At-most-once inclusion as a service contract

The carrier permits rebroadcasts. A service may consume each envelope identifier
at most once, including when the application rejects its call. This restriction
uses the public ledger only. It does not restrict player responses, fresh retries,
or private observation of pending messages.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def EnvironmentView.Unpublished (view : app.EnvironmentView) (id : MessageId Principal) : Prop :=
  id ∉ view.network.ledger.map Message.id

instance (view : app.EnvironmentView) (id : MessageId Principal) :
    Decidable (view.Unpublished app id) := inferInstanceAs (Decidable (_ ∉ _))

/-- An attempted second inclusion consumes a service turn without applying the call. -/
def atMostOnceCommand (view : app.EnvironmentView) : app.Command → app.Command
  | .include id => if view.Unpublished app id then .include id else .wait
  | command => command

def AtMostOnce (scheduler : app.Scheduler) : Prop :=
  ∀ history view id, (.include id) ∈ (scheduler history view).support →
    view.Unpublished app id

theorem atMostOnceCommand_fresh (view : app.EnvironmentView) (command : app.Command)
    (id : MessageId Principal) (included : app.atMostOnceCommand view command = .include id) :
    view.Unpublished app id := by
  cases command <;> simp only [atMostOnceCommand] at included
  all_goals try cases included
  case «include» prior =>
    split at included
    · cases included; assumption
    · cases included

theorem includePending_network (execution : app.Execution) (id : MessageId Principal) :
    (execution.includePending app id).network = (execution.network.includePending id).2 := by
  cases found : execution.network.lookup id <;>
    simp only [Execution.includePending, MessageNetwork.includePending, found]

theorem pendingOrPublishedInvariant (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler (fun execution => execution.network.PendingOrPublished) where
  respond execution who action valid := by
    rcases action with ⟨transmission⟩
    cases transmission with
    | none => exact valid
    | some transmission =>
        cases transmission with
        | submit submission =>
            exact valid.submit who
              (app.packet (app.submit execution.application who submission) who
                (execution.network.known who) submission)
        | replay id => exact valid.replay who id
  environment execution next command valid _ reached := by
    cases command with
    | wait =>
        simp only [Execution.environmentStep, FinDist.map_pure] at reached
        cases FinDist.mem_support_pure.mp reached
        exact valid
    | activate who =>
        obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
        obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
        exact valid.learn who selected
    | «include» id =>
        simp only [Execution.environmentStep, FinDist.map_pure] at reached
        cases FinDist.mem_support_pure.mp reached
        change (execution.includePending app id).network.PendingOrPublished
        rw [app.includePending_network]
        exact valid.includePending id
    | application command =>
        obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
        obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ supported
        exact valid

theorem publishedOnceInvariant (scheduler : app.Scheduler) (once : app.AtMostOnce scheduler) :
    app.ServiceInvariant scheduler (fun execution => execution.network.PublishedOnce) where
  respond execution who action valid := by
    rcases action with ⟨transmission⟩
    cases transmission with
    | none => exact valid
    | some transmission =>
        cases transmission with
        | submit submission =>
            exact valid.submit who
              (app.packet (app.submit execution.application who submission) who
                (execution.network.known who) submission)
        | replay id => exact valid.replay who id
  environment execution next command valid selected reached := by
    cases command with
    | wait =>
        simp only [Execution.environmentStep, FinDist.map_pure] at reached
        cases FinDist.mem_support_pure.mp reached
        exact valid
    | activate who =>
        obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
        obtain ⟨observations, _, rfl⟩ := FinDist.support_map .. ▸ supported
        exact valid.learn who observations
    | «include» id =>
        simp only [Execution.environmentStep, FinDist.map_pure] at reached
        cases FinDist.mem_support_pure.mp reached
        change (execution.includePending app id).network.PublishedOnce
        rw [app.includePending_network]
        exact valid.includePending id (once _ _ id selected)
    | application command =>
        obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
        obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ supported
        exact valid

theorem pendingOrPublished_history (scheduler : app.Scheduler)
    (initial : FinDist app.State) (horizon : Nat) {state : app.ProtocolState}
    (trace : (app.protocol initial horizon scheduler).Trace state) :
    serviceInvariant (fun execution => execution.network.PendingOrPublished) state :=
  (app.pendingOrPublishedInvariant scheduler).history initial horizon
    (fun _ _ => MessageNetwork.PendingOrPublished.empty) trace

theorem publishedOnce_history (scheduler : app.Scheduler) (once : app.AtMostOnce scheduler)
    (initial : FinDist app.State) (horizon : Nat) {state : app.ProtocolState}
    (trace : (app.protocol initial horizon scheduler).Trace state) :
    serviceInvariant (fun execution => execution.network.PublishedOnce) state :=
  (app.publishedOnceInvariant scheduler once).history initial horizon
    (fun _ _ => MessageNetwork.PublishedOnce.empty) trace

/-- At every initialized legal history, any rebroadcast leaves the set of
unpublished eligible identifiers unchanged. No player honesty is assumed. -/
theorem replay_unpublished_history (scheduler : app.Scheduler)
    (initial : FinDist app.State) (horizon : Nat) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (eligible : Message Principal app.Payload → Bool) (who : Principal)
    (id : MessageId Principal) :
    MessageNetwork.eligibleIds
        ((control.execution.network.replay who id).2.unpublished eligible)
        (control.execution.network.replay who id).2.pending =
      MessageNetwork.eligibleIds (control.execution.network.unpublished eligible)
        control.execution.network.pending :=
  (app.pendingOrPublished_history scheduler initial horizon trace).replay_unpublished_ids
    eligible who id

end Interaction.ReactiveApplication
