/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.MessagePublication
import Interaction.ReactiveEnvironmentStep
import Interaction.ReactiveServiceInvariant

/-! # At-most-once inclusion as a service contract

A service may consume each envelope identifier at most once, including when
the application rejects its call. This restriction uses the public ledger only.
It does not restrict player responses, fresh retries, or private observation of
pending messages.
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

theorem includePending_network (execution : app.Execution) (id : MessageId Principal) :
    (execution.includePending app id).network = (execution.network.includePending id).2 := by
  cases found : execution.network.lookup id <;>
    simp only [Execution.includePending, MessageNetwork.includePending, found]

/-- Player responses may submit envelopes but do not include them in the
ledger. Inclusion is a separate environment action. -/
theorem respond_ledger (execution : app.Execution) (who : Principal) (action : app.Action) :
    (execution.respond app who action).network.ledger = execution.network.ledger := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some submission => rfl

theorem pendingOrPublishedInvariant (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler (fun execution => execution.network.PendingOrPublished) where
  respond execution who action valid := by
    rcases action with ⟨transmission⟩
    cases transmission with
    | none => exact valid
    | some submission =>
        exact valid.submit who
          (app.packet (app.submit execution.application who submission) who
            (execution.network.known who) submission)
  environment execution next command valid _ reached := by
    apply app.environmentStep_cases execution next command reached
      (predicate := fun _ next => next.network.PendingOrPublished)
    · exact valid
    · exact fun who selected _ => valid.learn who selected
    · intro id
      change (execution.includePending app id).network.PendingOrPublished
      rw [app.includePending_network]
      exact valid.includePending id
    · exact fun _ _ _ => valid

theorem pendingOrPublished_history (scheduler : app.Scheduler)
    (initial : PMF app.State) (horizon : Nat) {state : app.ProtocolState}
    (trace : (app.protocol initial horizon scheduler).Trace state) :
    serviceInvariant (fun execution => execution.network.PendingOrPublished) state :=
  (app.pendingOrPublishedInvariant scheduler).history initial horizon
    (fun _ _ => MessageNetwork.PendingOrPublished.empty) trace

end Interaction.ReactiveApplication
