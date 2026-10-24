/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.MessageNetworkCounters
import Interaction.ReactiveEnvironmentStep
import Interaction.ReactivePublication

/-! # Every legal reactive prefix retains a fresh envelope identifier -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

theorem serialsBeforeNextInvariant (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler (fun execution => execution.network.SerialsBeforeNext) where
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
      (predicate := fun _ next => next.network.SerialsBeforeNext)
    · exact valid
    · exact fun who selected _ => valid.learn who selected
    · intro id
      change (execution.includePending app id).network.SerialsBeforeNext
      rw [app.includePending_network]
      exact valid.includePending id
    · exact fun _ _ _ => valid

theorem serialsBeforeNext_history (scheduler : app.Scheduler)
    (initial : PMF app.State) (horizon : Nat) {state : app.ProtocolState}
    (trace : (app.protocol initial horizon scheduler).Trace state) :
    serviceInvariant (fun execution => execution.network.SerialsBeforeNext) state :=
  (app.serialsBeforeNextInvariant scheduler).history initial horizon
    (fun _ _ => MessageNetwork.SerialsBeforeNext.empty) trace

end Interaction.ReactiveApplication
