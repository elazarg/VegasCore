/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetworkCounters
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
    | some transmission =>
        cases transmission with
        | submit submission => exact valid.submit who (app.packet submission)
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
        change (execution.includePending app id).network.SerialsBeforeNext
        rw [app.includePending_network]
        exact valid.includePending id
    | application command =>
        obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
        obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ supported
        exact valid

theorem serialsBeforeNext_history (scheduler : app.Scheduler)
    (initial : FinDist app.State) (horizon : Nat) {state : app.ProtocolState}
    (trace : (app.protocol initial horizon scheduler).Trace state) :
    serviceInvariant (fun execution => execution.network.SerialsBeforeNext) state :=
  (app.serialsBeforeNextInvariant scheduler).history initial horizon
    (fun _ _ => MessageNetwork.SerialsBeforeNext.empty) trace

end Interaction.ReactiveApplication
