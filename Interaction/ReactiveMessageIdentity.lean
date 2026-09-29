/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageNetworkIdentity
import Interaction.ReactiveAllocation

/-! # Envelope identity at every raw runtime history -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

theorem messageIdentityInvariant (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler (fun execution =>
      execution.network.SerialsBeforeNext ∧ execution.network.UniqueIds) where
  respond execution who action valid := by
    refine ⟨(app.serialsBeforeNextInvariant scheduler).respond execution who action valid.1, ?_⟩
    rcases action with ⟨transmission⟩
    cases transmission with
    | none => exact valid.2
    | some transmission =>
        cases transmission with
        | replay id => exact valid.2.replay who id
        | submit material =>
            exact valid.2.submit valid.1 who
              (app.packet (app.submit execution.application who material) who
                (execution.network.known who) material)
  environment execution next command valid selected reached := by
    refine ⟨(app.serialsBeforeNextInvariant scheduler).environment execution next command
      valid.1 selected reached, ?_⟩
    cases command with
    | wait =>
        simp only [Execution.environmentStep, PMF.pure_map] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact valid.2
    | activate who =>
        obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
        obtain ⟨sample, _, rfl⟩ := PMF.support_map .. ▸ supported
        exact valid.2.learn who sample
    | «include» id =>
        simp only [Execution.environmentStep, PMF.pure_map] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        change (execution.includePending app id).network.UniqueIds
        rw [app.includePending_network]
        exact valid.2.includePending id
    | application command =>
        obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
        obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ supported
        exact valid.2

/-- Arbitrary submissions, replays, passive samples and scheduler choices all
preserve the full message under its identifier. -/
theorem uniqueIds_history (scheduler : app.Scheduler) (initial : PMF app.State)
    (horizon : Nat) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control)) :
    control.execution.network.UniqueIds :=
  ((app.messageIdentityInvariant scheduler).history initial horizon
    (fun _ _ => ⟨MessageNetwork.SerialsBeforeNext.empty, MessageNetwork.UniqueIds.empty⟩) trace).2

end Interaction.ReactiveApplication
