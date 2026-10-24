/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.MessageNetworkIdentity
import Interaction.ReactiveAllocation
import Interaction.ReactiveEnvironmentStep

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
    | some material =>
        exact valid.2.submit valid.1 who
          (app.packet (app.submit execution.application who material) who
            (execution.network.known who) material)
  environment execution next command valid selected reached := by
    refine ⟨(app.serialsBeforeNextInvariant scheduler).environment execution next command
      valid.1 selected reached, ?_⟩
    apply app.environmentStep_cases execution next command reached
      (predicate := fun _ next => next.network.UniqueIds)
    · exact valid.2
    · exact fun who sample _ => valid.2.learn who sample
    · intro id
      change (execution.includePending app id).network.UniqueIds
      rw [app.includePending_network]
      exact valid.2.includePending id
    · exact fun _ _ _ => valid.2

/-- Arbitrary submissions, passive samples and scheduler choices all preserve
the full message under its identifier. -/
theorem uniqueIds_history (scheduler : app.Scheduler) (initial : PMF app.State)
    (horizon : Nat) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control)) :
    control.execution.network.UniqueIds :=
  ((app.messageIdentityInvariant scheduler).history initial horizon
    (fun _ _ => ⟨MessageNetwork.SerialsBeforeNext.empty, MessageNetwork.UniqueIds.empty⟩) trace).2

theorem idsDistinctInvariant (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler (fun execution =>
      execution.network.SerialsBeforeNext ∧ execution.network.IdsDistinct) where
  respond execution who action valid := by
    refine ⟨(app.serialsBeforeNextInvariant scheduler).respond execution who action valid.1, ?_⟩
    rcases action with ⟨transmission⟩
    cases transmission with
    | none => exact valid.2
    | some material =>
        exact valid.2.submit valid.1 who
          (app.packet (app.submit execution.application who material) who
            (execution.network.known who) material)
  environment execution next command valid selected reached := by
    refine ⟨(app.serialsBeforeNextInvariant scheduler).environment execution next command
      valid.1 selected reached, ?_⟩
    apply app.environmentStep_cases execution next command reached
      (predicate := fun _ next => next.network.IdsDistinct)
    · exact valid.2
    · exact fun who sample _ => valid.2.learn who sample
    · intro id
      change (execution.includePending app id).network.IdsDistinct
      rw [app.includePending_network]
      exact valid.2.includePending id
    · exact fun _ _ _ => valid.2

/-- At every reachable history, under every scheduler and arbitrary player
responses, no identifier is pending twice, published twice, or both. -/
theorem idsDistinct_history (scheduler : app.Scheduler) (initial : PMF app.State)
    (horizon : Nat) {state : app.ProtocolState}
    (trace : (app.protocol initial horizon scheduler).Trace state) :
    serviceInvariant (fun execution => execution.network.IdsDistinct) state := by
  have both := (app.idsDistinctInvariant scheduler).history initial horizon
    (fun _ _ => ⟨MessageNetwork.SerialsBeforeNext.empty, MessageNetwork.IdsDistinct.empty⟩) trace
  cases state with
  | none => trivial
  | some control => exact both.2

/-- Ledger identifiers are `Nodup` at every reachable history. Rejected calls
count as publications. No scheduler restriction is assumed. -/
theorem publishedOnce_history (scheduler : app.Scheduler) (initial : PMF app.State)
    (horizon : Nat) {state : app.ProtocolState}
    (trace : (app.protocol initial horizon scheduler).Trace state) :
    serviceInvariant (fun execution => execution.network.PublishedOnce) state := by
  have distinct := app.idsDistinct_history scheduler initial horizon trace
  cases state with
  | none => trivial
  | some control => exact MessageNetwork.IdsDistinct.publishedOnce distinct

end Interaction.ReactiveApplication
