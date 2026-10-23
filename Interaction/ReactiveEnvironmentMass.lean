/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseAccounting
import GameTheoryExtensions.Math.Probability.Support

/-! # Actual environment and scheduler atoms from recorded commands -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- The full scheduler word distinguishes different environment commands even
when their semantic application states would coincide. -/
theorem environmentStep_command_unique (before after : app.Execution)
    (first second : app.Command)
    (left : after ∈ (before.environmentStep app first).support)
    (right : after ∈ (before.environmentStep app second).support) : first = second := by
  have words := (app.environmentStep_environmentRecall before after first left).symm.trans
    (app.environmentStep_environmentRecall before after second right)
  have entries := List.singleton_inj.mp (List.append_cancel_left words)
  exact congrArg EnvironmentEntry.command entries

/-- An actual environment successor isolates its selected scheduler atom.
Every other command has zero mass at that full recorded execution. -/
theorem transition_environment_apply (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (remaining : Nat) (before after : app.Execution)
    (chosen : app.Command) (moved : after ∈ (before.environmentStep app chosen).support)
    (joint : Principal → Option app.Action) :
    (app.transition initial horizon scheduler (some ⟨remaining + 1, none, before⟩) joint)
        (some ⟨remaining, chosen.actor? app, after⟩) =
      scheduler before.environmentRecall (before.observeEnvironment app) chosen *
        (before.environmentStep app chosen) after := by
  classical
  rw [transition, PMF.bind_apply, tsum_eq_single chosen]
  · have injective : Function.Injective (fun execution : app.Execution =>
        some (⟨remaining, chosen.actor? app, execution⟩ : app.Control)) := by
      intro first second same
      exact congrArg Control.execution (Option.some.inj same)
    rw [pmf_map_apply_of_injective _ injective]
  · intro other different
    have absent : some (⟨remaining, chosen.actor? app, after⟩ : app.Control) ∉
        ((before.environmentStep app other).map fun execution =>
          some (⟨remaining, other.actor? app, execution⟩ : app.Control)).support := by
      intro supported
      obtain ⟨next, nextSupported, same⟩ := PMF.support_map .. ▸ supported
      have executions : next = after := congrArg Control.execution (Option.some.inj same)
      subst next
      exact different (app.environmentStep_command_unique before after other chosen nextSupported
        moved)
    rw [(PMF.apply_eq_zero_iff _ _).mpr absent, mul_zero]

end Interaction.ReactiveApplication
