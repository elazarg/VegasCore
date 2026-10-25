/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveResponseMenu
import Interaction.ReactiveResponseAccounting
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Actual scheduler origins of remembered environment entries -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu)

/-- Every remembered scheduler entry retains an actual earlier legal prefix,
its complete prior environment recall, its view and a supported command. -/
theorem recorded_environment_prefix
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (control : app.Control)
    (trace : (menu.protocol initial horizon scheduler).Trace (some control))
    (entry : app.EnvironmentEntry) (recorded : entry ∈ control.execution.environmentRecall) :
    ∃ (before : app.Control)
      (prior : (menu.protocol initial horizon scheduler).Trace (some before)),
      TracePrefix prior trace ∧ before.actor = none ∧ 0 < before.remaining ∧
      entry.beforeView = before.execution.observeEnvironment app ∧
      entry.command ∈ (scheduler before.execution.environmentRecall
        (before.execution.observeEnvironment app)).support ∧
      ∃ after, control.execution.environmentRecall =
        before.execution.environmentRecall ++ entry :: after := by
  have origin : ∀ {state} (_history : (menu.protocol initial horizon scheduler).Trace state),
      state.elim True (fun current => ∀ entry ∈ current.execution.environmentRecall,
        ∃ (before : app.Control)
          (prior : (menu.protocol initial horizon scheduler).Trace (some before)),
          TracePrefix prior _history ∧ before.actor = none ∧ 0 < before.remaining ∧
          entry.beforeView = before.execution.observeEnvironment app ∧
          entry.command ∈ (scheduler before.execution.environmentRecall
            (before.execution.observeEnvironment app)).support ∧
          ∃ after, current.execution.environmentRecall =
            before.execution.environmentRecall ++ entry :: after) := by
    intro state history
    induction history with
    | start => trivial
    | @extend source target prior joint legal reached ih =>
        change target ∈ (app.transition initial horizon scheduler source joint).support at reached
        cases source with
        | none =>
            obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
            intro entry recorded
            exact (List.not_mem_nil recorded).elim
        | some current =>
            rcases current with ⟨remaining, actor, execution⟩
            cases actor with
            | some acting =>
                cases (PMF.mem_support_pure_iff _ _).mp reached
                intro entry recorded
                rw [app.respond_environmentRecall] at recorded ⊢
                obtain ⟨before, history, kept, inactive, positive, viewed, selected, later,
                  recalled⟩ := ih entry recorded
                exact ⟨before, history, .extend kept joint legal reached, inactive, positive,
                  viewed, selected, later, recalled⟩
            | none =>
                cases remaining with
                | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
                | succ remaining =>
                    obtain ⟨command, selected, moved⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                    obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                    intro entry recorded
                    have recalled := app.environmentStep_environmentRecall
                      execution next command supported
                    rw [recalled] at recorded ⊢
                    rcases List.mem_append.mp recorded with old | last
                    · obtain ⟨before, history, kept, inactive, positive, viewed, selected,
                        later, previous⟩ := ih entry old
                      refine ⟨before, history, .extend kept joint legal reached, inactive,
                        positive, viewed, selected,
                        later ++ [⟨execution.observeEnvironment app, command⟩], ?_⟩
                      rw [previous, List.append_assoc, List.cons_append]
                    · have same := List.mem_singleton.mp last
                      subst entry
                      exact ⟨⟨remaining + 1, none, execution⟩, prior,
                        .extend .refl joint legal reached, rfl, Nat.zero_lt_succ _, rfl,
                        selected, [], rfl⟩
  exact origin trace entry recorded

end Interaction.ReactiveApplication.ResponseMenu
